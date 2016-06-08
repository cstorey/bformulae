#[macro_use]
extern crate maplit;
#[macro_use]
extern crate log;
extern crate sat;
use std::ops;
use std::fmt;
use std::collections::BTreeMap;
use std::sync::Arc;

#[derive(Debug,PartialOrd,Ord,PartialEq,Eq,Clone)]
pub enum Bools<V> {
    Lit(V),
    And(Arc<Bools<V>>, Arc<Bools<V>>),
    Or(Arc<Bools<V>>, Arc<Bools<V>>),
    Not(Arc<Bools<V>>),
}

pub type Env<V> = BTreeMap<V, bool>;

#[derive(Debug)]
pub struct CNF<V: Ord> {
    instance: sat::Instance,
    vars: BTreeMap<V, sat::Literal>,
}

impl<V> Bools<V> {
    pub fn var(id: V) -> Bools<V> {
        Bools::Lit(id)
    }
}
impl<V: Clone> Bools<V> {
    pub fn is(self, rhs: Bools<V>) -> Bools<V> {
        !(self ^ rhs)
    }
}

impl<V: Ord> Bools<V> {
    pub fn eval(&self, env: &Env<V>) -> Option<bool> {
        match self {
            &Bools::Lit(ref id) => env.get(id).map(|x| *x),
            &Bools::And(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a & b)),
            &Bools::Or(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a | b)),
            &Bools::Not(ref a) => a.eval(env).map(|a| !a),
        }
    }
}

impl<V: Ord> CNF<V> {
    fn new() -> CNF<V> {
        CNF {
            instance: sat::Instance::new(),
            vars: BTreeMap::new(),
        }
    }

    fn assert_var(&mut self, var: V, val: bool) {
        let var = self.var(var);
        self.assert([if val {
                         var
                     } else {
                         !var
                     }]);
    }

    fn assert<A: AsRef<[sat::Literal]> + fmt::Debug>(&mut self, s: A) {
        info!("assert! {:?}", s);
        self.instance.assert_any(s.as_ref())
    }
    fn assert_eq(&mut self, a: sat::Literal, b: sat::Literal) {
        info!("assert! {:?} <-> {:?}", a, b);
        self.assert([!a, b]);
        self.assert([a, !b]);
    }

    fn assert_and(&mut self, it: sat::Literal, l: sat::Literal, r: sat::Literal) {
        info!("assert! {:?} <-> {:?} /\\ {:?}", it, l, r);
        self.assert([!l, !r, it]);
        self.assert([l, !it]);
        self.assert([r, !it]);
    }
    fn assert_or(&mut self, it: sat::Literal, l: sat::Literal, r: sat::Literal) {
        info!("assert! {:?} <-> {:?} \\/ {:?}", it, l, r);
        self.assert([l, r, !it]);
        self.assert([!l, it]);
        self.assert([!r, it]);
    }
    fn var(&mut self, var: V) -> sat::Literal {
        let &mut CNF { ref mut instance, ref mut vars } = self;
        vars.entry(var).or_insert_with(|| instance.fresh_var()).clone()
    }
}

impl<V: Ord + Clone + fmt::Debug> Bools<V> {
    pub fn to_cnf(&self, env: &Env<V>) -> (sat::Literal, CNF<V>) {
        let mut cnf = CNF::new();
        for (k, v) in env.iter() {
            cnf.assert_var(k.clone(), *v);
        }
        let top = self.to_cnf_inner(&mut cnf);
        debug!("var -> Literal: {:#?}", cnf);
        debug!("formula: {:?} -> top:{:?}", self, top);
        (top, cnf)
    }

    fn to_cnf_inner(&self, cnf: &mut CNF<V>) -> sat::Literal {
        let self_var = cnf.instance.fresh_var();
        debug!("subclause: {:?} <-> {:?}", self, self_var);

        match self {
            &Bools::Lit(ref id) => {
                let it = cnf.var(id.clone());
                cnf.assert_eq(self_var, it.clone());
            }
            &Bools::Not(ref a) => {
                let it = a.to_cnf_inner(cnf);
                cnf.assert_eq(self_var, !it);
            }
            &Bools::And(ref l, ref r) => {
                let a = l.to_cnf_inner(cnf);
                let b = r.to_cnf_inner(cnf);
                cnf.assert_and(self_var, a, b);
            }
            &Bools::Or(ref l, ref r) => {
                let a = l.to_cnf_inner(cnf);
                let b = r.to_cnf_inner(cnf);
                cnf.assert_or(self_var, a, b);
            }
        }
        self_var
    }
}

impl<V> ops::BitOr for Bools<V> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        Bools::Or(Arc::new(self), Arc::new(other))
    }
}

impl<V> ops::BitAnd for Bools<V> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Bools::And(Arc::new(self), Arc::new(other))
    }
}

impl<V> ops::Not for Bools<V> {
    type Output = Self;
    fn not(self) -> Self {
        Bools::Not(Arc::new(self))
    }
}

impl<V: Clone> ops::BitXor for Bools<V> {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        (self.clone() | other.clone()) & !(self & other)
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;
    extern crate env_logger;
    use sat;
    use self::rand::Rng;
    use super::{Bools, Env};
    use self::quickcheck::{Gen, Arbitrary, TestResult};
    use std::iter;
    use sat::solver::Solver;
    use std::sync::Arc;

    type Var = u8;

    struct Sampler<'a, G, T>
        where G: 'a
    {
        gen: &'a mut G,
        iota: usize,
        thunk: Option<Arc<Fn(&'a mut G) -> T>>,
    }

    impl<'a, G: rand::Rng, T> Sampler<'a, G, T> {
        fn new(g: &'a mut G) -> Self {
            Sampler {
                gen: g,
                iota: 0,
                thunk: None,
            }
        }
        fn weighted<F: Fn(&mut G) -> T + 'static>(mut self, weight: usize, f: F) -> Self {
            // randfloat() <= (1/iota);
            // randfloat() * iota <= 1
            let iota = self.iota;
            if (0..weight)
                   .map(|i| 1 + iota + i)
                   .map(|i| self.gen.gen_range(0, i))
                   .any(|p| p <= 1) {
                self.thunk = Some(Arc::new(f) as Arc<Fn(&mut G) -> T>)
            }
            self.iota += weight;
            self
        }
        fn finish(self) -> Option<T> {
            let Sampler { thunk, gen, .. } = self;
            thunk.map(move |f| f(gen))
        }
    }

    impl<T: Arbitrary + Sync> Arbitrary for Bools<T> {
        fn arbitrary<G: Gen>(g: &mut G) -> Bools<T> {
            Sampler::new(g)
                .weighted(15, |g: &mut G| Bools::var(Arbitrary::arbitrary(g)))
                .weighted(1, |g: &mut G| !Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) & Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) | Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) ^ Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g).is(Bools::arbitrary(g)))
                .finish()
                .unwrap()
        }

        fn shrink(&self) -> Box<Iterator<Item = Self> + 'static> {
            match self {
                &Bools::Lit(ref n) => Box::new(n.shrink().map(Bools::Lit)),
                &Bools::Not(ref it) => Box::new(iter::once((&**it).clone())),
                &Bools::And(ref l, ref r) => {
                    Box::new(iter::once((&**l).clone()).chain(iter::once((&**r).clone())))
                }
                &Bools::Or(ref l, ref r) => {
                    Box::new(iter::once((&**l).clone()).chain(iter::once((&**r).clone())))
                }
            }
        }
    }

    fn verify_not_prop(input: Bools<Var>, env: Env<Var>) -> bool {
        (!input.clone()).eval(&env) == input.eval(&env).map(|r| !r)
    }

    #[test]
    fn verify_not() {
        quickcheck::quickcheck(verify_not_prop as fn(Bools<Var>, Env<Var>) -> bool);
    }

    fn verify_and_prop(left: Bools<Var>, right: Bools<Var>, env: Env<Var>) -> bool {
        trace!("verify_and_prop: {:?} & {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env),
                                                    right.clone().eval(&env)) {
            Some(a & b)
        } else {
            None
        };
        (left & right).eval(&env) == expected
    }

    #[test]
    fn verify_and() {
        quickcheck::quickcheck(verify_and_prop as fn(Bools<Var>, Bools<Var>, Env<Var>) -> bool);
    }

    fn verify_or_prop(left: Bools<Var>, right: Bools<Var>, env: Env<Var>) -> bool {
        trace!("verify_and_prop: {:?} | {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env),
                                                    right.clone().eval(&env)) {
            Some(a | b)
        } else {
            None
        };
        (left | right).eval(&env) == expected
    }

    #[test]
    fn verify_or() {
        quickcheck::quickcheck(verify_or_prop as fn(Bools<Var>, Bools<Var>, Env<Var>) -> bool);
    }

    fn verify_xor_prop(left: Bools<Var>, right: Bools<Var>, env: Env<Var>) -> bool {
        trace!("verify_and_prop: {:?} ^ {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env),
                                                    right.clone().eval(&env)) {
            Some(a ^ b)
        } else {
            None
        };
        (left ^ right).eval(&env) == expected
    }

    #[test]
    fn verify_xor() {
        quickcheck::quickcheck(verify_xor_prop as fn(Bools<Var>, Bools<Var>, Env<Var>) -> bool);
    }

    fn verify_is_prop(left: Bools<Var>, right: Bools<Var>, env: Env<Var>) -> bool {
        trace!("verify_and_prop: {:?} <-> {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env),
                                                    right.clone().eval(&env)) {
            Some(a == b)
        } else {
            None
        };
        (left.is(right)).eval(&env) == expected
    }

    #[test]
    fn verify_is() {
        quickcheck::quickcheck(verify_is_prop as fn(Bools<Var>, Bools<Var>, Env<Var>) -> bool);
    }


    #[test]
    fn trivial_example() {
        let x1 = Bools::var(0);
        let x2 = Bools::var(1);
        let x3 = Bools::var(2);
        let c = (!x1.clone() & x2.clone()) | (x1 & !x2.clone()) | (!x2 & x3);

        let env = btreemap!{0 => true, 1 => false, 2 => true};
        assert_eq!(c.eval(&env), Some(true));
        assert_eq!(c.eval(&btreemap![]), None);
    }

    fn verify_cnf_prop(input: Bools<Var>, env: Env<Var>) -> TestResult {
        use std::process::Command;
        if let Some(val) = input.eval(&env) {
            info!("verify_cnf_prop: {:?} / {:?} => {:?}", input, env, val);
            let (top, cnf) = input.to_cnf(&env);
            let s = sat::solver::Dimacs::new(|| Command::new("minisat"));
            debug!("cnf: {:?}", {
                let mut out = Vec::new();
                s.write_instance(&mut out, &cnf.instance);
                String::from_utf8(out)
            });

            if let Some(solution) = s.solve(&cnf.instance) {
                let okay = solution.get(top) == val;
                debug!("Solution okay? {:?}: {:?}", okay, solution);
                TestResult::from_bool(okay)
            } else {
                debug!("No solution found");
                TestResult::failed()
            }
        } else {
            TestResult::discard()
        }
    }

    #[test]
    fn verify_cnf() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(verify_cnf_prop as fn(Bools<Var>, Env<Var>) -> TestResult);
    }
}
