#[macro_use]
extern crate maplit;
#[macro_use]
extern crate log;
extern crate sat;
use std::ops;
use std::fmt;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use sat::solver::Solver;
use sat::Literal;

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
    pub instance: sat::Instance,
    vars: BTreeMap<V, Literal>,
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

impl<V: fmt::Display> fmt::Display for Bools<V> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Bools::Lit(ref id) => write!(fmt, "{}", id),
            &Bools::And(ref a, ref b) => write!(fmt, "({} & {})", a, b),
            &Bools::Or(ref a, ref b) => write!(fmt, "({} | {})", a, b),
            &Bools::Not(ref a) => write!(fmt, "!{}", a),
        }
    }
}



impl<V: Ord + Clone> CNF<V> {
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

    fn assert<A: AsRef<[Literal]> + fmt::Debug>(&mut self, s: A) {
        debug!("assert! {:?}", s);
        self.instance.assert_any(s.as_ref())
    }
    fn assert_eq(&mut self, a: Literal, b: Literal) {
        debug!("assert! {:?} <-> {:?}", a, b);
        self.assert([!a, b]);
        self.assert([a, !b]);
    }

    fn assert_and(&mut self, it: Literal, l: Literal, r: Literal) {
        debug!("assert! {:?} <-> {:?} /\\ {:?}", it, l, r);
        self.assert([!l, !r, it]);
        self.assert([l, !it]);
        self.assert([r, !it]);
    }
    fn assert_or(&mut self, it: Literal, l: Literal, r: Literal) {
        debug!("assert! {:?} <-> {:?} \\/ {:?}", it, l, r);
        self.assert([l, r, !it]);
        self.assert([!l, it]);
        self.assert([!r, it]);
    }
    fn var(&mut self, var: V) -> Literal {
        let &mut CNF { ref mut instance, ref mut vars } = self;
        vars.entry(var).or_insert_with(|| instance.fresh_var()).clone()
    }


    pub fn solve_with(&self, s: &Solver) -> Option<sat::Assignment> {
        s.solve(&self.instance)
    }

    pub fn next_solution(&mut self, s: &Solver) -> Option<BTreeMap<V, bool>> {
        if let Some(s) = s.solve(&self.instance) {
            let clause = self.vars
                             .values()
                             .map(|l| {
                                 if s.get(*l) {
                                     !l.clone()
                                 } else {
                                     l.clone()
                                 }
                             })
                             .collect::<Vec<_>>();
            debug!("Negation clause: {:?}", clause);
            self.instance.assert_any(clause.iter());

            let res = self.vars.iter().map(|(v, l)| (v.clone(), s.get(*l))).collect();
            Some(res)
        } else {
            None
        }
    }



    pub fn get(&self, assign: &sat::Assignment, var: &V) -> Option<bool> {
        self.vars.get(var).map(|l| assign.get(l.clone()))
    }
}

impl<V: Ord + Clone + fmt::Debug> Bools<V> {
    pub fn to_cnf(&self, env: &Env<V>) -> CNF<V> {
        let mut cnf = CNF::new();
        for (k, v) in env.iter() {
            cnf.assert_var(k.clone(), *v);
        }
        let _ = self.to_cnf_inner(&mut cnf);
        debug!("var -> Literal: {:#?}", cnf);
        cnf
    }

    fn to_cnf_inner(&self, cnf: &mut CNF<V>) -> Literal {
        debug!("subclause: {:?}", self);

        match self {
            &Bools::Lit(ref id) => {
                let it = cnf.var(id.clone());
                it.clone()
            }
            &Bools::Not(ref a) => {
                let self_var = cnf.instance.fresh_var();
                let it = a.to_cnf_inner(cnf);
                cnf.assert_eq(self_var, !it);
                self_var
            }
            &Bools::And(ref l, ref r) => {
                let self_var = cnf.instance.fresh_var();
                let a = l.to_cnf_inner(cnf);
                let b = r.to_cnf_inner(cnf);
                cnf.assert_and(self_var, a, b);
                self_var
            }
            &Bools::Or(ref l, ref r) => {
                let self_var = cnf.instance.fresh_var();
                let a = l.to_cnf_inner(cnf);
                let b = r.to_cnf_inner(cnf);
                cnf.assert_or(self_var, a, b);
                self_var
            }
        }
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
    use std::collections::{BTreeSet, BTreeMap};
    use std::iter;
    use std::sync::Arc;
    use std::process::Command;

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
        if let Some(val) = input.eval(&env) {
            let top_var = ::std::u8::MAX;
            if env.contains_key(&top_var) {
                return TestResult::discard();
            }

            info!("verify_cnf_prop: {:?} / {:?} => {:?}", input, env, val);

            let satisfiable = Bools::var(top_var).is(input.clone());
            info!("{:?} <-> {:?} => {:?}", top_var, input, satisfiable);
            let cnf = satisfiable.to_cnf(&env);
            let s = sat::solver::Dimacs::new(|| {
                let mut c = Command::new("minisat");
                c.arg("-verb=0");
                c
            });
            debug!("cnf: {:?}", {
                let mut out = Vec::new();
                s.write_instance(&mut out, &cnf.instance);
                String::from_utf8(out)
            });

            if let Some(solution) = cnf.solve_with(&s) {
                let eval_res = cnf.get(&solution, &top_var);
                let okay = eval_res == Some(val);
                debug!("Solution okay? {:?}: top: {:?} -> {:?}; expected: {:?}; from: {:?}",
                       okay,
                       top_var,
                       eval_res,
                       val,
                       solution);
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

    #[test]
    fn should_iter_examples() {
        let vars = [0, 1];
        let mut f = vars.iter()
                        .map(|&v| Bools::var(v))
                        .fold(None,
                              |acc, x| Some(acc.map(|acc| acc & x.clone()).unwrap_or(x)))
                        .expect("formula");

        let s = sat::solver::Dimacs::new(|| {
            let mut c = Command::new("minisat");
            c.arg("-verb=0");
            c
        });

        println!("Formula: {}", f);
        let mut cnf = (!f.clone()).to_cnf(&btreemap![]);

        println!("cnf: {}", {
            let mut out = Vec::new();
            s.write_instance(&mut out, &cnf.instance);
            String::from_utf8(out).unwrap_or("".to_string())
        });

        let mut solutions = BTreeSet::new();
        while let Some(soln) = cnf.next_solution(&s) {
            println!("solution: {:?}", soln);
            solutions.insert(soln);
        }

        assert_eq!(solutions,
                   btreeset! {
            btreemap!{0 => false, 1 => false},
            btreemap!{0 => false, 1 => true},
            btreemap!{0 => true, 1 => false},
            btreemap!{0 => true, 1 => true},
        });

    }
}
