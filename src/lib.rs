//! Provides a way to construct boolean formulae in propositional logic, and
//! evaluate their satisfiability given a set of variable assignments.
//! # Example
//! This is useful if you want to find out for what set of assignments a formulae is falsifiable. Eg:
//!
//! ```
//! use bformulae::Bools;
//! use std::collections::BTreeMap;
//!
//! let a = Bools::var("a");
//! let b = Bools::var("b");
//! let mut cnf = a.is(b).to_cnf(&BTreeMap::new());
//! for soln in cnf {
//!     println!("solution: {:?}", soln);
//! }
//! ```

#[macro_use]
extern crate maplit;
#[macro_use]
extern crate log;
extern crate cryptominisat;
use std::ops;
use std::fmt;
use std::iter;
use std::collections::BTreeMap;
use std::sync::Arc;
use cryptominisat::{Solver, Lit, Lbool};

/// The core represenation of a proposition, parameterized over the variable
/// type.
#[derive(Debug,PartialOrd,Ord,PartialEq,Eq,Clone)]
pub enum Bools<V> {
    Lit(V),
    And(Arc<Bools<V>>, Arc<Bools<V>>),
    Or(Arc<Bools<V>>, Arc<Bools<V>>),
    Xor(Arc<Bools<V>>, Arc<Bools<V>>),
    Not(Arc<Bools<V>>),
    Eq(Arc<Bools<V>>, Arc<Bools<V>>),
    Implies(Arc<Bools<V>>, Arc<Bools<V>>),
}

/// Convenience alias for the type of environments.
pub type Env<V> = BTreeMap<V, bool>;

/// A representation of a formula encoded as CNF.
/// Also allows iteration over solutions.
pub struct CNF<V: Ord> {
    instance: Solver,
    vars: BTreeMap<V, Lit>,
    cache: BTreeMap<Bools<V>, Lit>,
}

impl<V: fmt::Debug + Ord> fmt::Debug for CNF<V> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("CNF")
           .finish()
    }
}

impl<V> Bools<V> {
    /// Returns a variable reference.
    ///
    /// ```
    /// use bformulae::Bools;
    /// // f = a
    /// let f = Bools::var("a");
    /// ```
    pub fn var(id: V) -> Bools<V> {
        Bools::Lit(id)
    }
}
impl<V: Clone> Bools<V> {
    /// Returns a formula that is true when `self` and `rhs` are equal.
    ///
    /// ```
    /// use bformulae::Bools;
    /// // f = a ↔ b
    /// let f = Bools::var("a").is(Bools::var("b"));
    /// ```

    pub fn is(self, rhs: Bools<V>) -> Bools<V> {
        Bools::Eq(Arc::new(self), Arc::new(rhs))
    }

    /// Returns a formula that is of the form:
    ///
    /// ```
    /// use bformulae::Bools;
    /// // f = `a → b`
    /// let f = Bools::var("a").is(Bools::var("b"));
    /// ```
    pub fn implies(self, rhs: Bools<V>) -> Bools<V> {
        Bools::Implies(Arc::new(self), Arc::new(rhs))
    }
}

impl<V: Ord> Bools<V> {
    /// Evaluates a formula over the given variable substitutions, and returns whether the formula is true or not.
    /// Returns None if a variable is missing from the environment.
    ///
    /// ```
    /// use bformulae::Bools;
    /// use std::collections::BTreeMap;
    ///
    /// let f = Bools::var("athing");
    /// let mut env = BTreeMap::new();
    /// env.insert("athing", true);
    /// assert_eq!(f.eval(&env), Some(true));
    /// assert_eq!((!f).eval(&env), Some(false));
    /// ```

    pub fn eval(&self, env: &Env<V>) -> Option<bool> {
        match self {
            &Bools::Lit(ref id) => env.get(id).map(|x| *x),
            &Bools::And(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a & b)),
            &Bools::Or(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a | b)),
            &Bools::Xor(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a ^ b)),
            &Bools::Not(ref a) => a.eval(env).map(|a| !a),
            &Bools::Eq(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a == b)),
            &Bools::Implies(ref a, ref b) => {
                a.eval(env).and_then(|a| b.eval(env).map(|b| (!a) | b))
            }
        }
    }
}

impl<V: fmt::Display> fmt::Display for Bools<V> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Bools::Lit(ref id) => write!(fmt, "{}", id),
            &Bools::And(ref a, ref b) => write!(fmt, "({} & {})", a, b),
            &Bools::Or(ref a, ref b) => write!(fmt, "({} | {})", a, b),
            &Bools::Xor(ref a, ref b) => write!(fmt, "({} ^ {})", a, b),
            &Bools::Not(ref a) => write!(fmt, "!{}", a),
            &Bools::Eq(ref a, ref b) => write!(fmt, "({} == {})", a, b),
            &Bools::Implies(ref a, ref b) => write!(fmt, "({} -> {})", a, b),
        }
    }
}


fn lit_as_string(l: &Lit) -> String {
    format!("{}{}",
            if l.isneg() {
                "-"
            } else {
                ""
            },
            l.var() + 1)
}
fn lbool_as_optbool(l: Lbool) -> Option<bool> {
    match l {
        Lbool::True => Some(true),
        Lbool::False => Some(false),
        Lbool::Undef => None,
    }
}

impl<V: Ord + Clone> CNF<V> {
    fn new() -> CNF<V> {
        CNF {
            instance: Solver::new(),
            vars: BTreeMap::new(),
            cache: BTreeMap::new(),
        }
    }

    fn assert_var(&mut self, var: V, val: bool) -> Lit {
        let var = self.var(var);
        self.assert([if val {
                         var
                     } else {
                         !var
                     }]);
        var
    }

    fn assert<A: AsRef<[Lit]>>(&mut self, s: A) {
        debug!("cnf: {}",
               s.as_ref()
                .iter()
                .map(|l| lit_as_string(l))
                .collect::<Vec<_>>()
                .join(" "));
        self.instance.add_clause(s.as_ref());
    }
    fn assert_eq(&mut self, a: Lit, b: Lit) {
        debug!("assert! {:?} <-> {:?}",
               lit_as_string(&a),
               lit_as_string(&b));
        self.assert([!a, b]);
        self.assert([a, !b]);
    }

    fn assert_and(&mut self, it: Lit, l: Lit, r: Lit) {
        debug!("assert! {:?} <-> {:?} /\\ {:?}",
               lit_as_string(&it),
               lit_as_string(&l),
               lit_as_string(&r));
        self.assert([!l, !r, it]);
        self.assert([l, !it]);
        self.assert([r, !it]);
    }
    fn assert_or(&mut self, it: Lit, l: Lit, r: Lit) {
        debug!("assert! {:?} <-> {:?} \\/ {:?}",
               lit_as_string(&it),
               lit_as_string(&l),
               lit_as_string(&r));
        self.assert([l, r, !it]);
        self.assert([!l, it]);
        self.assert([!r, it]);
    }

    fn assert_xor(&mut self, it: Lit, l: Lit, r: Lit) {
        debug!("assert! {:?} <-> {:?} ^ {:?}",
               lit_as_string(&it),
               lit_as_string(&l),
               lit_as_string(&r));
        // IT = L ^ R
        // (!L | !R | !IT) & (L|R|!IT) & (L|!R|IT) & (!L|R|IT)
        self.assert([!l, !r, !it]);
        self.assert([l, r, !it]);
        self.assert([l, !r, it]);
        self.assert([!l, r, it]);
    }

    fn var(&mut self, var: V) -> Lit {
        let &mut CNF { ref mut instance, ref mut vars, .. } = self;
        let res = vars.entry(var.clone()).or_insert_with(|| instance.new_var());
        debug!("var: {:?}", lit_as_string(res));
        res.clone()
    }


    // FIXME: Return type.
    fn solve_with(&mut self) -> bool {
        let ret = lbool_as_optbool(self.instance.solve());
        debug!("Solution assignments: {:?}",
               self.instance
                   .get_model()
                   .iter()
                   .cloned()
                   .enumerate()
                   .map(|(i, lb)| (i, lbool_as_optbool(lb)))
                   .collect::<BTreeMap<_, _>>());
        ret.expect("solve_with")
    }
}

impl<V: Ord + Clone> iter::Iterator for CNF<V> {
    type Item = Env<V>;

    fn next(&mut self) -> Option<Env<V>> {
        if self.solve_with() {
            let clause = self.vars
                             .values()
                             .map(|l| {
                                 if self.instance.is_true(*l) {
                                     !l.clone()
                                 } else {
                                     l.clone()
                                 }
                             })
                             .collect::<Vec<_>>();
            debug!("Negation clause: {:?}",
                   clause.iter().map(lit_as_string).collect::<Vec<_>>());
            self.instance.add_clause(&clause);

            let res = self.vars
                          .iter()
                          .map(|(v, l)| (v.clone(), self.instance.is_true(*l)))
                          .collect();
            Some(res)
        } else {
            None
        }
    }
}

impl<V: Ord + Clone + fmt::Debug> Bools<V> {
    /// Encodes the formula and given environment into Conjunctive Normal Form
    /// using the Tseytin transformation. The resulting CNF is satisfiable iff
    /// the propositional formula is true in all cases.
    ///
    /// ```
    /// use bformulae::Bools;
    /// use std::collections::BTreeMap;
    ///
    /// let f = Bools::var("athing");
    /// let mut env = BTreeMap::new();
    /// env.insert("athing", true);
    /// let cnf = f.to_cnf(&env);
    /// ```

    pub fn to_cnf(&self, env: &Env<V>) -> CNF<V> {
        let mut cnf = CNF::new();
        for (k, v) in env.iter() {
            cnf.assert_var(k.clone(), *v);
        }
        let top = self.to_cnf_inner(&mut cnf);
        cnf.assert([top]);
        cnf
    }

    fn to_cnf_inner(&self, cnf: &mut CNF<V>) -> Lit {
        if cnf.cache.contains_key(self) {
            let val = cnf.cache[self];
            debug!("subclause(cached): {:?} => {:?}", self, lit_as_string(&val));
            val.clone()
        } else {
            let val = match self {
                &Bools::Lit(ref id) => {
                    let it = cnf.var(id.clone());
                    it.clone()
                }
                &Bools::Not(ref a) => {
                    let self_var = cnf.instance.new_var();
                    let it = a.to_cnf_inner(cnf);
                    cnf.assert_eq(self_var, !it);
                    self_var
                }
                &Bools::And(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_and(self_var, a, b);
                    self_var
                }
                &Bools::Or(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_or(self_var, a, b);
                    self_var
                }
                &Bools::Xor(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_xor(self_var, a, b);
                    self_var
                }
                &Bools::Eq(ref l, ref r) => {
                    // !(l ^ r)
                    let f = !((**l).clone() ^ (**r).clone());
                    f.to_cnf_inner(cnf)
                }
                &Bools::Implies(ref l, ref r) => {
                    // (!l) | r
                    let f = !(**l).clone() | (**r).clone();
                    f.to_cnf_inner(cnf)
                }
            };
            cnf.cache.insert(self.clone(), val);
            debug!("subclause: {:?} => {:?}", self, lit_as_string(&val));
            val
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
        Bools::Xor(Arc::new(self), Arc::new(other))
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;
    extern crate env_logger;
    use super::{Bools, Env, CNF};
    use self::quickcheck::{Gen, Arbitrary, TestResult};
    use std::collections::BTreeSet;
    use std::iter;
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
                .weighted(20, |g: &mut G| Bools::var(Arbitrary::arbitrary(g)))
                .weighted(1, |g: &mut G| !Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) & Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) | Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) ^ Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g).is(Bools::arbitrary(g)))
                .weighted(1,
                          |g: &mut G| Bools::arbitrary(g).implies(Bools::arbitrary(g)))
                .finish()
                .unwrap()
        }

        fn shrink(&self) -> Box<Iterator<Item = Self> + 'static> {
            match self {
                &Bools::Lit(ref n) => Box::new(n.shrink().map(Bools::Lit)),
                &Bools::Not(ref it) => Box::new(iter::once((&**it).clone())),
                &Bools::And(ref l, ref r) |
                &Bools::Or(ref l, ref r) |
                &Bools::Xor(ref l, ref r) |
                &Bools::Eq(ref l, ref r) |
                &Bools::Implies(ref l, ref r) => {
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
        trace!("verify_or_prop: {:?} | {:?} / {:?}", left, right, env);
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

    fn verify_implies_prop(left: Bools<Var>, right: Bools<Var>, env: Env<Var>) -> bool {
        trace!("verify_and_prop: {:?} <-> {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env),
                                                    right.clone().eval(&env)) {
            Some(!a | b)
        } else {
            None
        };
        let f = left.clone().implies(right.clone());
        let actual = f.clone().eval(&env);
        debug!("({} -> {}) [{}] in {:?} => {:?} (expect: {:?}; okay? {})",
               left,
               right,
               f,
               env,
               actual,
               expected,
               actual == expected);
        actual == expected
    }

    #[test]
    fn verify_implies() {
        quickcheck::quickcheck(verify_implies_prop as fn(Bools<Var>, Bools<Var>, Env<Var>) -> bool);
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

            info!("verify_cnf_prop: {} / {:?} => {:?}", input, env, val);

            let satisfiable = Bools::var(top_var).is(input.clone());
            info!("{:?} <-> {:?} => {:?}", top_var, input, satisfiable);

            let cnf = satisfiable.to_cnf(&env);
            for soln in cnf {
                info!("solution: {:?}", soln);
            }

            let cnf = satisfiable.to_cnf(&env);

            let mut solutions = BTreeSet::new();
            for soln in cnf {
                debug!("solution: {:?}", soln);
                solutions.insert(soln[&top_var]);
            }


            let okay = solutions == btreeset!{val};
            debug!("Solution okay? {:?}: top: {:?} -> {:?}; expected: {:?}",
                   okay,
                   top_var,
                   solutions,
                   val);
            TestResult::from_bool(okay)
        } else {
            TestResult::discard()
        }
    }

    #[test]
    fn verify_cnf() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(verify_cnf_prop as fn(Bools<Var>, Env<Var>) -> TestResult);
    }

    fn check_and_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new();
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_and(rv, av, bv);

        assert_eq!(cnf.next().is_some(), r == (a & b))
    }

    #[test]
    fn check_and_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_and_gate_prop as fn(bool, bool, bool));
    }

    fn check_or_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new();
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_or(rv, av, bv);

        assert_eq!(cnf.next().is_some(), r == (a | b))
    }

    #[test]
    fn check_or_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_or_gate_prop as fn(bool, bool, bool));
    }

    fn check_eq_prop(r: bool, a: bool) {
        let mut cnf = CNF::new();
        let av = cnf.assert_var("a", a);
        let rv = cnf.assert_var("r", r);
        cnf.assert_eq(rv, av);

        let res = cnf.next().is_some();
        assert_eq!(res, r == a)
    }

    #[test]
    fn check_eq() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_eq_prop as fn(bool, bool));
    }

    fn check_xor_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new();
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_xor(rv, av, bv);

        assert_eq!(cnf.next().is_some(), r == (a ^ b))
    }

    #[test]
    fn check_xor_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_xor_gate_prop as fn(bool, bool, bool));
    }



    #[test]
    fn should_iter_examples() {
        let vars = ['a', 'b'];
        let f = !vars.iter()
                     .map(|&v| Bools::var(v))
                     .fold(None,
                           |acc, x| Some(acc.map(|acc| acc & x.clone()).unwrap_or(x)))
                     .expect("formula");

        println!("Formula: {}", f);
        let cnf = f.to_cnf(&btreemap![]);

        let mut solutions = BTreeSet::new();
        for soln in cnf {
            println!("solution: {:?}", soln);
            solutions.insert(soln);
        }

        assert_eq!(solutions,
                   btreeset! {
            btreemap!{'a' => false, 'b' => false},
            btreemap!{'a' => false, 'b' => true},
            btreemap!{'a' => true, 'b' => false},
        });
    }
}
