//! Provides a way to construct boolean formulae in propositional logic, and
//! evaluate their satisfiability given a set of variable assignments.
//! # Example
//! This is useful if you want to find out for what set of assignments a formulae is falsifiable. Eg:
//!
//! ```
//! extern crate bformulae;
//! extern crate cryptominisat;
//! use std::collections::BTreeMap;
//! use bformulae::Bools;
//! use self::cryptominisat::Solver;
//!
//! fn main() {
//!     let a = Bools::var("a");
//!     let b = Bools::var("b");
//!     let mut cnf = a.is(b).to_cnf(BTreeMap::new(), Solver::new);
//!     for soln in cnf {
//!         println!("solution: {:?}", soln);
//!     }
//! }
//! ```

#[macro_use]
extern crate maplit;
#[macro_use]
extern crate log;
extern crate cryptominisat;
use std::ops;
use std::fmt;
use std::iter::{self, FromIterator};
use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::sync::Arc;
use cryptominisat::Lbool;
use std::clone::Clone;
use std::error;
use std::any::Any;
use std::marker::PhantomData;

#[derive(Clone,Debug, Eq, PartialEq)]
pub enum Error<T> {
    MissingVar(T),
}

impl<T: fmt::Display> fmt::Display for Error<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Error::MissingVar(ref v) => write!(fmt, "Missing variable: {}", v),
        }
    }
}

impl<T: fmt::Display + fmt::Debug + Any> error::Error for Error<T> {
    fn description(&self) -> &'static str {
        match self {
            &Error::MissingVar(_) => "Missing variable",
        }
    }
}

pub trait Environment<V>: FromIterator<(V, bool)> + IntoIterator<Item=(V, bool)> {
    fn get(&self, key: &V) -> Option<bool>;
}

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

pub trait DimacsLit : ops ::Not<Output=Self> + Sized + fmt::Debug + Clone {
}

pub trait Dimacs {
    type Lit : DimacsLit;

    fn new_var(&mut self) -> Self::Lit;
    fn add_clause<C: AsRef<[Self::Lit]>>(&mut self, C);
}

/// A representation of a formula encoded as CNF
/// Also allows iteration over solutions.
pub struct CNF<D: Dimacs, V: Ord, Env> {
    instance: D,
    vars: BTreeMap<V, D::Lit>,
    cache: BTreeMap<Bools<V>, D::Lit>,
    _env: PhantomData<Env>,
}

impl<D: Dimacs, V: fmt::Debug + Ord, Env> fmt::Debug for CNF<D, V, Env> {
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

impl<V: Ord + Clone> Bools<V> {
    /// Evaluates a formula over the given variable substitutions, and returns whether the formula is true or not.
    /// Returns Err if a variable is missing from the environment.
    ///
    /// ```
    /// use bformulae::Bools;
    /// use std::collections::BTreeMap;
    ///
    /// let f = Bools::var("athing");
    /// let mut env = BTreeMap::new();
    /// env.insert("athing", true);
    /// assert_eq!(f.eval(&env), Ok(true));
    /// assert_eq!((!f).eval(&env), Ok(false));
    /// ```
    /// ```
    /// use bformulae::{Bools,Error};
    /// use std::collections::BTreeMap;
    ///
    /// let f = Bools::var("missing variable");
    /// let mut env = BTreeMap::new();
    /// assert_eq!((!f).eval(&env), Err(Error::MissingVar("missing variable")));
    /// ```


    pub fn eval<Env: Environment<V>>(&self, env: &Env) -> Result<bool, Error<V>> {
        match self {
            &Bools::Lit(ref id) => {
                env.get(id)
                   .map(Ok)
                   .unwrap_or_else(|| Err(Error::MissingVar((*id).clone())))
            }
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



fn lbool_as_optbool(l: Lbool) -> Option<bool> {
    match l {
        Lbool::True => Some(true),
        Lbool::False => Some(false),
        Lbool::Undef => None,
    }
}

impl<D: Dimacs, V: Ord + Clone, Env> CNF<D, V, Env> {
    fn new<F: FnMut() -> D>(mut f: F) -> CNF<D, V, Env> {
        CNF {
            instance: f(),
            vars: BTreeMap::new(),
            cache: BTreeMap::new(),
            _env: PhantomData,
        }
    }

    fn assert_var(&mut self, var: V, val: bool) -> D::Lit {
        let var = self.var(var);
        let clause = [if val {
                          var.clone()
                      } else {
                          !var.clone()
                      }];
        self.assert(clause);
        var
    }

    fn assert<A: AsRef<[D::Lit]>>(&mut self, s: A) {
        debug!("cnf: {}",
               s.as_ref()
                .iter()
                .map(|l| format!("{:?}", l))
                .collect::<Vec<_>>()
                .join(" "));
        self.instance.add_clause(s);
    }
    fn assert_eq(&mut self, a: D::Lit, b: D::Lit) {
        debug!("assert! {:?} <-> {:?}", a, b);
        self.assert([!a.clone(), b.clone()]);
        self.assert([a, !b]);
    }

    fn assert_and(&mut self, it: D::Lit, l: D::Lit, r: D::Lit) {
        debug!("assert! {:?} <-> {:?} /\\ {:?}", it, l, r);
        self.assert([!l.clone(), !r.clone(), it.clone()]);
        self.assert([l, !it.clone()]);
        self.assert([r, !it]);
    }
    fn assert_or(&mut self, it: D::Lit, l: D::Lit, r: D::Lit) {
        debug!("assert! {:?} <-> {:?} \\/ {:?}", it, l, r);
        self.assert([l.clone(), r.clone(), !it.clone()]);
        self.assert([!l, it.clone()]);
        self.assert([!r, it]);
    }

    fn assert_xor(&mut self, it: D::Lit, l: D::Lit, r: D::Lit) {
        debug!("assert! {:?} <-> {:?} ^ {:?}", it, l, r);
        // IT = L ^ R
        // (!L | !R | !IT) & (L|R|!IT) & (L|!R|IT) & (!L|R|IT)
        self.assert([!l.clone(), !r.clone(), !it.clone()]);
        self.assert([l.clone(), r.clone(), !it.clone()]);
        self.assert([l.clone(), !r.clone(), it.clone()]);
        self.assert([!l, r, it]);
    }

    fn var(&mut self, var: V) -> D::Lit {
        let &mut CNF { ref mut instance, ref mut vars, .. } = self;
        let res = vars.entry(var.clone()).or_insert_with(|| instance.new_var());
        debug!("var: {:?}", res);
        res.clone()
    }
}

impl<V: Ord + Clone, Env> CNF<cryptominisat::Solver, V, Env> {
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

impl<V: Ord + Clone, Env: Environment<V>> iter::Iterator for CNF<cryptominisat::Solver, V, Env> {
    type Item = Env;

    fn next(&mut self) -> Option<Env> {
        if self.solve_with() {
            let clause = self.vars
                             .values()
                             .map(|l| {
                                 if self.instance.is_true(l.0) {
                                     !l.clone()
                                 } else {
                                     l.clone()
                                 }
                             })
                             .collect::<Vec<_>>();
            debug!("Negation clause: {:?}", clause);
            Dimacs::add_clause(&mut self.instance, clause);
            // self.instance.add_clause(clause);

            let res = self.vars
                          .iter()
                          .map(|(v, l)| (v.clone(), self.instance.is_true(l.0)))
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
    /// extern crate bformulae;
    /// extern crate cryptominisat;
    /// use std::collections::BTreeMap;
    /// use bformulae::Bools;
    /// use cryptominisat::Solver;
    ///
    /// fn main() {
    ///     let f = Bools::var("athing");
    ///     let mut env = BTreeMap::new();
    ///     env.insert("athing", true);
    ///     let cnf = f.to_cnf(env, Solver::new);
    /// }
    /// ```

    pub fn to_cnf<D: Dimacs, Env: Environment<V>, F: FnMut() -> D>(&self,
                                                                   env: Env,
                                                                   builder: F)
                                                                   -> CNF<D, V, Env> {
        let mut cnf = CNF::new(builder);
        for (k, v) in env.into_iter() {
            cnf.assert_var(k.clone(), v);
        }
        let top = self.to_cnf_inner(&mut cnf);
        cnf.assert([top]);
        cnf
    }

    fn to_cnf_inner<D: Dimacs, Env>(&self, cnf: &mut CNF<D, V, Env>) -> D::Lit {
        if cnf.cache.contains_key(self) {
            let ref val = cnf.cache[self];
            debug!("subclause(cached): {:?} => {:?}", self, val);
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
                    cnf.assert_eq(self_var.clone(), !it);
                    self_var
                }
                &Bools::And(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_and(self_var.clone(), a, b);
                    self_var
                }
                &Bools::Or(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_or(self_var.clone(), a, b);
                    self_var
                }
                &Bools::Xor(ref l, ref r) => {
                    let self_var = cnf.instance.new_var();
                    let a = l.to_cnf_inner(cnf);
                    let b = r.to_cnf_inner(cnf);
                    cnf.assert_xor(self_var.clone(), a, b);
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
            debug!("subclause: {:?} => {:?}", self, val);
            cnf.cache.insert(self.clone(), val.clone());
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

#[derive(Clone)]
pub struct CMLit(cryptominisat::Lit);

impl AsRef<cryptominisat::Lit> for CMLit {
    fn as_ref(&self) -> &cryptominisat::Lit {
        &self.0
    }
}

impl ops::Not for CMLit {
    type Output = Self;
    fn not(self) -> Self {
        CMLit(!self.0)
    }
}
impl fmt::Debug for CMLit {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if self.0.isneg() {
            try!(write!(fmt, "!"));
        }
        try!(write!(fmt, "{}", self.0.var() + 1));
        Ok(())
    }
}

impl DimacsLit for CMLit {}

impl Dimacs for cryptominisat::Solver {
    type Lit = CMLit;

    fn new_var(&mut self) -> CMLit {
        CMLit(cryptominisat::Solver::new_var(self))
    }
    fn add_clause<C: AsRef<[Self::Lit]>>(&mut self, c: C) {
        let clause = c.as_ref().iter().map(|l| l.0).collect::<Vec<cryptominisat::Lit>>();
        cryptominisat::Solver::add_clause(self, &clause);
    }
}

impl<V: Ord> Environment<V> for BTreeMap<V, bool> {
    fn get(&self, var: &V) -> Option<bool> {
        BTreeMap::get(self, var).map(Clone::clone)
    }
}

impl<V: Hash + Eq> Environment<V> for HashMap<V, bool> {
    fn get(&self, var: &V) -> Option<bool> {
        HashMap::get(self, var).map(Clone::clone)
    }
}


#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;
    extern crate env_logger;
    use super::{Bools, CNF, Error};
    use self::quickcheck::{Gen, Arbitrary, TestResult};
    use std::collections::{BTreeSet, BTreeMap};
    use std::iter;
    use std::sync::Arc;
    use cryptominisat;

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

    fn verify_not_prop(input: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        (!input.clone()).eval(&env).ok() == input.eval(&env).map(|r| !r).ok()
    }

    #[test]
    fn verify_not() {
        quickcheck::quickcheck(verify_not_prop as fn(Bools<Var>, BTreeMap<Var, bool>) -> bool);
    }

    fn verify_and_prop(left: Bools<Var>, right: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        trace!("verify_and_prop: {:?} & {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env).ok(),
                                                    right.clone().eval(&env).ok()) {
            Some(a & b)
        } else {
            None
        };
        (left & right).eval(&env).ok() == expected
    }

    #[test]
    fn verify_and() {
        quickcheck::quickcheck(verify_and_prop as fn(Bools<Var>, Bools<Var>, BTreeMap<Var, bool>)
                                                     -> bool);
    }

    fn verify_or_prop(left: Bools<Var>, right: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        trace!("verify_or_prop: {:?} | {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env).ok(),
                                                    right.clone().eval(&env).ok()) {
            Some(a | b)
        } else {
            None
        };
        (left | right).eval(&env).ok() == expected
    }

    #[test]
    fn verify_or() {
        quickcheck::quickcheck(verify_or_prop as fn(Bools<Var>, Bools<Var>, BTreeMap<Var, bool>)
                                                    -> bool);
    }

    fn verify_xor_prop(left: Bools<Var>, right: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        trace!("verify_and_prop: {:?} ^ {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env).ok(),
                                                    right.clone().eval(&env).ok()) {
            Some(a ^ b)
        } else {
            None
        };
        (left ^ right).eval(&env).ok() == expected
    }

    #[test]
    fn verify_xor() {
        quickcheck::quickcheck(verify_xor_prop as fn(Bools<Var>, Bools<Var>, BTreeMap<Var, bool>)
                                                     -> bool);
    }

    fn verify_is_prop(left: Bools<Var>, right: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        trace!("verify_and_prop: {:?} <-> {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env).ok(),
                                                    right.clone().eval(&env).ok()) {
            Some(a == b)
        } else {
            None
        };
        (left.is(right)).eval(&env).ok() == expected
    }

    #[test]
    fn verify_is() {
        quickcheck::quickcheck(verify_is_prop as fn(Bools<Var>, Bools<Var>, BTreeMap<Var, bool>)
                                                    -> bool);
    }

    fn verify_implies_prop(left: Bools<Var>, right: Bools<Var>, env: BTreeMap<Var, bool>) -> bool {
        trace!("verify_and_prop: {:?} <-> {:?} / {:?}", left, right, env);
        let expected = if let (Some(a), Some(b)) = (left.clone().eval(&env).ok(),
                                                    right.clone().eval(&env).ok()) {
            Some(!a | b)
        } else {
            None
        };
        let f = left.clone().implies(right.clone());
        let actual = f.clone().eval(&env).ok();
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
        quickcheck::quickcheck(verify_implies_prop as fn(Bools<Var>,
                                                         Bools<Var>,
                                                         BTreeMap<Var, bool>)
                                                         -> bool);
    }


    #[test]
    fn trivial_example() {
        let x1 = Bools::var(0);
        let x2 = Bools::var(1);
        let x3 = Bools::var(2);
        let c = (!x1.clone() & x2.clone()) | (x1 & !x2.clone()) | (!x2 & x3);

        let env = btreemap!{0 => true, 1 => false, 2 => true};
        assert_eq!(c.eval(&env), Ok(true));
        assert!(c.eval(&btreemap![]).is_err());
    }

    #[test]
    fn should_indicate_some_missing_var() {
        let x1 = Bools::var(0);
        assert_eq!(x1.eval(&btreemap![]), Err(Error::MissingVar(0)));
    }


    fn verify_cnf_prop(input: Bools<Var>, env: BTreeMap<Var, bool>) -> TestResult {
        if let Ok(val) = input.eval(&env) {
            let top_var = ::std::u8::MAX;
            if env.contains_key(&top_var) {
                return TestResult::discard();
            }

            info!("verify_cnf_prop: {} / {:?} => {:?}", input, env, val);

            let satisfiable = Bools::var(top_var).is(input.clone());
            info!("{:?} <-> {:?} => {:?}", top_var, input, satisfiable);

            let cnf = satisfiable.to_cnf(env.clone(), cryptominisat::Solver::new);
            for soln in cnf {
                info!("solution: {:?}", soln);
            }

            let cnf = satisfiable.to_cnf(env.clone(), cryptominisat::Solver::new);

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
        quickcheck::quickcheck(verify_cnf_prop as fn(Bools<Var>, BTreeMap<Var, bool>) -> TestResult);
    }

    fn check_and_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new(cryptominisat::Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_and(rv, av, bv);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        assert_eq!(next.is_some(), r == (a & b))
    }

    #[test]
    fn check_and_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_and_gate_prop as fn(bool, bool, bool));
    }

    fn check_or_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new(cryptominisat::Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_or(rv, av, bv);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        assert_eq!(next.is_some(), r == (a | b))
    }

    #[test]
    fn check_or_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_or_gate_prop as fn(bool, bool, bool));
    }

    fn check_eq_prop(r: bool, a: bool) {
        let mut cnf = CNF::new(cryptominisat::Solver::new);
        let av = cnf.assert_var("a", a);
        let rv = cnf.assert_var("r", r);
        cnf.assert_eq(rv, av);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        assert_eq!(next.is_some(), r == a)
    }

    #[test]
    fn check_eq() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_eq_prop as fn(bool, bool));
    }

    fn check_xor_gate_prop(r: bool, a: bool, b: bool) {
        let mut cnf = CNF::new(cryptominisat::Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_xor(rv, av, bv);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        assert_eq!(next.is_some(), r == (a ^ b))
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
        let cnf = f.to_cnf(btreemap![], cryptominisat::Solver::new);

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
