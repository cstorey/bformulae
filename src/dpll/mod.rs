use std::{ops,iter};
use std::collections::{BTreeSet,BTreeMap};
use formulae::{Environment, Dimacs, DimacsLit, CNF};

// With reference to: 
// * http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
//   (Formalization and Implementation of Modern SAT Solvers --Filip Marić)
// * https://en.wikipedia.org/wiki/DPLL_algorithm

// This is basically a naive implementation, and hence, rather inefficient.

#[derive(Copy, Clone,Debug,Default,PartialOrd, Ord, PartialEq, Eq)]
struct Var(usize);

#[derive(Clone,Debug,Default)]
struct Solver {
    idx: usize,
    clauses: BTreeSet<BTreeMap<Var, bool>>,
    model: BTreeMap<Var, bool>,
}

#[derive(Clone,Debug, Default)]
struct DpllLit {
    var: Var,
    val: bool,
}
#[derive(Default)]
struct PosNeg { 
    pos: bool, neg: bool,
}


impl ops::Not for DpllLit {
    type Output = Self;
    fn not(self) -> Self {
        let DpllLit { var, val } = self;
        DpllLit { var, val: !val }
    }
}

impl Solver {
    fn new() -> Self {
        Default::default()
    }
}

impl DimacsLit for DpllLit {}

impl Dimacs for Solver {
    type Lit = DpllLit;

    fn new_var(&mut self) -> Self::Lit {
        let val = true;
        self.idx += 1;
        let var = Var(self.idx);
        DpllLit { val, var, }
    }
    fn add_clause<C: AsRef<[Self::Lit]>>(&mut self, clause: C) {
        let term = clause.as_ref().iter()
            .map(|&DpllLit { var, val }| (var, val))
        .collect();
        self.clauses.insert(term);
    }
}

impl Solver {
    // FIXME: Return type.
    fn solve(&mut self) -> Option<BTreeMap<Var, bool>> {
        debug!("-> solve: {:?}", self);
        if self.no_more_unresolved_clauses() {
            debug!("No clauses; satisfiable: {:?}", self);
            debug!("<- solve: {:?}", &self.model);
            return Some(self.model.clone());
        }

        if self.any_empty_clauses() {
            debug!("Found an empty clause; unsatisfiable: {:?}", self);
            debug!("<- solve: ()");
            return None
        }

        if let Some(lit) = self.find_pure_literal() {
            debug!("Pure literal! {:?}", lit);
            return self.solve_with_assignment(lit);
        }
        if let Some(lit) = self.find_unit_clause() {
            debug!("Unit clause! {:?}", lit);
            return self.solve_with_assignment(lit);
        }

        let candidate = self.choose_literal();

        self.solve_with_assignment(candidate.clone())
                .or_else(|| self.solve_with_assignment(!candidate))
    }


    fn solve_with_assignment(&self, lit: DpllLit) -> Option<BTreeMap<Var, bool>> {
            let mut child = self.clone();
            child.assign(lit);
            return child.solve();
    }

    fn no_more_unresolved_clauses(&self) -> bool {
        self.clauses.is_empty()
    }

    fn any_empty_clauses(&self) -> bool {
        self.clauses.iter().any(|cl| cl.is_empty())
    }

    fn choose_literal(&self) -> DpllLit {
        self.clauses.iter()
        .flat_map(|cl| cl)
        .map(|(&var, &val)| DpllLit { var, val })
        .next()
        .expect("non-empty clauses")
    }

    fn find_pure_literal(&self) -> Option<DpllLit> {
        let mut occurrences = BTreeMap::new();
        for (var, &val) in self.clauses.iter().flat_map(|cl| cl) {
            let entry = occurrences.entry(var).or_insert(PosNeg::default());
            if val {
                entry.pos = true
            } else {
                entry.neg = true
            };
        }
        return occurrences.into_iter().filter_map(|(var, pn)| pn.as_pure_for(var) )
        .next()
    }

    fn find_unit_clause(&self) -> Option<DpllLit> {
        // FIXME: 
        self.clauses.iter()
            .filter(|cl| cl.len() == 1)
            .flat_map(|cl| cl.iter().next() )
            .map(|(&var, &val)| DpllLit { var, val })
            .next()
    }

    fn assign(&mut self, lit: DpllLit) {
        debug!("Assign: {:?}", lit);
        let to_update = self.clauses.iter()
            .filter(|cl| cl.contains_key(&lit.var))
            .cloned()
            .collect::<Vec<_>>();
        for mut cl in to_update {
            debug!("Update clause: {:?}", cl);
            self.clauses.remove(&cl);
            let val = cl.remove(&lit.var);
            if val == Some(lit.val) {
                // Problem here is that if the other literals in this clause
                // form the only mention of said literal; then the current
                // problem is that we return a model that ignores them.

                debug!("Removed now tautological clause ({:?} == {:?}): {:?}", lit, val, cl);
            } else {
                debug!("Updated clause: {:?}", cl);
                self.clauses.insert(cl);
            }
        }
        self.model.insert(lit.var, lit.val);
    }
}
impl<V: Ord + Clone, Env: Environment<V>> iter::Iterator for CNF<Solver, V, Env> {
    type Item = Env;

    fn next(&mut self) -> Option<Env> {
            if let Some(model) = self.instance.solve() {
            let clause = self.vars
                             .values()
                             .map(|l| {
                                 if *model.get(&l.var).unwrap_or(&false) {
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
                          .map(|(v, l)| (v.clone(), *model.get(&l.var).unwrap_or(&false)))
                          .collect();
            Some(res)
        } else {
            None
        }
    }
}

impl PosNeg {
    fn as_pure_for(self, var: &Var) -> Option<DpllLit> {
        if self.pos ^ self.neg {
            Some(DpllLit { var: var.clone(), val: self.pos }) 
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;
    extern crate env_logger;
    use {Bools, CNF, Error, Dimacs};
    use self::quickcheck::{Gen, Arbitrary, TestResult};
    use std::collections::{BTreeSet, BTreeMap};
    use std::iter;
    use std::sync::Arc;
    use dpll::{Solver, DpllLit};

    type Var = u8;

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
        let top_var = ::std::u8::MAX;
        if env.contains_key(&top_var) {
            return TestResult::discard();
        }
        
        info!("verify_cnf_prop: input: {:?}; env: {:?}", input, env);
        if let Ok(val) = input.eval(&env) {

            info!("verify_cnf_prop: {} / {:?} => {:?}", input, env, val);

            let satisfiable = Bools::var(top_var).is(input.clone());
            info!("{:?} <-> {:?} => {:?}", top_var, input, satisfiable);

            let cnf = satisfiable.to_cnf(env.clone(), Solver::new);
            for soln in cnf {
                info!("solution: {:?}", soln);
            }

            let cnf = satisfiable.to_cnf(env.clone(), Solver::new);

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


    fn check_conjunction_prop(a: bool, b: bool) {
        let expected = a & b;
        info!("check_conjunction_prop: a:{:?} ∧ b:{:?} => {:?}", a, b, expected);
        let mut cnf = CNF::new(Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        cnf.assert([av]);
        cnf.assert([bv]);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        let is_sat = next.is_some();

        info!("check_conjunction_prop: a:{:?} ∧ b:{:?} (result {}; expected: {})", a, b,
            if is_sat { "SAT" } else { "UNSAT" },
            if expected { "SAT" } else { "UNSAT" },
        );
        assert_eq!(is_sat, expected)
    }

    #[test]
    fn check_conjunction() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_conjunction_prop as fn(bool, bool));
    }

    fn check_disjunction_prop(a: bool, b: bool) {
        let expected = a | b;
        info!("check_disjunction_prop: a:{:?} ∨ b:{:?} => {:?}", a, b, expected);
        let mut cnf = CNF::new(Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        cnf.assert([av, bv]);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        let is_sat = next.is_some();

        info!("check_disjunction_prop: a:{:?} ∨ b:{:?} (result {}; expected: {})", a, b,
            if is_sat { "SAT" } else { "UNSAT" },
            if expected { "SAT" } else { "UNSAT" },
        );
        assert_eq!(is_sat, expected)
    }

    #[test]
    fn check_disjunction() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_disjunction_prop as fn(bool, bool));
    }

    fn check_and_gate_prop(r: bool, a: bool, b: bool) {
        info!("check_and_gate_prop: a:{:?} ∧ b:{:?} == r:{:?}", a, b, r);
        let mut cnf = CNF::new(Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_and(rv, av, bv);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        let is_sat = next.is_some();

        info!("check_and_gate_prop: a:{:?} ∧ b:{:?} == r:{:?} (result {}; expected: {})", a, b, r,
            if is_sat { "SAT" } else { "UNSAT" },
            if r == (a & b) { "SAT" } else { "UNSAT" },
        );
        assert_eq!(is_sat, r == (a & b))
    }

    #[test]
    fn check_and_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_and_gate_prop as fn(bool, bool, bool));
    }

    fn check_or_gate_prop(r: bool, a: bool, b: bool) {
        info!("check_or_gate_prop: a:{:?} ∨ b:{:?} == r:{:?}", a, b, r);
        let mut cnf = CNF::new(Solver::new);
        let av = cnf.assert_var("a", a);
        let bv = cnf.assert_var("b", b);
        let rv = cnf.assert_var("r", r);
        cnf.assert_or(rv, av, bv);

        let next: Option<BTreeMap<&str, bool>> = cnf.next();
        let is_sat = next.is_some();
        info!("check_or_gate_prop: a:{:?} ∨ b:{:?} == r:{:?} (result {}; expected: {})", a, b, r,
            if is_sat { "SAT" } else { "UNSAT" },
            if r == (a | b) { "SAT" } else { "UNSAT" },
        );
        assert_eq!(is_sat, r == (a | b))
    }

    #[test]
    fn check_or_gate() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_or_gate_prop as fn(bool, bool, bool));
    }

    fn check_eq_prop(r: bool, a: bool) {
        let mut cnf = CNF::new(Solver::new);
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
        let mut cnf = CNF::new(Solver::new);
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
        env_logger::init().unwrap_or(());
        let vars = ['a', 'b'];
        let f = !vars.iter()
                     .map(|&v| Bools::var(v))
                     .fold(None,
                           |acc, x| Some(acc.map(|acc| acc & x.clone()).unwrap_or(x)))
                     .expect("formula");

        info!("Formula: {}", f);
        let cnf = f.to_cnf(btreemap![], Solver::new);

        info!("Collecting solutions");
        let mut solutions = BTreeSet::new();
        for soln in cnf {
            info!("solution: {:?}", soln);
            solutions.insert(soln);
        }

        assert_eq!(solutions,
                   btreeset! {
            btreemap!{'a' => false, 'b' => false},
            btreemap!{'a' => false, 'b' => true},
            btreemap!{'a' => true, 'b' => false},
        });
    }


    fn check_assignments_prop(clauses: BTreeSet<BTreeMap<usize, bool>>) {
        info!("check_assignments_prop");
        use ::dpll::Var;
        let mut solver = Solver::new();
        debug!("num clauses: {:?}", clauses.len());
        for cl in clauses.iter() {
            let cl = cl.into_iter().map(|(&var, &val)| DpllLit { var: Var(var), val })
                .collect::<Vec<_>>();
            debug!("Assert clause: {:?}", cl);
            solver.add_clause(cl);
        }

        if let Some(model) = solver.solve() {
            debug!("Found model: {:?}", model);
            for cl in clauses.iter() {
                debug!("Check clause: {:?}", cl);
                assert!(
                    cl.iter().any(|(&var, val)| model.get(&Var(var)).map(|v| v == val).unwrap_or(false))
                )

            }
        }
    }

    #[test]
    fn check_assignments() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_assignments_prop as fn(BTreeSet<BTreeMap<usize, bool>>));
    }
 
     fn check_satisfiability_against_cryptominisat_prop(clauses: BTreeSet<BTreeMap<usize, bool>>) {
        info!("check_assignments_prop");
        use ::dpll::Var;
        use ::cryptominisat as cms;
        use formulae::lbool_as_optbool;

        let dpll_satp =  {
            let mut solver = Solver::new();
            debug!("num clauses: {:?}", clauses.len());
            for cl in clauses.iter() {
                let cl = cl.iter().map(|(&var, &val)| DpllLit { var: Var(var), val })
                    .collect::<Vec<_>>();
                debug!("Assert clause: {:?}", cl);
                solver.add_clause(cl);
            }

            let result = solver.solve();
            info!("Dpll Model: {:?}", result);
            result.is_some()
        };

        let cms_sat = {
            let mut cmsat = cms::Solver::new();
            let mut cmvars = BTreeMap::new();
            for cl in clauses.iter() {
                debug!("Assert clause: {:?}", cl);
                let cm_clause = cl.iter().map(|(&var, &val)| {
                    let v = *cmvars.entry(var).or_insert_with(|| cmsat.new_var());
                    if val { v } else { !v }
                }).collect::<Vec<_>>();
                cmsat.add_clause(&*cm_clause);
            } 
            let res = cmsat.solve() == cms::Lbool::True;
            info!("CryptoMinisat Model: {:?}",
                if res {
                    Some(cmsat.get_model().iter().cloned().map(lbool_as_optbool).enumerate().collect::<BTreeMap<_, _>>())
                } else { None });
            res
        };

        assert_eq!(dpll_satp, cms_sat);
    }

    #[test]
    fn check_satisfiability_against_cryptominisat() {
        env_logger::init().unwrap_or(());
        quickcheck::quickcheck(check_satisfiability_against_cryptominisat_prop as fn(BTreeSet<BTreeMap<usize, bool>>));
    }
}