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

#[cfg(test)]
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate log;
extern crate cryptominisat;

mod formulae;
mod dpll;

pub use formulae::*;