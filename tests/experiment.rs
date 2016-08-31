extern crate sat;
extern crate bformulae;
#[macro_use]
extern crate maplit;
use bformulae::{Bools, CNF};
use std::process::Command;
use std::collections::{BTreeSet, BTreeMap};


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
