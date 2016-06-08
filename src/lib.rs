#[macro_use]
extern crate maplit;
use std::ops::{BitOr, BitAnd, Not};
use std::collections::BTreeMap;

#[derive(Debug,PartialOrd,Ord,PartialEq,Eq,Clone)]
pub enum Bools {
    Lit(usize),
    And(Box<Bools>, Box<Bools>),
    Or(Box<Bools>, Box<Bools>),
    Not(Box<Bools>),
}

type Env = BTreeMap<usize, bool>;

impl Bools {
    fn var(id: usize) -> Bools {
        Bools::Lit(id)
    }
    fn eval(&self, env: &Env) -> Option<bool> {
        match self {
            &Bools::Lit(id) => env.get(&id).map(|x| *x),
            &Bools::And(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a & b)),
            &Bools::Or(ref a, ref b) => a.eval(env).and_then(|a| b.eval(env).map(|b| a | b)),
            &Bools::Not(ref a) => a.eval(env).map(|a| !a),
        }
    }
}

impl BitOr for Bools {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        Bools::Or(Box::new(self), Box::new(other))
    }
}

impl BitAnd for Bools {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Bools::And(Box::new(self), Box::new(other))
    }
}

impl Not for Bools {
    type Output = Self;
    fn not(self) -> Self {
        Bools::Not(Box::new(self))
    }
}

#[cfg(test)]
mod tests {
    use super::Bools;
    #[test]
    fn it_works() {
        let x1 = Bools::var(0);
        let x2 = Bools::var(1);
        let x3 = Bools::var(2);
        let c = (!x1.clone() & x2.clone()) | (x1 & !x2.clone()) | (!x2 & x3);

        let env = btreemap!{0 => true, 1 => false, 2 => true};
        assert_eq!(c.eval(&env), Some(true));
        assert_eq!(c.eval(&btreemap![]), None);
    }
}
