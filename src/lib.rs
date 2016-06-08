#[macro_use]
extern crate maplit;
use std::ops;
use std::collections::BTreeMap;

#[derive(Debug,PartialOrd,Ord,PartialEq,Eq,Clone)]
pub enum Bools<V> {
    Lit(V),
    And(Box<Bools<V>>, Box<Bools<V>>),
    Or(Box<Bools<V>>, Box<Bools<V>>),
    Not(Box<Bools<V>>),
}

pub type Env<V> = BTreeMap<V, bool>;

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

impl<V> ops::BitOr for Bools<V> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        Bools::Or(Box::new(self), Box::new(other))
    }
}

impl<V> ops::BitAnd for Bools<V> {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Bools::And(Box::new(self), Box::new(other))
    }
}

impl<V> ops::Not for Bools<V> {
    type Output = Self;
    fn not(self) -> Self {
        Bools::Not(Box::new(self))
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
    use self::rand::Rng;
    use super::{Bools, Env};
    use self::quickcheck::{Gen, Arbitrary};
    use std::iter;

    type Var = u8;

    struct Sampler<'a, G, T>
        where G: 'a
    {
        gen: &'a mut G,
        iota: usize,
        thunk: Option<Box<Fn(&'a mut G) -> T>>,
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
                self.thunk = Some(Box::new(f) as Box<Fn(&mut G) -> T>)
            }
            self.iota += weight;
            self
        }
        fn finish(self) -> Option<T> {
            let Sampler { thunk, gen, .. } = self;
            thunk.map(move |f| f(gen))
        }
    }

    impl<T: Arbitrary> Arbitrary for Bools<T> {
        fn arbitrary<G: Gen>(g: &mut G) -> Bools<T> {
            Sampler::new(g)
                .weighted(10, |g: &mut G| Bools::var(Arbitrary::arbitrary(g)))
                .weighted(1, |g: &mut G| !Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) & Bools::arbitrary(g))
                .weighted(1, |g: &mut G| Bools::arbitrary(g) | Bools::arbitrary(g))
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
}
