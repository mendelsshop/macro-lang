use std::ops::{Add, Sub};

#[derive(Hash, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct Phase(pub isize);

impl Add for Phase {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Phase(self.0 + rhs.0)
    }
}
impl Sub for Phase {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Phase(self.0 + rhs.0)
    }
}
impl Sub<Option<Self>> for Phase {
    type Output = Option<Self>;

    fn sub(self, rhs: Option<Self>) -> Self::Output {
        rhs.map(|rhs| Phase(self.0 + rhs.0))
    }
}
impl Add<Option<Self>> for Phase {
    type Output = Option<Self>;

    fn add(self, rhs: Option<Self>) -> Self::Output {
        rhs.map(|rhs| Phase(self.0 + rhs.0))
    }
}
