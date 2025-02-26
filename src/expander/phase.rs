use std::{
    cmp::Ordering,
    ops::{Add, Sub},
};

#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
// TODO: label phase (make into enum)
pub enum Phase {
    Normal(isize),
    Label,
}

impl Ord for Phase {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Phase::Normal(p1), Phase::Normal(p2)) => p1.cmp(p2),
            (Phase::Label, Phase::Normal(_)) => Ordering::Less,
            (Phase::Normal(_), Phase::Label) => Ordering::Greater,
            (Phase::Label, Phase::Label) => Ordering::Equal,
        }
    }
}

impl PartialOrd for Phase {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Phase::Normal(p1), Phase::Normal(p2)) => p1.partial_cmp(p2),
            (Phase::Label, Phase::Normal(_)) => Some(Ordering::Less),
            (Phase::Normal(_), Phase::Label) => Some(Ordering::Greater),
            (Phase::Label, Phase::Label) => Some(Ordering::Equal),
        }
    }
}

impl Add for Phase {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Phase::Normal(p1), Phase::Normal(p2)) => Phase::Normal(p1 + p2),
            _ => Phase::Label,
        }
    }
}
impl Sub for Phase {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Phase::Normal(p1), Phase::Normal(p2)) => Phase::Normal(p1 - p2),
            _ => Phase::Label,
        }
    }
}
