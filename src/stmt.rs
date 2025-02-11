use std::fmt::Display;

use crate::cnf::{Cnf, Disj};

#[derive(PartialEq, Eq, Clone)]
pub enum Stmt {
    Cont,
    Taut,
    Symbol(char),
    Not(Box<Stmt>),
    And(Box<Stmt>, Box<Stmt>),
    Or(Box<Stmt>, Box<Stmt>),
    Implies(Box<Stmt>, Box<Stmt>),
    Equiv(Box<Stmt>, Box<Stmt>)
}

impl Stmt {
    pub fn taut() -> Stmt {
        return Stmt::Taut;
    }

    pub fn cont() -> Stmt {
        return Stmt::Cont;
    }

    pub fn symbol(c: char) -> Stmt {
        return Stmt::Symbol(c);
    }

    pub fn not(self) -> Stmt {
        return Stmt::Not(Box::new(self));
    }

    pub fn and(self, e: Stmt) -> Stmt {
        return Stmt::And(Box::new(self), Box::new(e));
    }

    pub fn or(self, e: Stmt) -> Stmt {
        return Stmt::Or(Box::new(self), Box::new(e));
    }

    pub fn implies(self, e: Stmt) -> Stmt {
        return Stmt::Implies(Box::new(self), Box::new(e));
    }

    pub fn equiv(self, e: Stmt) -> Stmt {
        return Stmt::Equiv(Box::new(self), Box::new(e));
    }

    fn extrapolate(self) -> Self {
        return match self {
            Stmt::Not(o) => Self::not((*o).extrapolate()),
            Stmt::And(l, r) => (*l).extrapolate().and((*r).extrapolate()),
            Stmt::Or(l, r) => (*l).extrapolate().or((*r).extrapolate()),
            Stmt::Implies(l, r) => Self::not((*l).extrapolate()).or((*r).extrapolate()),
            Stmt::Equiv(l, r) => Self::and(
                Self::not((*l).clone().extrapolate()).or((*r).clone().extrapolate()), 
                Self::not((*r).extrapolate()).or((*l).extrapolate())
            ),
            s => s,
        };
    }

    fn extract_cont_taut(self) -> Self {
        return match self {
            Stmt::Cont => self,
            Stmt::Taut => self,
            Stmt::Symbol(_) => self,
            Stmt::Not(o) => match (*o).extract_cont_taut() {
                Stmt::Cont => Stmt::Taut,
                Stmt::Taut => Stmt::Cont,
                s => Self::not(s)
            },
            Stmt::And(l, r) => match ((*l).extract_cont_taut(), (*r).extract_cont_taut()) {
                (Stmt::Cont, _) => Stmt::Cont,
                (_, Stmt::Cont) => Stmt::Cont,
                (Stmt::Taut, o) => o,
                (o, Stmt::Taut) => o,
                (l, r) => l.and(r)
            },
            Stmt::Or(l, r) => match ((*l).extract_cont_taut(), (*r).extract_cont_taut()) {
                (Stmt::Taut, _) => Stmt::Taut,
                (_, Stmt::Taut) => Stmt::Taut,
                (Stmt::Cont, o) => o,
                (o, Stmt::Cont) => o,
                (l, r) => l.or(r)
            },
            _ => panic!("Must extrapolate implications before extracting cont/taut"),
        };
    }

    fn demorgan_pos(self) -> Self {
        return match self {
            Stmt::Not(o) => (*o).demorgan_neg(),
            Stmt::And(l, r) => (*l).demorgan_pos().and((*r).demorgan_pos()),
            Stmt::Or(l, r) => (*l).demorgan_pos().or((*r).demorgan_pos()),
            Stmt::Symbol(_) | Stmt::Taut | Stmt::Cont => self,
            _ => panic!("Must extrapolate implications before DeMorgan"),
        }
    }

    fn demorgan_neg(self) -> Self {
        return match self {
            Stmt::Not(o) => *o,
            Stmt::And(l, r) => (*l).demorgan_neg().or((*r).demorgan_neg()),
            Stmt::Or(l, r) => (*l).demorgan_neg().and((*r).demorgan_neg()),
            Stmt::Symbol(_) => Self::not(self),
            Stmt::Taut => Stmt::Cont,
            Stmt::Cont => Stmt::Taut,
            _ => panic!("Must extrapolate implications before DeMorgan"),
        }
    }

    fn dist_disj(self) -> Self {
        return match self {
            Stmt::Or(l, r) => {
                match ((*l).dist_disj(), (*r).dist_disj()) {
                    (Stmt::And(ll, lr), Stmt::And(rl, rr)) => {
                            ((*ll).clone().or((*rl).clone()))
                        .and((*ll).clone().or((*rr).clone()))
                        .and((*lr).clone().or((*rl).clone()))
                        .and((*lr).clone().or((*rr).clone()))
                    }

                    (Stmt::And(ll, lr), rd) => {
                            ((*ll).or(rd.clone()))
                        .and((*lr).or(rd.clone()))
                    }

                    (ld, Stmt::And(rl, rr)) => {
                            (ld.clone().or(*rl))
                        .and(ld.clone().or(*rr))
                    }

                    (ld, rd) => ld.or(rd)
                }
            },
            Stmt::And(l, r) => l.dist_disj().and(r.dist_disj()),
            Stmt::Not(o) => Stmt::not(o.dist_disj()),
            s => s
        };
    }

    fn base_cnf(self) -> Self {
        let mut e = self;
        e = e.extrapolate();
        e = e.extract_cont_taut();
        e = e.demorgan_pos();
        loop {
            let n = e.clone().dist_disj();
            if n == e {
                return n;
            }
            e = n;
        }
    }

    fn disj(&self) -> Option<Disj> {
        // Returns None in case of a tautology
        return match self {
            Stmt::Taut => None,
            Stmt::Cont => Some(Disj::contradiction()),
            Stmt::Symbol(c) => Some(Disj::axiom(*c)),
            Stmt::Not(o) => {
                if let Stmt::Symbol(c) = **o {
                    Some(Disj::axiom_not(c))
                } else {
                    panic!("Not in CNF")
                }
            },
            Stmt::Or(l, r) => match (l.disj(), r.disj()) {
                // Combine with tautology
                (Some(l), Some(r)) => l.combine(&r),
                _ => None, // Either side is tautology: True | P is still True
            },
            _ => panic!("Not in CNF"),
        }
    }

    pub fn cnf(&self) -> Cnf {
        let mut cnf = Cnf::new();

        match self.clone().base_cnf() {
            Stmt::And(l, r) => {
                cnf.insert_all(&l.cnf());
                cnf.insert_all(&r.cnf());
            },
            o => {
                if let Some(disj) = o.disj() {
                    cnf.insert(disj);
                }
            }
        };

        return cnf;
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return match self {
            Stmt::Cont => write!(f, "~"),
            Stmt::Taut => write!(f, "*"),
            Stmt::Symbol(sym) => write!(f, "{sym}"),
            Stmt::Not(o) => write!(f, "!{o}"),
            Stmt::And(l, r) => write!(f, "({l} & {r})"),
            Stmt::Or(l, r) => write!(f, "({l} | {r})"),
            Stmt::Implies(l, r) => write!(f, "({l} -> {r})"),
            Stmt::Equiv(l, r) => write!(f, "({l} <-> {r})"),
        };
    }
}