use std::collections::HashSet;
use std::fmt::Display;
use std::hash::Hash;


/// A disjunction of symbols, either inverted or not. Symbols are represented as [char]s.
/// Internally, the disjunction is represented as two disjoint sets, one with non-inverted
/// (positive) symbols, and one with inverted (negative) symbols.
#[derive(PartialEq, Eq, Clone)]
pub struct Disj {
    pos: HashSet<char>,
    neg: HashSet<char>
}

#[allow(unused)]
impl Disj {
    /// Creates a new [Disj], given the sets with positive and negative symbols.
    /// 
    /// For example, given `pos = {P, Q}` and `neg = {R}`, it creates a disjunction stating
    /// `P | Q | !R`.
    /// 
    /// The sets should typically be disjoint, since otherwise the statement would
    /// be a tautology (i.e. `P | !P` is always true, other disjuncts will no longer
    /// matter then). However, a tautology is useless and can't be represented in a 
    /// unified way, so instead the sets are made disjunct by removing the terms that
    /// exist in both sets.
    /// 
    /// For example, given `pos = {P, Q}` and `neg = {Q, R}`, logically you'd make the
    /// statement `P | Q | !Q | !R`, but that is a logical tautology. Instead, it creates
    /// the statement `P | !R`, which is the result of resolving `P | Q` and `!Q | !R`
    /// against eachother. This side effect of non-disjoint sets allows for resolution between two
    /// statements to be as simple as passing the unions of respectively the positive and
    /// negative symbols of both statements.
    /// 
    /// Note that when both sets are empty, the resulting disjunction is a contradiction
    /// by vacuous truth: _"Do any of the disjuncts satisfy? No, because there are no disjuncts."_
    pub fn new(mut pos: HashSet<char>, mut neg: HashSet<char>) -> Disj {
        // Remove terms that are both in pos and neg: if we have P | !P then we essentially have stated a tautology
        let mut isc = Vec::new();

        for i in pos.intersection(&neg) {
            isc.push(*i);
        }

        for i in isc.iter() {
            pos.remove(i);
            neg.remove(i);
        }

        return Disj { pos, neg };
    }

    /// Creates a new [Disj], given the sets with positive and negative symbols as slices.
    pub fn of_slices(pos: &[char], neg: &[char]) -> Disj {
        return Self::new(
            pos.iter().copied().collect(),
            neg.iter().copied().collect()
        );
    }

    /// Returns the set of non-inverted (positive) disjuncts.
    pub fn pos(&self) -> &HashSet<char> {
        return &self.pos;
    }

    /// Returns the set of inverted (negative) disjuncts.
    pub fn neg(&self) -> &HashSet<char> {
        return &self.neg;
    }

    /// Tests whether the given term is part of this disjunction in non-inverted form.
    pub fn is_pos(&self, term: char) -> bool {
        return self.pos.contains(&term);
    }

    /// Tests whether the given term is part of this disjunction in inverted form.
    pub fn is_neg(&self, term: char) -> bool {
        return self.neg.contains(&term);
    }

    /// Tests whether the given term is not part of this disjunction.
    pub fn is_unknown(&self, term: char) -> bool {
        return !self.is_pos(term) && !self.is_neg(term);
    }

    /// Tests whether this disjunction presents a contradiction. A contradictory disjunction
    /// is a disjunction with no terms. In other words, there does not exist a disjunct that can
    /// be satisfied, so by vacuous truth it is a contradiction. Resolution will generate a
    /// contradiction if two statements are contradictory.
    pub fn is_contradiction(&self) -> bool {
        return self.pos.is_empty() && self.neg.is_empty();
    }

    /// Given a specific term to resolve over, resolves this statement against the other.
    /// 
    /// For example, if this statement is `!P | Q`, the other statement is `!Q | R`, and
    /// the term `Q` was given to resolve over, it will return `!P | R`. In other words:
    /// if `P -> Q` and `Q -> R` then `P -> R`, but it will only see this if the term `Q`
    /// is given to resolve.
    /// 
    /// The method will return `None` if:
    /// - This or the other statement do not state the given term
    /// - Both this and the other statement state the given term positively
    /// - Both this and the other statement state the given term negatively
    pub fn resolve(&self, other: &Self, c: char) -> Option<Disj> {
        if self.is_unknown(c) || other.is_unknown(c) {
            return None;
        }
        if self.is_pos(c) && other.is_pos(c) {
            return None;
        }
        if self.is_neg(c) && other.is_neg(c) {
            return None;
        }

        let mut pos = HashSet::new();
        let mut neg = HashSet::new();

        pos.extend(self.pos());
        pos.extend(other.pos());
        neg.extend(self.neg());
        neg.extend(other.neg());
        pos.remove(&c);
        neg.remove(&c);

        if (!pos.is_disjoint(&neg)) {
            return None;
        }

        return Some(Self::new(pos, neg));
    }

    pub fn combine(&self, other: &Self) -> Option<Disj> {
        let mut pos = HashSet::new();
        let mut neg = HashSet::new();

        pos.extend(self.pos());
        pos.extend(other.pos());
        neg.extend(self.neg());
        neg.extend(other.neg());

        if (!pos.is_disjoint(&neg)) {
            return None;
        }

        return Some(Self::new(pos, neg));
    }

    /// Returns all the possible resolutions between this statement and the other.
    pub fn resolve_vec(&self, other: &Self) -> Vec<Disj> {
        let mut out = Vec::new();

        let mut syms = HashSet::<char>::new();

        syms.extend(self.pos.iter());
        syms.extend(self.neg.iter());
        syms.extend(other.pos.iter());
        syms.extend(other.neg.iter());

        for c in syms.iter() {
            if let Some(s) = self.resolve(other, *c) {
                out.push(s);
            }
        }

        return out;
    }

    pub fn implies(l: char, r: char) -> Disj {
        return Self::of_slices(&[r], &[l]);
    }

    pub fn axiom(t: char) -> Disj {
        return Self::of_slices(&[t], &[]);
    }

    pub fn axiom_not(t: char) -> Disj {
        return Self::of_slices(&[], &[t]);
    }

    pub fn contradiction() -> Disj {
        return Self { pos: HashSet::new(), neg: HashSet::new() }
    }
}

// Hash is somehow not implemented on HashSet itself so we have to manually implement Hash
impl Hash for Disj {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for c in self.pos.iter() {
            if !self.is_pos(*c) {
                c.hash(state);
            }
        }
        for c in self.neg.iter() {
            if !self.is_neg(*c) {
                c.hash(state);
            }
        }
    }
}

impl Display for Disj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_contradiction() {
            return write!(f, "~");
        }

        let mut sep = false;

        for p in self.pos.iter() {
            if sep {
                write!(f, " | ")?;
            } else {
                sep = true;
            }

            write!(f, "{p}")?;
        }

        for n in self.neg.iter() {
            if sep {
                write!(f, " | ")?;
            } else {
                sep = true;
            }

            write!(f, "!{n}")?;
        }

        Ok(())
    }
}

/// A statement in conjunction-normal form (CNF). A [Cnf] object acts as a set of
/// [Disj] objects.
pub struct Cnf {
    pub terms: HashSet<Disj>
}

impl Cnf {
    pub fn new() -> Cnf {
        return Cnf {
            terms: HashSet::new()
        };
    }

    pub fn of_vec(vec: &Vec<Disj>) -> Cnf {
        let mut cnf = Self::new();
        for disj in vec.iter() {
            cnf.insert((*disj).clone());
        }
        return cnf;
    }

    pub fn clear(&mut self) {
        self.terms.clear();
    }

    pub fn insert(&mut self, disj: Disj) -> bool {
        return self.terms.insert(disj);
    }

    pub fn insert_all(&mut self, cnf: &Cnf) -> bool {
        let mut ch = false;
        for disj in cnf.terms.iter() {
            ch |= self.insert((*disj).clone());
        }
        return ch;
    }

    pub fn contains(&self, disj: &Disj) -> bool {
        return self.terms.contains(disj);
    }

    pub fn contains_all(&self, cnf: &Cnf) -> bool {
        return cnf.terms.iter().all({ |e| 
            self.contains(e)
        });
    }

    pub fn resolve(&self, out: &mut Cnf) -> bool {
        let stmts = Vec::from_iter(self.terms.iter());
        let mut change = false;

        for i in 0..stmts.len() {
            for j in (i+1)..stmts.len() {
                let a = stmts[i];
                let b = stmts[j];

                let res = a.resolve_vec(b);
                for disj in res.iter() {
                    change |= out.insert((*disj).clone());
                }
            }
        }

        return change;
    }
}

impl Display for Cnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sep = false;

        write!(f, "(")?;
        for t in self.terms.iter() {
            if sep {
                write!(f, ") & (")?;
            } else {
                sep = true;
            }

            write!(f, "{t}")?;
        }
        write!(f, ")")?;

        Ok(())
    }
}