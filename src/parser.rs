use crate::stmt::Stmt;
use crate::parser::ParseResult::*;

/// Recursive-descent parser for [Stmt]s.
pub struct Parser {
    index: usize,
    input: Vec<char>,
}

enum ParseResult<T> {
    /// Parsed object is found and properly parsed
    Ok(T),

    /// Parsed object is not found
    Absent(usize),

    /// Parsed object is found but has an incorrect syntax
    Error(String, usize)
}

pub enum ParsedStatement {
    /// An axiom was parsed: this statement must be assumed to be true.
    Axiom(Stmt),

    /// A question wa parsed: we must resolve this question against the set of knowledge.
    Question(Stmt),

    /// Stop signal: end the REPL.
    Stop,

    /// Some error was found in the input
    Error(String, usize)
}

impl<T> ParseResult<T> {
    fn error_if_absent(self, message: &str) -> ParseResult<T> {
        return match self {
            Absent(idx) => Error(String::from(message), idx),
            r => r
        };
    }

    fn is_not_present(&self) -> bool {
        return match self {
            Ok(_) => false,
            Absent(_) => true,
            Error(_, _) => true,
        }
    }
}

impl Parser {
    pub fn new(line: String) -> Parser {
        return Parser { index: 0, input: Vec::from_iter(line.chars()) };
    }

    fn has(&self, c: char) -> bool {
        return self.index < self.input.len() && self.input[self.index] == c;
    }

    fn cur(&self) -> Option<char> {
        return if self.index < self.input.len() {
            Some(self.input[self.index])
        } else {
            None
        }
    }

    fn off(&self, o: usize) -> Option<char> {
        return if (self.index + o) < self.input.len() {
            Some(self.input[self.index + o])
        } else {
            None
        }
    }

    fn shift(&mut self) {
        self.index += 1;
    }

    /// Skips over whitespace.
    fn ws(&mut self) {
        while self.has(' ') || self.has('\t') || self.has('\n') || self.has('\r') {
            self.shift();
        }
    }

    /// Reads an expression.
    pub fn expr(&mut self) -> ParsedStatement {
        return match self.or() {
            Ok(s) => {
                self.ws();
                match self.cur() {
                    Some('?') => {
                        self.shift();
                        if let Some(_) = self.cur() {
                            return ParsedStatement::Error(String::from("Expected end"), self.index)
                        }

                        return ParsedStatement::Question(s);
                    }
                    Some(_) => {
                        return ParsedStatement::Error(String::from("Expected '?' or end"), self.index)
                    }
                    None => {
                        return ParsedStatement::Axiom(s);
                    }
                }
            }
            Absent(_) => ParsedStatement::Stop,
            Error(msg, idx) => ParsedStatement::Error(msg, idx)
        }
    }

    /// Parses a symbol: `P` for any character P
    fn symbol(&mut self) -> ParseResult<Stmt> {
        self.ws();
        if let Some(cur) = self.cur() {
            if cur >= 'A' && cur <= 'Z' || cur >= 'a' && cur <= 'z' {
                self.shift();
                return Ok(Stmt::symbol(cur));
            }
        }
        
        return Absent(self.index);
    }

    /// Parses a not expression: `!x` for any atomic expression x
    fn not(&mut self) -> ParseResult<Stmt> {
        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '!' {
                return Absent(self.index);
            }
            self.shift();
        }
        
        self.ws();

        return match self.base() {
            Ok(s) => Ok(s.not()),
            o => o.error_if_absent("Expected expression")
        };
    }

    /// Parses a contradiction: `~`
    fn cont(&mut self) -> ParseResult<Stmt> {
        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '~' {
                return Absent(self.index);
            }
            self.shift();
        }

        return Ok(Stmt::cont())
    }

    /// Parses a tautology: `*`
    fn taut(&mut self) -> ParseResult<Stmt> {
        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '*' {
                return Absent(self.index);
            }
            self.shift();
        }

        return Ok(Stmt::taut())
    }
    
    /// Parses an atomic expression: `*`, `~`, `(x)`, `!a`, `P` for any expression x, any atomic expression a, any character P
    fn base(&mut self) -> ParseResult<Stmt> {
        self.ws();

        match self.not() {
            Absent(_) => {},
            o => return o
        };
        match self.taut() {
            Absent(_) => {},
            o => return o
        };
        match self.cont() {
            Absent(_) => {},
            o => return o
        };
        match self.symbol() {
            Absent(_) => {},
            o => return o
        };
        match self.par() {
            Absent(_) => {},
            o => return o
        };

        return Absent(self.index);
    }

    /// Parses a parenthesized expression: `(x)` for any expression x
    fn par(&mut self) -> ParseResult<Stmt> {
        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '(' {
                return Absent(self.index);
            }
            self.shift();
        }

        self.ws();

        let i = match self.or() {
            Ok(s) => s,
            o => return o.error_if_absent("Expected expression")
        };

        self.ws();

        if let Some(cur) = self.cur() {
            if cur != ')' {
                return Absent(self.index).error_if_absent("Expected ')'");
            }
            self.shift();
        }

        return Ok(i)
    }

    /// Parses an implication or bi-implication, or reverse implication: `a <- b`, `a -> b`, `a <-> b` for any atomic expression a, b
    fn implication(&mut self) -> ParseResult<Stmt> {
        self.ws();

        let l = match self.base() {
            Ok(s) => s,
            o => return o
        };

        self.ws();

        let c = match (self.cur(), self.off(1), self.off(2)) {
            (Some('-'), Some('>'), _) => {
                self.shift();
                self.shift();
                0
            }
            (Some('<'), Some('-'), Some('>')) => {
                self.shift();
                self.shift();
                self.shift();
                1
            }
            (Some('<'), Some('-'), _) => {
                self.shift();
                self.shift();
                2
            }
            _ => return Ok(l)
        };

        self.ws();

        let r = match self.implication() {
            Ok(s) => s,
            o => return o.error_if_absent("Expected expression")
        };

        return if c == 0 {
            Ok(l.implies(r))
        } else if c == 1 {
            Ok(l.equiv(r))
        } else {
            Ok(r.implies(l))
        }
    }

    /// Parses a conjunction: `a & b` for any implications a, b
    fn and(&mut self) -> ParseResult<Stmt> {
        self.ws();

        let l = match self.implication() {
            Ok(s) => s,
            o => return o
        };

        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '&' {
                return Ok(l);
            }
            self.shift();
        } else {
            return Ok(l);
        }

        self.ws();

        let r = match self.and() {
            Ok(s) => s,
            o => return o.error_if_absent("Expected expression")
        };

        return Ok(l.and(r))
    }

    /// Parses a disjunction: `a | b` for any conjunctions a, b
    fn or(&mut self) -> ParseResult<Stmt> {
        self.ws();

        let l = match self.and() {
            Ok(s) => s,
            o => return o
        };

        self.ws();

        if let Some(cur) = self.cur() {
            if cur != '|' {
                return Ok(l);
            }
            self.shift();
        } else {
            return Ok(l);
        }

        self.ws();

        let r = match self.or() {
            Ok(s) => s,
            o => return o.error_if_absent("Expected expression")
        };

        return Ok(l.or(r))
    }
}