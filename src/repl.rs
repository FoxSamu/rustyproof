use std::fs::read;
use std::io::{self, BufRead};

use crate::cnf::{Cnf, Disj};
use crate::parser::*;

pub fn repl() {
    let mut cnf = Cnf::new();

    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let ln = line.unwrap();

        let mut par = Parser::new(ln);
        match par.expr() {

            // on question: check if we have the requested statement along our knowledge
            ParsedStatement::Question(o) => {
                let n = o.cnf();
                println!("> CNF: {n}");

                if cnf.contains_all(&n) {
                    println!("> Satisfied!")
                } else {
                    println!("> Not satisfied!")
                }
            },

            // on axiom: compute further resolvents from the axiom and existing knowledge
            ParsedStatement::Axiom(o) => {
                let n = o.cnf();
                println!("> CNF: {n}");

                cnf.insert_all(&n);

                let mut other = Cnf::new();

                loop {
                    other.clear();
                    cnf.resolve(&mut other);
                    if !cnf.insert_all(&other) {
                        break;
                    }
                }

                println!("> Resolved: {cnf}");

                if cnf.contains(&Disj::contradiction()) {
                    println!("> Contradiction! Resetting statements");
                    cnf.clear();
                }
            },

            // on stop: just exit
            ParsedStatement::Stop => break,

            // on error: mark where the error is in the input and print the error message
            ParsedStatement::Error(msg, idx) => {
                for _ in 0..idx {
                    print!(" ");
                }
                println!("^");

                println!("> Error! {msg}");
            }
        }
    }
}