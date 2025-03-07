# Rustyproof

A small theorem prover for propositional logic, by means of resolution, written in Rust.

# Running

Navigate the terminal to the root directory of the project. Given you have the correct Rust version installed, this will run the program in the terminal:
```
cargo run
```

# Usage

The prover is a REPL-like interface. You can write axioms to its input which it will treat as truth, and then ask it a question to which it will answer whether it follows from the axioms.

An expression consists of symbols (single character names), and the following operators (in order of precedence):
- Contradiction `~`, Tautology `*`
- Negation `!X`
- Implication `A -> B`, Reverse-Implication `A <- B`, Bi-Implication `A <-> B`
- Conjunction `A & B`
- Disjunction `A | B`

To alter precedence, you can wrap expressions in parentheses

Here are some example expressions
```
A -> B

!(A & B) -> (!A | !B)
```

Input works as follows:
- The input `A` is treated as axiom
- The input `A?` is treated as question
- An empty input will stop the REPL

# Examples

Prove DeMorgan's rule of a negated conjunction:
```
!(A & B)
(!A | !B)?
```

# Known issues

- When parsing an empty input, the program will run into a stack-overflow and exit. If it works, it works...

# License



Copyright 2025 Olaf Nankman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
