import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../lean"
set_option verso.exampleModule "Brane.Basic"

#doc (Manual) "Lean 4" =>
%%%
tag := "lean"
htmlSplit := .never
%%%

Lean{index}[Lean] is a functional programming language and an interactive theorem prover.
Terms are values, types are first-class, and proofs are terms whose type is a proposition.
The same language is used for programs, specifications, and proofs, which is why a Lean project can mix computation and mathematics in one file.

This workspace uses Lean `v4.35.0`, pinned by the `lean-toolchain` file in each package.
The `elan` tool manager reads that file and selects the matching compiler.

# A first definition
%%%
tag := "lean-definition"
%%%

The simplest definitions bind a name to a value.
The following declaration comes from `lean/Brane/Basic.lean`:

```anchor hello
def hello : String := "world"
```

`hello` is a `String`, inferred from the literal on the right-hand side.
Type annotations are optional when Lean can infer them, but writing them down often makes errors easier to read.

# Functions
%%%
tag := "lean-functions"
%%%

Functions are defined by pattern matching or by expressions.
This one takes a natural number and returns its double:

```anchor double
def double (n : Nat) : Nat := n + n
```

The result type is `Nat`, and the body is an ordinary expression.
Lean does not distinguish between "programs" and "mathematical functions"; `double` can be evaluated and can also appear in theorems.

# Propositions and proofs
%%%
tag := "lean-proofs"
%%%

A theorem is a declaration whose type is a proposition.
The proof is a term of that type.
Tactic proofs are written with `by`, which switches to tactic mode:

```anchor double_eq_two_mul
theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  simp [double, Nat.two_mul]
```

The statement says that doubling a number is the same as multiplying it by two.
The proof rewrites with the definition of `double` and the lemma `Nat.two_mul`.

You can check any declaration in the editor with `#check`, evaluate it with `#eval`, and inspect the proof state after each tactic line in the infoview.
See {ref "lean-nvim"}[lean.nvim] for the editor bindings.

# Further reading
%%%
tag := "lean-reading"
%%%

 * [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
 * [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
 * [Lean language reference](https://lean-lang.org/doc/reference/latest/)
 * {ref "exercises"}[Exercises] in this manual
