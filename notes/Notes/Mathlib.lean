import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Mathlib" =>
%%%
tag := "mathlib"
htmlSplit := .never
%%%

*Mathlib*{index}[Mathlib] is Lean's large, community-maintained library of mathematics, tactics, and data structures.
It contains algebra, analysis, topology, combinatorics, and the automation that makes everyday proofs practical.

The `lean/` package depends on Mathlib `v4.35.0`, the release that matches Lean `v4.35.0`.
The dependency is declared in `lean/lakefile.toml` and pinned in `lean/lake-manifest.json`.

The `notes/` package deliberately does not depend on Mathlib.
Only the code package pays the cost of building it.

# Importing it
%%%
tag := "mathlib-import"
%%%

Most files that use Mathlib start with:

```
import Mathlib.Tactic
```

`Mathlib.Tactic` imports the commonly used tactics.
A more targeted import such as `Mathlib.Data.Nat.Basic` builds faster, but `Mathlib.Tactic` is convenient while learning.

`lean/Brane/Exercises.lean` uses this import so that the `omega` tactic is available.

# Tactics
%%%
tag := "mathlib-tactics"
%%%

A tactic transforms the current proof goal.
Some useful ones:

: `rfl`

  Closes goals that hold by definitional equality.

: `simp`

  Rewrites with the lemmas in its simp set.

: `omega`

  Decides linear arithmetic over integers and naturals.

: `ring`

  Normalizes expressions in commutative (semi)rings.

: `aesop`

  Runs a general-purpose proof search.

The first exercise in {ref "exercises"}[Exercises] is solved by `omega`.
The infoview in {ref "lean-nvim"}[lean.nvim] shows the goal before and after each tactic, which is the fastest way to learn what a tactic does.

# The cache
%%%
tag := "mathlib-cache"
%%%

Mathlib is large, so its build artifacts are distributed as a cache.
In a fresh checkout, run:

```
lake exe cache get
```

from the directory of the package that depends on Mathlib.
This downloads precompiled `.olean` files instead of building everything locally.

This workspace already has a populated `lean/.lake` directory, so the cache has been fetched.
