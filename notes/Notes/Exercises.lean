import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../lean"
set_option verso.exampleModule "Brane.Exercises"

#doc (Manual) "Exercises" =>
%%%
tag := "exercises"
htmlSplit := .never
%%%

The exercises live in `lean/Brane/Exercises.lean`.
They are quoted here through anchors, so the text always shows the current source.

The first theorem is complete and serves as an example.
The second contains `sorry`, Lean's placeholder for an unfinished proof.
Replacing a `sorry` with a proof is the basic loop of formalization.

# A worked example
%%%
tag := "exercise-worked"
%%%

```anchor add_comm_exercise
theorem add_comm_exercise (a b : Nat) : a + b = b + a := by
  omega
```

The statement is commutativity of addition on natural numbers.
The proof uses {index}[omega] `omega`, a linear arithmetic decision procedure.
The proof is a single tactic, `omega`, which decides linear arithmetic goals.

`omega` is imported from Mathlib.
The `module` header at the top of the file is required because the file imports a module-system library.

# Your first exercise
%%%
tag := "exercise-first"
%%%

```anchor zero_add_exercise
theorem zero_add_exercise (n : Nat) : 0 + n = n := by
  sorry
```

The goal is `0 + n = n`.
Addition on `Nat` is defined by recursion on the second argument, so this equality holds by computation.
That suggests a very short proof.

Try these steps:

 * Open `lean/Brane/Exercises.lean`.
 * Place the cursor on the `sorry`.
 * Open the infoview with `,i` and inspect the goal.
 * Replace `sorry` with `rfl` and save.
 * If you want more practice, try `simp` or `omega` as well.

`make lean` should then build without the `sorry` warning for this declaration.

# Next steps
%%%
tag := "exercise-next"
%%%

Once the exercise is finished, add a lemma of your own to `Brane/Exercises.lean`, for example a statement about `double` from `Brane/Basic.lean`.
Then quote it here with a new anchor.

The workflow is:

 * Add `-- ANCHOR: name` and `-- ANCHOR_END: name` comments around the declaration.
 * Add a ```` ```anchor name ```` block to this chapter.
 * Rebuild the notes and check the rendered output.

See {ref "verso-anchors"}[Anchors and external code] for the exact syntax.
