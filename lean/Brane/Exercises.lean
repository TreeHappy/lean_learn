/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
module
import Mathlib.Tactic

/-!
# Exercises

Small Lean exercises for this project. See `notes/Notes/Exercises.lean` for
the accompanying explanation.
-/

public section

namespace Brane

-- ANCHOR: add_comm_exercise
theorem add_comm_exercise (a b : Nat) : a + b = b + a := by
  omega
-- ANCHOR_END: add_comm_exercise

-- ANCHOR: zero_add_exercise
theorem zero_add_exercise (n : Nat) : 0 + n = n := by
  sorry
-- ANCHOR_END: zero_add_exercise

end Brane
