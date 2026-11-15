namespace Brane

-- ANCHOR: hello
def hello : String := "world"
-- ANCHOR_END: hello

-- ANCHOR: double
def double (n : Nat) : Nat := n + n
-- ANCHOR_END: double

-- ANCHOR: double_eq_two_mul
theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  simp [double, Nat.two_mul]
-- ANCHOR_END: double_eq_two_mul

end Brane
