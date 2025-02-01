import Mathlib

def make_array (n: Nat): Array Nat :=
  (Array.mkArray (n + 1) 0).set 0 1

theorem values_make_array (n i : Nat) (h1: i < n + 1):
  (make_array n)[i]'(by unfold make_array; simp[h1]) =
    if i = 0 then 1 else i := by
  unfold make_array
  split
  . case isTrue iz =>
      simp[iz]
      -- rw[iz] at h1-- fails even though we have iz : i = 0
  · case isFalse nz => sorry
