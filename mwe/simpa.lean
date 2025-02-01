import Mathlib.Tactic
import Std
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers

example (p getIdx position : Nat) (h: position < getIdx): 0 < getIdx - position := by
  simp [h]; assumption

example (p getIdx position : Nat) (h: position < getIdx): 0 < getIdx - position := by
  simpa [h];
