import Mathlib.Tactic
import Std
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Multiset.Nodup
import Mathlib.Data.Multiset.Nodup
import Mathlib.NumberTheory.SmoothNumbers
import Init.Data.Array.Basic

-- Fills all elements with index position + k * p in the array arr.
def fillMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (v : α): Array α :=
  if p <= 0 then arr -- TODO: make this a constraint.
  else if h: position ≥ arr.size then
    arr
  else
    fillMultiples (arr.set poxsition v) (position + p) p v -- need to update lean
termination_by arr.size - position -- works because of https://leanprover-community.github.io/mathlib4_docs/Init/Data/Array/Basic.html#Preliminary-theorems

@[simp] theorem size_fillMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (v : α) :
    (fillMultiples arr position p v).size = arr.size := by
    unfold fillMultiples
    induction arr, position, p, v using fillMultiples.induct with
    | case1 arr position p v h =>
      simp [h]
    | case2 arr position p v h1 h2 =>
      simp [h1, h2]
    | case3 arr position p v h1 h2 ih =>
      simp [h1] at ih
      simp [h1, h2]
      unfold fillMultiples
      simp [h1]
      exact ih

theorem values_fillMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (v : α) (getIdx : Nat) (idxValid : getIdx < arr.size):
  (fillMultiples arr position p v)[getIdx]'(by simp[idxValid]) =
    if(p > 0 ∧ getIdx >= position ∧ p ∣ (getIdx - position)) then
      v
    else
      arr[getIdx] := by
  unfold fillMultiples
  induction arr, position, p, v using fillMultiples.induct with
  | case1 arr position p v h => -- case p = 0
      simp [h, not_lt_of_ge]
  | case2 arr position p v h1 h2 =>
      have pos_gt_idx: getIdx < position := by apply lt_of_lt_of_le idxValid h2
      simp [h1, h2, pos_gt_idx, not_le_of_lt]
  | case3 arr position p v h1 h2 ih =>
      unfold fillMultiples
      have h1': 0 < p := by exact lt_of_not_le h1
      simp [h1, h2, h1', idxValid] at ih ⊢
      rw [ih]
      by_cases position_idx: position = getIdx
      rw [position_idx]
      simp
      rw [Array.get_set_ne arr]
      sorry -- position != getIdx
      sorry
      sorry
      sorry


def fillSieve (sieve: Array Nat) (position: Nat) : Array Nat :=
  if position ≥ sieve.size then
    sieve
  else if sieve[position]! == 0 then
    fillSieve (fillMultiples sieve position position position) (position + 1)
  else
    fillSieve sieve (position + 1)
termination_by sieve.size - position

def factorSieve (n : Nat) : Array Nat :=
  fillSieve (Array.mkArray (n + 1) 0) 2

def foldlWithIndex.{u, v} {α : Type u} {β : Type v} (f : β → Nat → α → β) (init : β) (arr : Array α) (start : Nat := 0) : β :=
  if h: start < arr.size then
    foldlWithIndex f (f init start arr[start]) arr (start + 1)
  else
    init
termination_by arr.size - start

def addIfEqual (acc v2 idx: Nat) : Nat :=
  if v2 = idx then
    acc + v2
  else
    acc

def sum (sieve : Array Nat) : Nat :=
  foldlWithIndex addIfEqual 0 sieve

def S_impl (n : Nat) :=
  foldlWithIndex addIfEqual 0 (factorSieve n)
#eval! S_impl 200 -- expect 4227
-- #eval! S_impl 2000000

def S (n: Nat) := ∑ p ∈ Nat.primesBelow n, p

#check S 10

theorem S_impl_implements_S (n : Nat) : S n = S_impl n := by
  -- use induction
  sorry


-- #check countIfEqual Nat.add
