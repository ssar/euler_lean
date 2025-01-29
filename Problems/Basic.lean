import Mathlib.Tactic
import Std
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Init.Data.Array.Basic

-- Project euler problem 10

-- Fills all elements with index position + k * p in the array arr.
def fillMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (v : α): Array α :=
  if p <= 0 then arr
  else if h: arr.size ≤ position then
    arr
  else
    fillMultiples (arr.set position v) (position + p) p v
termination_by arr.size - position -- works because of https://leanprover-community.github.io/mathlib4_docs/Init/Data/Array/Basic.html#Preliminary-theorems

@[simp] theorem size_fillMultiples {α : Type} (arr: Array α) (position: Nat) (p : Nat) (v : α) :
    (fillMultiples arr position p v).size = arr.size := by
    unfold fillMultiples
    induction arr, position, p, v using fillMultiples.induct with
    | case1 arr position p v h => simp [h]
    | case2 arr position p v h1 h2 => simp [h1, h2]
    | case3 arr position p v h1 h2 ih =>
      unfold fillMultiples
      simpa [h1, h2, ih] using ih

theorem values_fillMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (v : α) (getIdx : Nat) (idxValid : getIdx < arr.size):
  (fillMultiples arr position p v)[getIdx]'(by simp[idxValid]) =
    if(0 < p ∧ position ≤ getIdx ∧ p ∣ (getIdx - position)) then
      v
    else
      arr[getIdx] := by
  unfold fillMultiples
  induction arr, position, p, v using fillMultiples.induct with
  | case1 arr position p v h => simp [h, not_lt_of_ge] -- case p = 0
  | case2 arr position p v h1 h2 =>
      have pos_gt_idx: getIdx < position := by apply lt_of_lt_of_le idxValid h2
      simp [h1, h2, pos_gt_idx, not_le_of_lt]
  | case3 arr position p v h1 h2 ih =>
      unfold fillMultiples
      have h1': 0 < p := by exact lt_of_not_le h1
      simp [h1, h2, h1', idxValid] at ih ⊢ -- TODO
      rw [ih]
      by_cases position_idx: position = getIdx
      · simp [position_idx, lt_of_not_ge]
      · rw [Array.get_set_ne arr]
        · by_cases position_le_getIdx: position ≤ getIdx
          · have position_lt_getIdx: position < getIdx :=
              by simp[lt_iff_le_and_ne.mpr, position_idx, position_le_getIdx]
            by_cases p_dvd: p ∣ getIdx - position
            · have p_le: p ≤ getIdx - position := by
                apply Nat.le_of_dvd; simp [position_lt_getIdx]; assumption -- why simpa doesnt work? -> ask
              have p_le': position + p ≤ getIdx := by
                exact Nat.add_le_of_le_sub' position_le_getIdx p_le
              have p_dvd': p ∣ getIdx - (position + p) := by
                rw [Nat.sub_add_eq]; apply Nat.dvd_sub'; exact p_dvd; exact Nat.dvd_refl p
              simp[position_le_getIdx, p_dvd, p_le', p_dvd']
            simp[position_le_getIdx, p_dvd] -- TODO
            intro position_le_getIdx'
            rw [Nat.sub_add_eq, ← Nat.dvd_add_self_right, Nat.sub_add_cancel]
            simp [p_dvd] -- TODO
            rwa [← Nat.sub_le_sub_iff_right position_le_getIdx,
                  Nat.add_sub_cancel_left] at position_le_getIdx'
          simp[position_le_getIdx] -- TODO
          intro position_le_getIdx'
          have h: position ≤ getIdx :=
          calc position ≤ position + p := by simp
            _ ≤ getIdx := by assumption
          contradiction
        · assumption
        assumption

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
