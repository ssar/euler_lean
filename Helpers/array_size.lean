-- import Mathlib
import Mathlib.Data.Nat.Defs

-- Applies f to all elements with index position + k * p in the array arr.
def mapMultiples {α : Type} (arr : Array α ) (position p : Nat) (f : α → α) : Array α :=
  if p ≤ 0 then arr
  else if h: arr.size ≤ position then
    arr
  else
    mapMultiples (arr.set position (f arr[position])) (position + p) p f
termination_by arr.size - position

#check (mapMultiples #[0,1] 1 1 id)[1]

@[simp] theorem size_mapMultiples {α : Type} (arr: Array α) (position p : Nat) (f : α → α) :
    (mapMultiples arr position p f).size = arr.size := by
    induction arr, position, p, f using mapMultiples.induct with
    | _  => unfold mapMultiples; simp[*]

#check (mapMultiples #[0,1] 1 1 id)[1]

def asq (a b:Nat) (h: a * a ≤ b) :
  a ≤ b := by
  omega

def asq' (a b:Nat) (h: a * a ≤ b) (h1: 1 < a) :
  a ≤ b := by
  omega

def asq'' (a b c:Nat) (h: a * c ≤ b) (h1: 1 ≤ c) :
  a ≤ b := by
  omega

def asqw (a b:Nat) (h: a * a ≤ b) :
  a ≤ b := by
  have as: a ≤ a * a := Nat.le_mul_self a
  omega
