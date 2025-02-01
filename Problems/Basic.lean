import Mathlib.Tactic
import Std
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Init.Data.Array.Basic

-- Project euler problem 10

-- Maps all elements with index position + k * p in the array arr.
def mapMultiples {α : Type} (arr: Array α ) (position: Nat) (p : Nat) (f : α → α): Array α :=
  if p <= 0 then arr
  else if h: arr.size ≤ position then
    arr
  else
    mapMultiples (arr.set position (f arr[position])) (position + p) p f
termination_by arr.size - position -- works because of https://leanprover-community.github.io/mathlib4_docs/Init/Data/Array/Basic.html#Preliminary-theorems

@[simp] theorem size_mapMultiples {α : Type} (arr: Array α) (position: Nat) (p : Nat) (f : α → α) :
    (mapMultiples arr position p f).size = arr.size := by
    induction arr, position, p, f using mapMultiples.induct with
    | _  => unfold mapMultiples; simp [*]

theorem values_mapMultiples {α : Type} (arr: Array α ) (position p: Nat) (f : α → α) (getIdx : Nat) (idxValid : getIdx < arr.size):
  (mapMultiples arr position p f)[getIdx]'(by simp[idxValid]) =
    if(0 < p ∧ position ≤ getIdx ∧ p ∣ (getIdx - position)) then
      f arr[getIdx]
    else
      arr[getIdx] := by
  unfold mapMultiples
  induction arr, position, p, f using mapMultiples.induct with
  | case1 arr position p f h => simp [h, not_lt_of_ge] -- case p = 0
  | case2 arr position p f h1 h2 =>
      have pos_gt_idx: getIdx < position := by apply lt_of_lt_of_le idxValid h2
      simp [h1, h2, pos_gt_idx, not_le_of_lt]
  | case3 arr position p f h1 h2 ih =>
      unfold mapMultiples
      have h1': 0 < p := by exact lt_of_not_le h1
      simp [h1, h2, h1', idxValid] at ih ⊢ -- TODO
      rw [ih]
      by_cases position_idx: position = getIdx
      · simp [position_idx, lt_of_not_ge, h1]
      · rw [Array.get_set_ne arr]
        · by_cases position_le_getIdx: position ≤ getIdx
          · have position_lt_getIdx: position < getIdx :=
              by simp[lt_iff_le_and_ne.mpr, position_idx, position_le_getIdx]
            by_cases p_dvd: p ∣ getIdx - position
            · have p_le: p ≤ getIdx - position := by
                apply Nat.le_of_dvd; simp [position_lt_getIdx]; assumption
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

def firstNonZero (a b: Nat) : Nat := if a = 0 then b else a

def calculateFactors (arr: Array Nat) (position: Nat) : Array Nat :=
  if h: position ≥ arr.size then
    arr
  else if arr[position] = 0 then
    calculateFactors (mapMultiples arr position position (firstNonZero . position)) (position + 1)
  else
    calculateFactors arr (position + 1)
termination_by arr.size - position

@[simp] theorem size_calculateFactors (arr: Array Nat) (position: Nat):
  (calculateFactors arr position).size = arr.size := by
  induction arr, position using calculateFactors.induct with
  | _  => unfold calculateFactors; simp [*]

private def minFacBelow (n below: Nat) : Nat :=
  if Nat.minFac n < below then Nat.minFac n else 0

lemma minFacBelowOnDiff (n below) :
  minFacBelow n below ≠ minFacBelow n (below + 1) -> minFacBelow n (below + 1) = below := by
  intro h
  by_cases b: n.minFac < below
  · unfold minFacBelow at h
    have b': n.minFac < below + 1 := by linarith
    simp [b, b'] at h
  by_cases c: n.minFac = below
  · unfold minFacBelow
    simp[b, c]
  · have b': below < n.minFac := by
      apply LE.le.lt_of_ne; apply le_of_not_gt; simp[b]; symm; assumption
    have b'': ¬ n.minFac < below + 1 := by linarith
    unfold minFacBelow at h
    simp [b, b''] at h

lemma minFacBelowDiffOnPrimes (n below) (belowValid: 0 ≠ below) (nValid: 1 < n):
  minFacBelow n below ≠ minFacBelow n (below + 1) -> below.Prime := by
  intro h
  apply minFacBelowOnDiff at h
  unfold minFacBelow at h
  split at h
  rw [← h]
  apply Nat.minFac_prime
  linarith
  contradiction

lemma minFacBelowDiffOnPrimes' (n below) (belowValid: 0 ≠ below) (nValid: 1 < n):
  ¬ below.Prime -> minFacBelow n below = minFacBelow n (below + 1) := by
  rw [← not_imp_not, not_not]; exact minFacBelowDiffOnPrimes n below belowValid nValid

lemma minFacNoChangeAtNoPrime (position i: Nat) (iValid: 1 < i) (isNotPrime: ¬position.Prime):
     position ≤ i.minFac ↔ (position + 1) ≤ i.minFac := by
  apply Iff.intro
  · intro a
    have h: position ≠ i.minFac := by
      intro h1;
      rw [h1] at isNotPrime;
      have iPrime: Nat.Prime i.minFac := by apply Nat.minFac_prime; linarith
      contradiction
    rw [le_iff_eq_or_lt] at a
    rw [Nat.add_one_le_iff]
    simp[h] at a
    assumption
  · intro a
    linarith

private def containsMinFacsBelow (arr: Array Nat) (below: Nat) :=
  ∀ (i : Nat) (h: i < arr.size ∧ 1 < i), arr[i] = minFacBelow i below

lemma containsMinFacsBelow_onPrimes (arr: Array Nat) (below: Nat) (belowValid: 0 ≠ below):
  (¬below.Prime) -> containsMinFacsBelow arr below -> containsMinFacsBelow arr (below + 1) := by
  unfold containsMinFacsBelow
  intro p b i h; specialize b i h
  rw [b]
  apply minFacBelowDiffOnPrimes' _ _ belowValid h.2
  assumption

lemma values_calculateFactors (arr: Array Nat) (position: Nat)(posValid : 1 < position)
     (arrValid: containsMinFacsBelow arr position):
     containsMinFacsBelow (calculateFactors arr position) arr.size := by
    induction arr, position using calculateFactors.induct with
    | case1 arr position h =>
      unfold calculateFactors; simp[h]
      unfold containsMinFacsBelow at arrValid ⊢
      intro i iValid; specialize arrValid i iValid
      unfold minFacBelow at arrValid ⊢
      have eoa: i.minFac < arr.size :=
        have iPos: 0 < i := by linarith
        calc i.minFac ≤ i := Nat.minFac_le iPos
          _ < arr.size := iValid.1
      have eoa': i.minFac < position := by linarith
      simp[eoa, eoa'] at arrValid ⊢
      assumption
    | case2 arr position h1 h2 ih =>
      have positionPrime: position.Prime := by
        have posValid': position < arr.size ∧ 1 < position := by simp [lt_of_not_le h1, posValid]
        specialize arrValid position posValid'
        unfold minFacBelow at arrValid
        rw [h2] at arrValid
        split at arrValid
        · case isTrue h =>
            apply ne_of_lt (Nat.minFac_pos position) at arrValid
            contradiction
        · case isFalse h =>
            have eq: position.minFac = position := by
              have posPos: 0 < position := by linarith
              apply eq_of_le_of_le (Nat.minFac_le posPos)
              linarith
            rw [← eq]
            apply Nat.minFac_prime
            symm
            apply ne_of_lt posValid
      unfold calculateFactors; simp[h1, h2] at ih arrValid ⊢
      apply ih; linarith
      unfold containsMinFacsBelow at arrValid ⊢
      intro i iValid; simp at iValid
      specialize arrValid i iValid
      rw[values_mapMultiples]
      · have posValid': 0 < position := by linarith
        simp[posValid']
        by_cases minFacP: i.minFac = position -- should we split on position ∣ i - position ?
        · have posdvd: position ∣ i - position := by
           rw[← minFacP]
           apply Nat.dvd_sub'
           apply Nat.minFac_dvd
           simp
          have posLeI: position ≤ i := by rw[← minFacP]; apply Nat.minFac_le; linarith
          unfold firstNonZero
          rw[arrValid]
          unfold minFacBelow
          rw [minFacP]
          simp[posLeI, posdvd]
        · by_cases positionDvd: position ∣ i
          · have positionDvd': position ∣ i - position := by
              apply Nat.dvd_sub'; assumption; apply dvd_refl
            have posLeI: position ≤ i := by apply Nat.le_of_dvd; linarith[iValid.1]; assumption
            simp[posLeI, positionDvd']
            have minFacLtPos: i.minFac < position := by
              rw[Nat.lt_iff_le_and_ne]
              simp[minFacP]
              apply Nat.minFac_le_of_dvd; linarith
              assumption
            have minFacLtPos': i.minFac < position + 1 := by linarith
            rw[arrValid]
            unfold minFacBelow
            simp[minFacLtPos, minFacLtPos']
            unfold firstNonZero
            have minFacNonZero: i.minFac ≠ 0 := by linarith[Nat.minFac_pos i]
            simp[minFacNonZero]
          · have positionDvd': position ≤ i -> ¬ position ∣ i - position := by
              intro p
              rw[← Nat.dvd_add_self_right]
              rwa[Nat.sub_add_cancel]; assumption
            have positionDvd'': ¬ (position ≤ i ∧ position ∣ i - position) := by
              rw[not_and]
              intro p
              rw[← Nat.dvd_add_self_right]
              rwa[Nat.sub_add_cancel]; assumption
            simp[positionDvd'']
            rw[arrValid]
            unfold minFacBelow
            by_cases mfp: i.minFac < position
            · have mfp': i.minFac < position + 1 := by linarith
              simp[mfp, mfp']
            · have mfp': ¬ i.minFac < position + 1 := by
                rw[Nat.lt_add_one_iff_lt_or_eq]
                simp[mfp, minFacP]
              simp[mfp, mfp']
    | case3 arr position h1 h2 ih =>
      have positionPrime: ¬position.Prime := by
        have posPos : 0 < position := by linarith
        have posValid': position < arr.size ∧ 1 < position := by simp [lt_of_not_le h1, posValid]
        specialize arrValid position posValid'
        unfold minFacBelow at arrValid
        split at arrValid
        · case isTrue h =>
            have h': position.minFac ≠ position := by linarith
            rw [Nat.prime_def_minFac]
            simp [h']
        · case isFalse h => contradiction
      unfold calculateFactors
      simp [h1, h2]
      apply ih; linarith
      apply containsMinFacsBelow_onPrimes; linarith; assumption
      assumption

def factorSieve (n : Nat) : Array Nat :=
  if h: n = 0 then
    #[2]
  else if h': n ≤ 1 then
    #[2, 1]
  else
    -- wtf
    (calculateFactors (Array.mkArray (n + 1) 0) 2).set 1 2 (by simp; have g: 0 < n := by linarith; assumption)

@[simp] theorem size_factorSieve (n : Nat) :
  (factorSieve n).size = n + 1 := by unfold factorSieve; simp

theorem values_factorSieve (n : Nat):
  ∀ (i : Nat) (h: i < n + 1), (factorSieve n)[i]'(by simp[h]) = i.minFac := by
  unfold factorSieve
  intro i h
  -- simp[values_calculateFactors]
  -- unfold containsMinFacsBelow
  -- simp
  -- intro arrValid
  match n with
  | 0 => simp at h; simp[h]
  | 1 =>
    simp at h;
    simp[h];
    match i with
      | 0 => simp
      | 1 => simp
  | n + 2 =>

    match i with
      | 0 => simp
      | 1 => simp
      | i + 2 => sorry
  split
  . case isTrue nz =>
      rw[nz] at h
      simp at h
      simp[h]
  · case isFalse =>
      split
      · case isTrue n1

    intro i h1 h2
    rw [values_calculateFactors]
    simp
    unfold minFacBelow
    have minfacLeN: i.minFac < n + 1 :=
    calc i.minFac ≤ i := by apply Nat.minFac_le; linarith
      _ < n + 1 := h1
    simp[minfacLeN]
    linarith
    unfold containsMinFacsBelow
    unfold minFacBelow
    simp
    intro j _ jGtOne
    have minFacGeTwo: ¬ j.minFac < 2 := by
      simp
      apply Nat.Prime.two_le
      apply Nat.minFac_prime; linarith
    simp[minFacGeTwo]
    have h2': 1 < i := by linarith
    simp[h1,h2']


#check values_mapMultiples
lemma calculateFactors_doesNotModifyFirst (arr: Array Nat)(pos: Nat)
  (arrValid: 0 < arr.size)(posValid: 1 < pos):
  (calculateFactors arr pos)[0]'(by simp[*]) = arr[0] := by
  -- unfold calculateFactors;
  induction arr, pos using calculateFactors.induct with
  | case1 arr position h => unfold calculateFactors; simp[h]
  | case2 arr position h1 h2 ih =>
     unfold calculateFactors
     simp[*]
     rw [values_mapMultiples]
     have posValid': 0 < position := by linarith
     simp[*] at ih ⊢; rw[← ih];
     sorry
  | case3 arr position h1 h2 ih  => sorry


lemma zero_factorSieve' (arr: Array Nat) (position: Nat)(posValid : 1 < position)
     (arrValid: containsMinFacsBelow arr position):
     (factorSieve n)[0] = 0 := by
     unfold factorSieve
    induction (mkArray (n + 1) 0), 2 using calculateFactors.induct with
    | case1 arr position h => unfold calculateFactors; simp[h]; sorry
    | case2 arr position h1 h2 ih => sorry
    | case3 arr position h1 h2 ih  => sorry

theorem zero_factorSieve (n : Nat):
  (factorSieve n)[0] = 0 := by
    unfold factorSieve
    -- let a := mkArray (n + 1)
    induction (mkArray (n + 1) 0), n using calculateFactors.induct with
    | case1 arr position h => unfold calculateFactors; simp[h]; sorry
    | case2 arr n h1 h2 ih => sorry
    | case3 arr n h1 h2 ih  => sorry
  sorry


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

def S_impl (n : Nat) :=
  foldlWithIndex addIfEqual 0 (factorSieve n) 2
#eval S_impl 200 -- expect 4227
-- #eval S_impl 2000000 -- 142913828922

def S (n: Nat) := ∑ p ∈ Nat.primesBelow n, p

#check S 10

theorem S_impl_implements_S (n : Nat) : S n = S_impl n := by
  unfold S S_impl
  induction n
  case zero => unfold foldlWithIndex; simp
  case succ n ih =>
    rw[Nat.primesBelow_succ]
    by_cases isPrime: n.Prime
    · simp[isPrime]
      rw[Finset.sum_insert]
      rw[ih]
      sorry
      intro h
      apply Nat.lt_of_mem_primesBelow at h
      linarith
    · simp[isPrime]
      rw [ih]
      sorry

-- #check countIfEqual Nat.add
--(dbgTraceIfShared "foldlWithIndex" arr)
