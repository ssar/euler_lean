import Mathlib.Tactic
import Std
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Init.Data.Array.Basic
-- import Mathlib

-- Project euler problem 10: https://projecteuler.net/problem=10

/-! ### Function to calculate -/

def S (n: Nat) := ∑ p ∈ Nat.primesBelow n, p

/-! ### Implementation of solution -/

-- Maps all elements with index position + k * p in the array arr.
def mapMultiples {α : Type} (arr : Array α ) (position p : Nat) (f : α → α) : Array α :=
  if p ≤ 0 then arr
  else if h: arr.size ≤ position then
    arr
  else
    mapMultiples (arr.set position (f arr[position])) (position + p) p f
termination_by arr.size - position

@[simp] theorem size_mapMultiples {α : Type} (arr: Array α) (position p : Nat) (f : α → α) :
    (mapMultiples arr position p f).size = arr.size := by
    induction arr, position, p, f using mapMultiples.induct with
    | _  => unfold mapMultiples; simp[*]

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

def factorSieve (n : Nat) : Array Nat :=
  match n with
  | 0 => #[2]
  | 1 => #[2, 1]
  | n + 2 => ((calculateFactors (Array.mkArray (n + 3) 0) 2).set 1 1).set 0 2

@[simp] theorem size_factorSieve (n : Nat) : (factorSieve n).size = n + 1 := by
  unfold factorSieve
  split; all_goals simp

def sieve_isPrime (arr : Array Nat) (n: Nat) (_: n < arr.size := by get_elem_tactic): Bool :=
  2 ≤ n ∧ arr[n] = n

def S_calc (arr : Array Nat) (n acc : Nat := 0) (_: n < arr.size := by get_elem_tactic) : Nat :=
  if n = 0 then acc
  else if sieve_isPrime arr n then
    S_calc arr (n - 1) (acc + n)
  else
    S_calc arr (n - 1) acc
termination_by n

def S_impl (n : Nat): Nat := S_calc (factorSieve (n - 1)) (n - 1)

#eval S_impl 200 -- expect 4227
-- #eval S_impl 2000000 -- 142913828922

/-! ### Proof of correctness -/

theorem values_mapMultiples {α : Type} (arr: Array α ) (position p: Nat) (f : α → α) (getIdx : Nat)
    (idxValid : getIdx < arr.size):
  (mapMultiples arr position p f)[getIdx]'(by simp[idxValid]) =
    if(0 < p ∧ position ≤ getIdx ∧ p ∣ (getIdx - position)) then
      f arr[getIdx]
    else
      arr[getIdx] := by
  induction arr, position, p, f using mapMultiples.induct with
  | case1 arr position p f h => unfold mapMultiples; simp[h, not_lt_of_ge]
  | case2 arr position p f h1 h2 =>
      unfold mapMultiples
      have posGtIdx: getIdx < position := by linarith
      simp_arith [h1, h2, posGtIdx, not_le_of_lt]
  | case3 arr position p f h1 h2 ih =>
      unfold mapMultiples
      have h1': 0 < p := by exact lt_of_not_le h1
      simp [h1, h2, h1', idxValid] at ih ⊢
      rw [ih]
      by_cases position_idx: position = getIdx
      · simp [position_idx, lt_of_not_ge, h1]
      · rw [Array.get_set_ne arr]
        · by_cases position_le_getIdx: position ≤ getIdx
          · have position_lt_getIdx: position < getIdx := by
              simp[lt_iff_le_and_ne.mpr, position_idx, position_le_getIdx]
            by_cases p_dvd: p ∣ getIdx - position
            · have p_le: p ≤ getIdx - position := by
                apply Nat.le_of_dvd; simp [position_lt_getIdx]; assumption
              have p_le': position + p ≤ getIdx := by
                exact Nat.add_le_of_le_sub' position_le_getIdx p_le
              have p_dvd': p ∣ getIdx - (position + p) := by
                rw [Nat.sub_add_eq]; apply Nat.dvd_sub'; exact p_dvd; exact Nat.dvd_refl p
              simp[position_le_getIdx, p_dvd, p_le', p_dvd']
            simp[position_le_getIdx, p_dvd]
            intro position_le_getIdx'
            rw [Nat.sub_add_eq, ← Nat.dvd_add_self_right, Nat.sub_add_cancel]
            simp only [p_dvd, IsEmpty.forall_iff]
            rwa [← Nat.sub_le_sub_iff_right position_le_getIdx,
                  Nat.add_sub_cancel_left] at position_le_getIdx'
          simp[position_le_getIdx]
          omega
        · assumption
        assumption

private def minFacBelow (n below: Nat) : Nat :=
  if Nat.minFac n < below then Nat.minFac n else 0

private def containsMinFacsBelow (arr: Array Nat) (below: Nat) :=
  ∀ (i : Nat) (h: i < arr.size ∧ 1 < i), arr[i] = minFacBelow i below

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
  · rw [← h]
    apply Nat.minFac_prime
    linarith
  · contradiction

lemma minFacBelowDiffOnPrimes' (n below) (belowValid: 0 ≠ below) (nValid: 1 < n):
  ¬ below.Prime -> minFacBelow n below = minFacBelow n (below + 1) := by
  rw [← not_imp_not, not_not]; exact minFacBelowDiffOnPrimes n below belowValid nValid

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
        by_cases minFacP: i.minFac = position
        · subst position
          have posdvd: i.minFac ∣ i - i.minFac := by
           apply Nat.dvd_sub'
           apply Nat.minFac_dvd
           simp
          have posLeI: i.minFac ≤ i := by apply Nat.minFac_le; linarith
          unfold firstNonZero
          rw[arrValid]
          unfold minFacBelow
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

theorem values_factorSieve (n : Nat):
  ∀ (i : Nat) (h: i < n + 1), (factorSieve n)[i]'(by simp[h]) = i.minFac := by
  unfold factorSieve
  intro i h
  match n with
  | 0 => simp only [zero_add, Nat.lt_one_iff] at h; simp[h]
  | 1 =>
    match i with
      | 0 => simp
      | 1 => simp
  | n + 2 =>
    match i with
      | 0 => simp
      | 1 => simp
      | i + 2 =>
        simp
        rw[values_calculateFactors]
        · unfold minFacBelow
          have minfacLeN: (i + 2).minFac < n + 3 :=
          calc (i + 2).minFac ≤ (i + 2) := by apply Nat.minFac_le; linarith
            _ < n + 3 := by linarith
          simp[h, minfacLeN]
        · simp
        · unfold containsMinFacsBelow
          unfold minFacBelow
          intro j hj
          have minFacGeTwo: ¬ j.minFac < 2 := by
            rw[not_lt]
            apply Nat.Prime.two_le
            apply Nat.minFac_prime
            linarith
          simp[hj, minFacGeTwo]
        · simp[h]

theorem S_calc_rec (arr : Array Nat) (n: Nat) (acc: Nat) (s: n < arr.size):
    S_calc arr n acc = (S_calc arr n) + acc := by
  induction n generalizing acc
  case zero => unfold S_calc; simp
  case succ n ih =>
    unfold S_calc
    simp
    split
    nth_rw 1 [ih]
    nth_rw 2 [ih]
    linarith
    nth_rw 1 [ih]

theorem sieve_isPrime_prime (n m : Nat) (h: m ≤ n := by get_elem_tactic) :
  sieve_isPrime (factorSieve n) m (by simp_arith; assumption) ↔ m.Prime := by
  unfold sieve_isPrime
  rw[values_factorSieve]
  rw[Nat.prime_def_minFac]
  simp
  linarith

lemma S_calc_succ (n l1 l2 acc: Nat)
        (h1: n ≤ l1 := by get_elem_tactic) (h2: n ≤ l2 := by get_elem_tactic):
  S_calc (factorSieve l1) n acc (by simp;omega) =
      S_calc (factorSieve l2) n acc (by simp;omega) := by
  induction n generalizing acc
  case zero => unfold S_calc; simp
  case succ n ih =>
    unfold S_calc
    simp
    simp[sieve_isPrime_prime l1 (n + 1)]
    simp[sieve_isPrime_prime l2 (n + 1)]
    rw[ih]
    rw[ih]

theorem S_impl_succ (n : Nat):
  S_impl (n + 1) = if Nat.Prime n then (S_impl n) + n else S_impl n := by
  nth_rw 1 [S_impl]
  simp
  unfold S_calc
  split
  · case isTrue h => unfold S_impl; unfold S_calc; simp[h]
  · case isFalse h =>
      unfold S_impl
      simp[sieve_isPrime_prime]
      split
      · rw[S_calc_rec]
        rw[S_calc_succ (n - 1) n (n - 1)]
      · rw[S_calc_succ (n - 1) n (n - 1)]

theorem S_impl_implements_S (n : Nat) : S n = S_impl n := by
  unfold S
  induction n
  case zero => unfold S_impl; unfold S_calc; simp
  case succ n ih =>
    rw[Nat.primesBelow_succ]
    by_cases isPrime: n.Prime
    · simp only [isPrime, ↓reduceIte]
      rw[Finset.sum_insert, ih]
      simp[S_impl_succ, isPrime, Nat.add]
      linarith
      intro pb
      apply Nat.lt_of_mem_primesBelow at pb
      linarith
    · simp only [isPrime, ↓reduceIte]
      simp[S_impl_succ, isPrime, Nat.add]
      linarith

/-! ### Lemmas that ended up unused. -/

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

theorem factorSieve_succ (n : Nat):
  factorSieve (n + 1) = (factorSieve n).push (n + 1).minFac := by
  apply Array.ext; simp
  intro i hi hi'
  simp only[size_factorSieve] at hi hi'
  by_cases last: i = n + 1
  · subst i
    rw[values_factorSieve]
    have fs: (factorSieve n).size = n + 1 := by simp
    have fe: ((factorSieve n).push (n + 1).minFac)[(factorSieve n).size] = (n + 1).minFac :=
      Array.getElem_push_eq (factorSieve n) (n + 1).minFac
    simp[fs] at fe
    simp[fe]
    linarith
  · have hi'': i < n + 1 := by
      rw[Nat.lt_add_one_iff_lt_or_eq] at hi
      simp[last] at hi
      assumption
    rw[Array.getElem_push_lt]
    rw[values_factorSieve]; rw[values_factorSieve]
    linarith; linarith
