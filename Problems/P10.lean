import Init.Data.Array.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic
import Std

-- Project euler problem 10: https://projecteuler.net/problem=10

/-! ### Function to calculate -/

def S (n: Nat) := ∑ p ∈ Nat.primesBelow n, p

/-! ### Implementation of solution -/

-- Maps all elements with index position + k * p in the array arr.
def mapMultiples {α : Type} (arr : Array α ) (position p : Nat) (f : α → α) : Array α :=
  if h: arr.size ≤ position then
    arr
  else if p = 0 then
    arr.set position (f arr[position])
  else
    mapMultiples (arr.set position (f arr[position])) (position + p) p f
termination_by arr.size - position

@[simp] theorem size_mapMultiples {α : Type} (arr: Array α) (position p : Nat) (f : α → α) :
    (mapMultiples arr position p f).size = arr.size := by
    induction arr, position, p, f using mapMultiples.induct with
    | _  => unfold mapMultiples; simp[*]

def calculateFactors_idxValid {a b: Nat} (h: ¬ b ≤ a * a):
    a < b := by
  apply lt_of_not_le at h
  calc a ≤ a * a := Nat.le_mul_self a
    _ < b := h

def calculateFactors (arr: Array Nat) (position: Nat) : Array Nat :=
  if h: position * position ≥ arr.size then
    arr
  else if arr[position]'(calculateFactors_idxValid h) = position then
    calculateFactors (mapMultiples arr (position * position) position (min position)) (position + 1)
  else
    calculateFactors arr (position + 1)
termination_by arr.size - position
decreasing_by all_goals apply calculateFactors_idxValid at h; simp; omega

@[simp] theorem size_calculateFactors (arr: Array Nat) (position: Nat):
  (calculateFactors arr position).size = arr.size := by
  induction arr, position using calculateFactors.induct with
  | _  => unfold calculateFactors; simp [*]

def factorSieve (n : Nat) : Array Nat :=
  match n with
  | 0 => #[2]
  | 1 => #[2, 1]
  | n + 2 => ((calculateFactors (Array.range (n + 3)) 2).set 0 2).set 1 1

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
    if(position ≤ getIdx ∧ p ∣ (getIdx - position)) then
      f arr[getIdx]
    else
      arr[getIdx] := by
  induction arr, position, p, f using mapMultiples.induct with
  | case1 arr position p f h1 =>
      unfold mapMultiples
      have posGtIdx: getIdx < position := by linarith
      simp_arith [h1, posGtIdx, not_le_of_lt]
  | case2 arr position f h =>
      unfold mapMultiples
      simp[h]
      simp_rw[Nat.sub_eq_zero_iff_le, ← Nat.le_antisymm_iff]
      rw[Array.get_set]
      split; simp[*]; rfl
  | case3 arr position p f h1 h2 ih =>
      unfold mapMultiples
      simp [h1, h2, idxValid] at ih ⊢
      rw [ih]
      by_cases position_idx: position = getIdx
      · simp [position_idx, lt_of_not_ge, h2]
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
  if Nat.minFac n < below then Nat.minFac n else n

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
  · subst h
    have nge: n.minFac ≤ n := by apply Nat.minFac_le; linarith
    have ngt: n.minFac < n + 1 := by linarith
    contradiction

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

lemma containsMinFacsBelow_prime {arr: Array Nat} {below p: Nat}
      (c: containsMinFacsBelow arr below) (pp: p.Prime) (pv: p < arr.size) :
    arr[p] = p := by
  unfold containsMinFacsBelow at c
  have pv': p < arr.size ∧ 1 < p := by constructor; assumption; apply Nat.Prime.one_lt; assumption
  specialize c p pv'
  rw[c]
  unfold minFacBelow
  simp[Nat.Prime.minFac_eq pp]

lemma containsMinFacsBelow_bSquared (arr: Array Nat) (below: Nat) :
   containsMinFacsBelow arr below →
       ∀ (i : Nat) (h1: i < arr.size) (_: i < (below^2)) (_: 1 < i), arr[i] = i.minFac := by
    intro h i h1 h2 h3
    by_cases iPrime: i.Prime
    · symm; rw[Nat.Prime.minFac_eq iPrime]
      symm; apply containsMinFacsBelow_prime h iPrime
    · case neg =>
      unfold containsMinFacsBelow at h
      have h': i < arr.size ∧ 1 < i := by omega
      specialize h i h'
      unfold minFacBelow at h
      rw[h]
      have ip: 0 < i := by linarith
      have ib: i.minFac ^ 2 < below ^ 2 :=
      calc i.minFac ^ 2 ≤ i := Nat.minFac_sq_le_self ip iPrime
        _ < below ^ 2 := h2
      have imb: i.minFac < below := by apply lt_of_pow_lt_pow_left₀ 2; simp; assumption
      simp[imb]

lemma containsMinFacsBelow_prime_bSquared {arr: Array Nat} {below: Nat}
   (c: containsMinFacsBelow arr below) (i : Nat) (h1: i < arr.size) (h2: i < below ^2) (il: 1 < i):
       arr[i] = i ↔ i.Prime := by
  rw[Nat.prime_def_minFac]
  constructor
  · intro ie
    constructor; linarith
    nth_rw 2 [←ie]
    symm; apply containsMinFacsBelow_bSquared arr below; all_goals assumption
  · intro im
    nth_rw 2 [← im.2]
    apply containsMinFacsBelow_bSquared arr below; all_goals assumption

lemma containsMinFacsBelow_ge_iff (arr: Array Nat) (below: Nat) (as: arr.size ≤ below^2) :
    containsMinFacsBelow arr below ↔ ∀ (i : Nat) (h: i < arr.size ∧ 1 < i), arr[i] = i.minFac := by
    constructor
    · intro c i h
      apply containsMinFacsBelow_bSquared arr below
      assumption
      calc i < arr.size := h.1
        _ ≤ below^2 := as
      exact h.2
    · intro e i; specialize e i
      unfold minFacBelow
      by_cases ip: i.Prime
      · rw[Nat.Prime.minFac_eq ip] at e ⊢
        simpa
      · intro h; specialize e h
        have ib: i.minFac^2 < below^2
        calc i.minFac^2 ≤ i := by apply Nat.minFac_sq_le_self; linarith; exact ip
          _ < arr.size := h.1
          _ ≤ below ^ 2 := as
        have ib': i.minFac < below := by apply lt_of_pow_lt_pow_left₀ 2 _ ib; linarith
        simp[ib', e]

lemma values_calculateFactors (arr: Array Nat) (position: Nat)(posValid : 1 < position)
     (arrValid: containsMinFacsBelow arr position):
     containsMinFacsBelow (calculateFactors arr position) arr.size := by
    induction arr, position using calculateFactors.induct with
    | case1 arr position h =>
      rw [containsMinFacsBelow_ge_iff]
      unfold calculateFactors; simp[h]
      rw [containsMinFacsBelow_ge_iff] at arrValid
      assumption
      linarith
      simp
      rw[pow_two]
      exact Nat.le_mul_self arr.size
    | case2 arr position h1 h2 ih =>
      have positionPrime: position.Prime := by
        rw[← containsMinFacsBelow_prime_bSquared arrValid _ _ _ posValid]
        assumption
        apply lt_self_pow₀ posValid
        linarith
      unfold calculateFactors; simp[h1, h2] at ih arrValid ⊢
      unfold containsMinFacsBelow
      apply ih; linarith
      intro i iValid; simp at iValid
      rw[values_mapMultiples _ _ _ _ _ iValid.1]
      by_cases possq: i < position^2
      · apply containsMinFacsBelow_bSquared at arrValid -- TODO: this should be shorter.
        specialize arrValid i iValid.1 possq iValid.2
        have possq': ¬ position * position ≤ i := by linarith
        simp[possq']
        unfold minFacBelow
        split
        rw[arrValid]
        · case _ h =>
          by_cases iPrime: i.Prime
          · rw[arrValid]; exact Nat.Prime.minFac_eq iPrime
          · have ip: 0 < i := by linarith
            have cn: i.minFac^2 < position ^ 2
            calc i.minFac^2 ≤ i := Nat.minFac_sq_le_self ip iPrime
              _ < position ^ 2 := possq
            have cn': i.minFac < position := by apply lt_of_pow_lt_pow_left₀ 2 _ cn; linarith;
            linarith
      unfold containsMinFacsBelow at arrValid
      specialize arrValid i iValid
      by_cases minFacP: i.minFac = position
      · subst position
        have posdvd: i.minFac ∣ i - i.minFac^2 := by
          apply Nat.dvd_sub'
          apply Nat.minFac_dvd
          rw[pow_two]
          simp
        have posLeI: i.minFac ≤ i := by apply Nat.minFac_le; linarith
        rw[arrValid]
        unfold minFacBelow
        rw[←pow_two]
        have possq': i.minFac^2 ≤ i := by linarith
        simp[posLeI, posdvd, possq']
      · by_cases positionDvd: position ∣ i
        · have positionDvd': position ∣ i - position * position := by
            apply Nat.dvd_sub'; assumption; simp
          have posLeI: position * position ≤ i := by
            rw[←pow_two]
            linarith
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
          have minFacNonZero: i.minFac ≠ 0 := by linarith[Nat.minFac_pos i]
          simp[minFacNonZero]
          linarith
        · have positionDvd': position ≤ i -> ¬ position ∣ i - position := by
            intro p
            rw[← Nat.dvd_add_self_right]
            rwa[Nat.sub_add_cancel]; assumption
          have positionDvd'': ¬ (position * position ≤ i ∧ position ∣ i - position * position) := by
            rw[not_and]
            intro p
            have posdvd: position ∣ position * position := Nat.dvd_mul_right position position
            rw[← Nat.dvd_add_left posdvd]
            rw[Nat.sub_add_cancel p]
            assumption
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
        rw[← containsMinFacsBelow_prime_bSquared arrValid _ _ _ posValid]
        assumption
        apply lt_self_pow₀ posValid; linarith
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

#print axioms S_impl_implements_S

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
