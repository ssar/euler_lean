def f (n:Nat) : Nat :=
  if (n = 0) then
    1
  else if (2 ∣ n) then
    f (n / 2)
  else
    f (n - 1)
termination_by n

theorem f_eq_1 (n:Nat): f n = 1 := by
  unfold f
  induction n using f.induct with
  | case1 => simp only [↓reduceIte];
  | case2 n h2 h3 ih =>
      simp only [↓reduceIte, *];
      unfold f;
      assumption
  | case3 n h2 h3 ih =>
      simp only [↓reduceIte, *];
      unfold f;
      assumption
      -- split at ih
      -- · case isTrue => simp only [↓reduceIte, *]
      -- · case isFalse => simp only [↓reduceIte, *]


def g (n:Nat) : Nat :=
  if (n = 0) then
    1
  else if (2 ∣ n) then
    1
  else
    1

theorem g_eq_1 (n:Nat): g n = 1 := by
  unfold g
  split
  case isTrue h => rfl
  case isFalse h => refl
