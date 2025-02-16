def foldlWithIndex.{u, v} {α : Type u} {β : Type v} (f : β → Nat → α → β) (init : β)
    (arr : Array α) (start : Nat := 0) : β :=
  if h: start < arr.size then
    foldlWithIndex f (f init start arr[start]) arr (start + 1)
  else
    init
termination_by arr.size - start

lemma start_foldlWithIndex.{u, v} {α : Type u} {β : Type v} (f : β → Nat → α → β)
  (init : β) (pre suff : Array α) :
  foldlWithIndex f init (pre ++ suff) pre.size =
    foldlWithIndex (f · ∘ (· + pre.size)) init suff := by

      sorry



theorem concat_foldlWithIndex.{u, v} {α : Type u} {β : Type v} (f : β → Nat → α → β)
    (init : β) (pre suff : Array α) (start : Nat) :
  foldlWithIndex f init (pre ++ suff) start =
    foldlWithIndex (f · ∘ (· + pre.size))
                   (foldlWithIndex f init pre start)
                   suff (start - pre.size) := by
    induction init, pre, start using foldlWithIndex.induct with
    | f a b c => exact f a b c
    | case1 init arr start h ih =>
      nth_rw 1 [foldlWithIndex] -- unfold unfolds both https://leanprover-community.github.io/archive/stream/270676-lean4/topic/help.20with.20.60unfold.60.html
      simp[h]
      have sa : start - arr.size = 0 := by apply Nat.sub_eq_zero_of_le; linarith;
      have ss: start < arr.size + suff.size := by linarith
      have av: (arr ++ suff)[start]'(by simp; linarith) = arr[start] := by
        rw[Array.getElem_append]
        simp[h]
      simp[ss, av]
      nth_rw 3 [foldlWithIndex]
      by_cases suffEmpty: suff = #[]
      · simp[suffEmpty]
        nth_rw 2 [foldlWithIndex] -- unfold unfolds both https://leanprover-community.github.io/archive/stream/270676-lean4/topic/help.20with.20.60unfold.60.html
        simp[h]
      · have saa: (start + 1 - arr.size) = 0 := by apply Nat.sub_eq_zero_of_le; linarith
        simp[h, sa]
        simp[saa] at ih
        assumption
    | case2 init pre start h =>
      nth_rw 3 [foldlWithIndex]
      simp[h]
      induction pre.size with
      | zero => sorry
      | succ => sorry

      -- rcases pre with ⟨pre⟩
      -- induction pre with
      -- | nil => simp; rfl
      -- | cons a l ih =>
      --   simp at h ih ⊢
      --   have ll: l.length ≤ start := by linarith
      --   simp[ll] at ih

      --   unfold foldlWithIndex
      --   simp[h]
      --   -- specialize ih
      --   nth_rw 1 [foldlWithIndex]
      --   simp [h]
      --   sorry
