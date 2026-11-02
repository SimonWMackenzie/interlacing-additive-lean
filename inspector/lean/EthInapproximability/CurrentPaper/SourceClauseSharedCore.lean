import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Heterogeneous physical banks sharing one writer core

The row OR-gate and unit-clause writers have different finite scratch banks.
Both can nevertheless point at the same parsed row and the same three writer
cells. This construction embeds each local bank into one physical master bank,
identifying only cells explicitly named by an injective core map. Neither
local writer is granted the other's scratch state.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseSharedCore

open scoped Classical

variable {C K L : Type*}

abbrev LeftScratch (κ : C ↪ K) := {x : K // x ∉ Set.range κ}
abbrev RightScratch (mu : C ↪ L) := {x : L // x ∉ Set.range mu}
abbrev Stack (κ : C ↪ K) (mu : C ↪ L) :=
  C ⊕ (LeftScratch κ ⊕ RightScratch mu)

noncomputable def left (κ : C ↪ K) (mu : C ↪ L) : K ↪ Stack κ mu where
  toFun x := if h : x ∈ Set.range κ then
      .inl (Classical.choose h)
    else .inr (.inl ⟨x, h⟩)
  inj' := by
    intro x y h
    by_cases hx : x ∈ Set.range κ
    · by_cases hy : y ∈ Set.range κ
      · have he : Classical.choose hx = Classical.choose hy := by
          simpa [hx, hy] using h
        have hxx : κ (Classical.choose hx) = x := Classical.choose_spec hx
        have hyy : κ (Classical.choose hy) = y := Classical.choose_spec hy
        calc x = κ (Classical.choose hx) := hxx.symm
          _ = κ (Classical.choose hy) := congrArg κ he
          _ = y := hyy
      · simp [hx, hy] at h
    · by_cases hy : y ∈ Set.range κ
      · simp [hx, hy] at h
      · simpa [hx, hy] using h

noncomputable def right (κ : C ↪ K) (mu : C ↪ L) : L ↪ Stack κ mu where
  toFun x := if h : x ∈ Set.range mu then
      .inl (Classical.choose h)
    else .inr (.inr ⟨x, h⟩)
  inj' := by
    intro x y h
    by_cases hx : x ∈ Set.range mu
    · by_cases hy : y ∈ Set.range mu
      · have he : Classical.choose hx = Classical.choose hy := by
          simpa [hx, hy] using h
        have hxx : mu (Classical.choose hx) = x := Classical.choose_spec hx
        have hyy : mu (Classical.choose hy) = y := Classical.choose_spec hy
        calc x = mu (Classical.choose hx) := hxx.symm
          _ = mu (Classical.choose hy) := congrArg mu he
          _ = y := hyy
      · simp [hx, hy] at h
    · by_cases hy : y ∈ Set.range mu
      · simp [hx, hy] at h
      · simpa [hx, hy] using h

theorem left_core (κ : C ↪ K) (mu : C ↪ L) (c : C) :
    left κ mu (κ c) = .inl c := by
  have h : κ c ∈ Set.range κ := ⟨c, rfl⟩
  have hc : Classical.choose h = c :=
    κ.injective (Classical.choose_spec h)
  simp [left, h, hc]

theorem right_core (κ : C ↪ K) (mu : C ↪ L) (c : C) :
    right κ mu (mu c) = .inl c := by
  have h : mu c ∈ Set.range mu := ⟨c, rfl⟩
  have hc : Classical.choose h = c :=
    mu.injective (Classical.choose_spec h)
  simp [right, h, hc]

theorem left_outside (κ : C ↪ K) (mu : C ↪ L)
    (x : K) (hx : x ∉ Set.range κ) :
    left κ mu x = .inr (.inl ⟨x, hx⟩) := by
  change (if h : x ∈ Set.range κ then
      (Sum.inl (Classical.choose h) : Stack κ mu)
    else .inr (.inl ⟨x, h⟩)) = _
  rw [dif_neg hx]

theorem right_outside (κ : C ↪ K) (mu : C ↪ L)
    (x : L) (hx : x ∉ Set.range mu) :
    right κ mu x = .inr (.inr ⟨x, hx⟩) := by
  change (if h : x ∈ Set.range mu then
      (Sum.inl (Classical.choose h) : Stack κ mu)
    else .inr (.inr ⟨x, h⟩)) = _
  rw [dif_neg hx]

theorem shared (κ : C ↪ K) (mu : C ↪ L) (c : C) :
    left κ mu (κ c) = right κ mu (mu c) := by
  rw [left_core, right_core]

theorem left_bank_right_core (κ : C ↪ K) (mu : C ↪ L)
    [DecidableEq K] [DecidableEq (Stack κ mu)]
    (foreign : Stack κ mu → List Bool) (S : K → List Bool) (c : C) :
    BitMachineStackEmbedding.bank (left κ mu) foreign S (right κ mu (mu c)) =
      S (κ c) := by
  rw [← shared, BitMachineStackEmbedding.bank_at]

theorem right_bank_left_core (κ : C ↪ K) (mu : C ↪ L)
    [DecidableEq L] [DecidableEq (Stack κ mu)]
    (foreign : Stack κ mu → List Bool) (S : L → List Bool) (c : C) :
    BitMachineStackEmbedding.bank (right κ mu) foreign S (left κ mu (κ c)) =
      S (mu c) := by
  rw [shared, BitMachineStackEmbedding.bank_at]

end EthInapproximability.CurrentPaper.SourceClauseSharedCore
