import EthInapproximability.CurrentPaper.WeightedRawWordsUnpack

/-! # Charged word operations on the global bank

Thin wrappers of production machines, all run on the global bank:
`MatrixStage4ScalarPreparationOps.copyProgram` (copy with the private blank
`cs`), `SourceClauseFixedUnary.program` (fixed unary pushes),
`MatrixStage4ScalarPreparationOps.multiplyProgram`, `unaryPowerProgram`, and
the S1 `clearProgram`. Also the bookkeeping lemmas for clearing a region
whose residue is only existentially known. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

/-- The consumer's raw word cell `j` (the admitted `scaleKey (raw j)`). -/
def rawCell (j : Fin 6) : Global :=
  cons (WeightedActualSizeSuffix.scaleKey (.inl (ETHScaleGlobalLog.raw j)))

/-! ## Copy -/

def slots3 (a b : Global) (h1 : a ≠ b) (h2 : a ≠ aux .cs) (h3 : b ≠ aux .cs) :
    Fin 3 ↪ Global where
  toFun
    | 0 => a
    | 1 => b
    | 2 => aux .cs
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def copyProg (a b : Global) (h1 : a ≠ b) (h2 : a ≠ aux .cs) (h3 : b ≠ aux .cs) :=
  MatrixStage4ScalarPreparationOps.copyProgram (slots3 a b h1 h2 h3)

theorem copy_word (a b : Global) (h1 : a ≠ b) (h2 : a ≠ aux .cs) (h3 : b ≠ aux .cs)
    (S : Global → List Bool) (hb : S b = []) (hcs : S (aux .cs) = []) :
    ((advance (copyProg a b h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Global => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (slots3 a b h1 h2 h3) S hcs
  have e0 : (slots3 a b h1 h2 h3) 0 = a := rfl
  have e1 : (slots3 a b h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

/-! ## Fixed unary push onto a possibly nonempty cell -/

theorem push_unary (target : Global) (S : Global → List Bool) (N : ℕ) :
    ((advance (SourceClauseFixedUnary.program target N))^[N + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label N), (), S⟩ :
        TM2.Cfg (fun _ : Global => Bool) (SourceClauseFixedUnary.Label N) Unit) =
      ⟨none, (), Function.update S target (List.replicate N true ++ S target)⟩ := by
  have h := SourceClauseFixedUnary.run_from target S (0 : SourceClauseFixedUnary.Label N)
    N (by simp) (S target)
  have hs : SourceClauseFixedUnary.state target S (0 : SourceClauseFixedUnary.Label N)
      (S target) = ⟨some 0, (), S⟩ := by
    simp [SourceClauseFixedUnary.state]
  rw [hs] at h
  exact h

/-! ## Clearing -/

theorem cleared_update_comm {n : ℕ} (cells : Fin n → Global) (S : Global → List Bool)
    (a : Global) (u : List Bool) (ha : ∀ i, cells i ≠ a) :
    BitMachineClearBank.cleared cells (Function.update S a u) =
      Function.update (BitMachineClearBank.cleared cells S) a u := by
  funext j
  by_cases hj : j = a
  · subst hj
    have : ¬ ∃ i, cells i = j := fun ⟨i, hi⟩ => ha i hi
    simp [BitMachineClearBank.cleared, this]
  · simp [BitMachineClearBank.cleared, hj]

/-- Clearing every private region cell after an embedded run whose only
non-region cells are preserved gives back the old bank. -/
theorem cleared_bank_eq {K : Type*} [DecidableEq K] {n : ℕ} (cells : Fin n → Global)
    (ι : K ↪ Global) (G : Global → List Bool) (F : K → List Bool)
    (hG : ∀ i, G (cells i) = [])
    (hin : ∀ k, (∃ i, cells i = ι k) ∨ F k = G (ι k)) :
    BitMachineClearBank.cleared cells (bank ι G F) = G := by
  funext j
  unfold BitMachineClearBank.cleared
  by_cases hc : ∃ i, cells i = j
  · rw [if_pos hc]
    obtain ⟨i, rfl⟩ := hc
    exact (hG i).symm
  · rw [if_neg hc]
    by_cases hr : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := hr
      rw [bank_at]
      rcases hin k with h | h
      · exact (hc h).elim
      · exact h
    · exact bank_outside ι G F j hr

theorem sum_le_mul {n : ℕ} (f : Fin n → ℕ) (B : ℕ) (h : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ n * B := by
  have := Finset.sum_le_card_nsmul Finset.univ f B (fun i _ => h i)
  simpa using this

end
end EthInapproximability.CurrentPaper.WeightedRawWords
