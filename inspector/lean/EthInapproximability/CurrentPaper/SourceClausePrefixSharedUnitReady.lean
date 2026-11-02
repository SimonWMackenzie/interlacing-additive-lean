import EthInapproximability.CurrentPaper.SourceClausePrefixSharedGate

/-! Exact common-bank projection required before each prefix unit routine. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedUnitReady

open scoped Classical

theorem keep_iff (x : PrefixUnitRun.Stack) :
    x ∈ PrefixUnitClean.keep ↔
      x ∈ Set.range PrefixSharedCore.unitCore := by
  constructor
  · intro hx
    simp only [PrefixUnitClean.keep, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
    · exact ⟨4, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [PrefixSharedCore.unitCore,
      PrefixSharedCore.unitCoreCell, PrefixUnitClean.keep]

theorem blank_ready (n v : ℕ) (saved output count : List Bool) :
    ∀ x : PrefixUnitRun.Stack,
      PrefixGateReady.blank n v saved output count
        (PrefixSharedCore.unitEmbedding x) =
      PrefixUnitClean.blank n v saved output count x := by
  intro x
  by_cases hx : x ∈ Set.range PrefixSharedCore.unitCore
  · obtain ⟨i, rfl⟩ := hx
    rw [PrefixSharedCore.unitEmbedding,
      SourceClauseSharedCore.right_core]
    fin_cases i
    · exact (PrefixUnitClean.blank_vertexCount n v saved output count).symm
    · exact (PrefixUnitClean.blank_ordinal n v saved output count).symm
    · exact (PrefixUnitClean.blank_saved n v saved output count).symm
    · exact (PrefixUnitClean.blank_output n v saved output count).symm
    · exact (PrefixUnitClean.blank_count n v saved output count).symm
  · rw [PrefixSharedCore.unitEmbedding,
      SourceClauseSharedCore.right_outside _ _ x hx]
    have hk : x ∉ PrefixUnitClean.keep :=
      fun h => hx ((keep_iff x).mp h)
    simp [PrefixGateReady.blank, PrefixUnitClean.blank,
      PrefixUnitClean.clean, SourceClauseClearExcept.result, hk]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedUnitReady
