import EthInapproximability.CurrentPaper.SourceClausePrefixGate
import EthInapproximability.CurrentPaper.SourceClauseClearExcept

/-!
The actual prefix OR-gate writer followed by a charged scratch clear. It
retains the row-query bank and reverse clause payload/output/count cells.
The separate prefix unit writer is not joined here.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding
open scoped Classical

abbrev Stack := SourceClauseRowGate.Stack 1
noncomputable instance : Fintype Stack := Fintype.ofFinite _

def rowCell (x : SourceCSPRowQueryFrame.Stack 1) : Stack := .inl (.inl x)
def savedCell : Stack := gateSavedKey
def outputCell : Stack :=
  SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.gateEmbedding
        (SourceClauseGateTwoAddress.embedding
          (SourceClauseGateMachine.embedding (.inr (.inl 1))))))
def countCell : Stack := gateCountKey

noncomputable def keep : Finset Stack :=
  (Finset.univ.image rowCell) ∪ {savedCell, outputCell, countCell}

noncomputable def clean (S : Stack → List Bool) : Stack → List Bool :=
  SourceClauseClearExcept.result keep S

noncomputable def clearCost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keep),
    (S (SourceClauseClearExcept.workBank keep i)).length) +
      SourceClauseClearExcept.workCount keep + 2

theorem clear_run (S : Stack → List Bool) :
    ((advance (SourceClauseClearExcept.program keep))^[clearCost S])
      (⟨some (.clear 0), ((), none), S⟩) =
      ⟨none, ((), none), clean S⟩ := by
  exact SourceClauseClearExcept.run keep S

theorem row_mem (x : SourceCSPRowQueryFrame.Stack 1) :
    rowCell x ∈ keep := by
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

theorem saved_mem : savedCell ∈ keep := by simp [keep]
theorem output_mem : outputCell ∈ keep := by simp [keep]
theorem count_mem : countCell ∈ keep := by simp [keep]

theorem final_row {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool)
    (x : SourceCSPRowQueryFrame.Stack 1) :
    clean (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (SourceBooleanEncoding.width 2 q + 1)
      true savedBits outputBits countBits) (rowCell x) =
      vertexFrame v x := by
  rw [clean, SourceClauseClearExcept.result, if_pos (row_mem x)]
  exact SourceClauseRowGate.final_row (0 : Fin 1) (vertexFrame v)
    v.val 2 s.val n s.val v.val (SourceBooleanEncoding.width 2 q + 1)
    true savedBits outputBits countBits (vertexFrame_query v) x

theorem final_saved {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) :
    clean (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (SourceBooleanEncoding.width 2 q + 1)
      true savedBits outputBits countBits) savedCell =
      (EncodedCNF.clauseFields (orGate
        (base n q (atLeastOrdinal v) + s.val)
        (SourceBooleanEncoding.positive (bitIndex v s)))).reverse ++
        savedBits := by
  rw [clean, SourceClauseClearExcept.result, if_pos saved_mem]
  exact atLeast_gate_saved v s savedBits outputBits countBits

theorem final_count {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) :
    clean (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (SourceBooleanEncoding.width 2 q + 1)
      true savedBits outputBits countBits) countCell =
      true :: true :: true :: countBits := by
  rw [clean, SourceClauseClearExcept.result, if_pos count_mem]
  exact atLeast_gate_count v s savedBits outputBits countBits

theorem final_output {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) :
    clean (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      true savedBits outputBits countBits) outputCell = outputBits := by
  rw [clean, SourceClauseClearExcept.result, if_pos output_mem]
  simp only [outputCell, SourceClauseRowGate.finalBank, bank_at,
    SourceClauseGateSlotAddress.final_output]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateClean
