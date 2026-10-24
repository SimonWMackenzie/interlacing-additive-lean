import EthInapproximability.CurrentPaper.SourceClauseClearExcept
import EthInapproximability.CurrentPaper.SourceClauseRowIndexedGate

/-!
# A reusable row-gate scratch reset

The checked row frame and the three persistent writer cells—reverse payload,
unary clause count, and output suffix—are retained. Every other stack in the
one-gate composite bank is physically emptied by the generic finite-bank
clearer. The next literal call must still reload its unary operands and
connect its initial bank; this theorem alone is not the tuple iterator.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowGateCleanup

open Turing BitMachineEncoding

noncomputable abbrev Stack (q : ℕ) := SourceClauseRowIndexedGate.Stack q

def rowCell {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) : Stack q :=
  SourceClauseRowIndexedGate.gateEmbedding (.inl (.inl x))

def savedCell {q : ℕ} : Stack q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inl 0)))))))

def outputCell {q : ℕ} : Stack q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inl 1)))))))

def countCell {q : ℕ} : Stack q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding
          (SourceClauseGateTwoAddress.embedding
            (SourceClauseGateMachine.embedding (.inr (.inr ())))))))

noncomputable def keep (q : ℕ) : Finset (Stack q) :=
  (Finset.univ.image (rowCell (q := q))) ∪
    {savedCell, outputCell, countCell}

theorem row_mem {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) :
    rowCell x ∈ keep q := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem saved_mem {q : ℕ} : savedCell (q := q) ∈ keep q := by
  simp [keep]

theorem output_mem {q : ℕ} : outputCell (q := q) ∈ keep q := by
  simp [keep]

theorem count_mem {q : ℕ} : countCell (q := q) ∈ keep q := by
  simp [keep]

noncomputable def clean {q : ℕ} (S : Stack q → List Bool) :
    Stack q → List Bool := SourceClauseClearExcept.result (keep q) S

theorem row_preserved {q : ℕ} (S : Stack q → List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    clean S (rowCell x) = S (rowCell x) :=
  SourceClauseClearExcept.retained (keep q) S _ (row_mem x)

theorem saved_preserved {q : ℕ} (S : Stack q → List Bool) :
    clean S savedCell = S savedCell :=
  SourceClauseClearExcept.retained (keep q) S _ saved_mem

theorem output_preserved {q : ℕ} (S : Stack q → List Bool) :
    clean S outputCell = S outputCell :=
  SourceClauseClearExcept.retained (keep q) S _ output_mem

theorem count_preserved {q : ℕ} (S : Stack q → List Bool) :
    clean S countCell = S countCell :=
  SourceClauseClearExcept.retained (keep q) S _ count_mem

theorem scratch_empty {q : ℕ} (S : Stack q → List Bool)
    (x : Stack q) (hx : x ∉ keep q) : clean S x = [] :=
  SourceClauseClearExcept.emptied (keep q) S x hx

theorem run {q : ℕ} (S : Stack q → List Bool) :
    ((advance (SourceClauseClearExcept.program (keep q)))^[
      (∑ i : Fin (SourceClauseClearExcept.workCount (keep q)),
        (S (SourceClauseClearExcept.workBank (keep q) i)).length) +
        SourceClauseClearExcept.workCount (keep q) + 2])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount (keep q)))
          (Unit × Option Bool)) =
      ⟨none, ((), none), clean S⟩ :=
  SourceClauseClearExcept.run (keep q) S

end EthInapproximability.CurrentPaper.SourceClauseRowGateCleanup
