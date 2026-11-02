import EthInapproximability.CurrentPaper.SourceClauseBooleanPrefix
import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
An actual unary computation of the pair-clause ordinal from the supplied
vertex count and vertex index. The two alphabet indices are fixed finite
control parameters. This is an ordinal preparer, not yet the pair callback.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix

open Turing BitMachineEncoding

def pairOffset (s t : Fin 2) : ℕ := 2 * s.val + t.val

def pairSizes (s t : Fin 2) : Fin 1 → ℕ := fun _ => pairOffset s t

def pairTarget : Fin 1 → Fin 6 := fun _ => 5

def ordinalInitial (n v : ℕ) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg (some .outer) false
    (List.replicate v true) (List.replicate 4 true)
    (List.replicate n true) [] [] []).stk

def ordinalIntermediate (n v : ℕ) : Fin 6 → List Bool :=
  (MatrixAddressMachine.cfg none false
    (List.replicate v true) (List.replicate 4 true)
    (List.replicate n true) [] []
    (List.replicate (v * 4 + n) true)).stk

def ordinalFinal (n v : ℕ) (s t : Fin 2) : Fin 6 → List Bool :=
  SourceClauseFixedBatch.bankPrefix pairTarget (pairSizes s t)
    (ordinalIntermediate n v) 1

def ordinalProgram (s t : Fin 2) :=
  BitMachineRawSequence.program MatrixAddressMachine.program
    (SourceClauseFixedBatch.program pairTarget (pairSizes s t))
    (SourceClauseFixedBatch.labelAt (pairSizes s t) 0) false ()

theorem ordinalIntermediate_run (n v : ℕ) :
    ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime v 4 n])
      (⟨some MatrixAddressMachine.Label.outer, false, ordinalInitial n v⟩ :
        MatrixAddressMachine.Config) =
      ⟨none, false, ordinalIntermediate n v⟩ := by
  simpa [MatrixAddressMachine.run, ordinalInitial, ordinalIntermediate] using
    MatrixAddressMachine.address_run v 4 n false []

theorem ordinalFinal_run (n v : ℕ) (s t : Fin 2) :
    ((advance (SourceClauseFixedBatch.program pairTarget (pairSizes s t)))^[
      SourceClauseFixedBatch.costPrefix (pairSizes s t) 1 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt (pairSizes s t) 0), (),
        ordinalIntermediate n v⟩) =
      ⟨none, (), ordinalFinal n v s t⟩ := by
  exact SourceClauseFixedBatch.run pairTarget (pairSizes s t)
    (ordinalIntermediate n v)

theorem ordinal_run (n v : ℕ) (s t : Fin 2) :
    ∃ T ≤ MatrixAddressMachine.exactTime v 4 n +
      SourceClauseFixedBatch.costPrefix (pairSizes s t) 1 + 2,
      ((advance (ordinalProgram s t))^[T])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, ()), ordinalInitial n v⟩) =
        ⟨none, (false, ()), ordinalFinal n v s t⟩ := by
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    MatrixAddressMachine.program
    (SourceClauseFixedBatch.program pairTarget (pairSizes s t))
    MatrixAddressMachine.Label.outer
    (SourceClauseFixedBatch.labelAt (pairSizes s t) 0)
    false false () ()
    (ordinalInitial n v) (ordinalIntermediate n v) (ordinalFinal n v s t)
    (MatrixAddressMachine.exactTime v 4 n)
    (SourceClauseFixedBatch.costPrefix (pairSizes s t) 1 + 1)
    (ordinalIntermediate_run n v) (ordinalFinal_run n v s t)
  exact ⟨T, by omega, hr⟩

theorem ordinalFinal_value (n v : ℕ) (s t : Fin 2) :
    ordinalFinal n v s t 5 =
      List.replicate (n + 4 * v + 2 * s.val + t.val) true := by
  simp [ordinalFinal, SourceClauseFixedBatch.bankPrefix,
    SourceClauseFixedBatch.prepend, pairTarget, pairSizes,
    pairOffset, ordinalIntermediate, MatrixAddressMachine.cfg,
    List.replicate_append_replicate]
  ring

theorem ordinalFinal_source {n : ℕ} (v : Fin n) (s t : Fin 2) :
    ordinalFinal n v.val s t 5 =
      List.replicate (pairOrdinal v s t) true := by
  rw [ordinalFinal_value]
  simp [pairOrdinal]

theorem ordinal_charge (s t : Fin 2) :
    SourceClauseFixedBatch.costPrefix (pairSizes s t) 1 =
      pairOffset s t + 1 := by
  simp [SourceClauseFixedBatch.costPrefix, pairSizes, pairOffset]

theorem ordinal_run_explicit {n : ℕ} (v : Fin n) (s t : Fin 2) :
    ∃ T ≤ MatrixAddressMachine.exactTime v.val 4 n + pairOffset s t + 3,
      ((advance (ordinalProgram s t))^[T])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, ()), ordinalInitial n v.val⟩) =
        ⟨none, (false, ()), ordinalFinal n v.val s t⟩ ∧
      ordinalFinal n v.val s t 5 =
        List.replicate (pairOrdinal v s t) true := by
  obtain ⟨T, hT, hr⟩ := ordinal_run n v.val s t
  refine ⟨T, ?_, hr, ordinalFinal_source v s t⟩
  rw [ordinal_charge] at hT
  omega

end EthInapproximability.CurrentPaper.SourceBooleanPrefix
