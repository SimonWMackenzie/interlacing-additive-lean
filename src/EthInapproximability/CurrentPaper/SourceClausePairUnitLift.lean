import EthInapproximability.CurrentPaper.SourceClausePairSourceSchedule
import EthInapproximability.CurrentPaper.SourceClausePrefixUnitCycle

/-!
Separate the pair source's vertex index from its clause ordinal on one
physical bank. The existing at-least shared core aliases these two indices;
this disjoint ordinal cell permits its signed unit routine to be reused for
pair slots without changing the vertex's query cell.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairUnitLift

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack := PrefixSharedCore.Stack ⊕ Unit

def ordinalCell : PrefixSharedCore.Stack := .inl 1

noncomputable def unitEmbedding : PrefixSharedCore.Stack ↪ Stack where
  toFun x := if x = ordinalCell then .inr () else .inl x
  inj' := by
    intro x y h
    by_cases hx : x = ordinalCell
    · by_cases hy : y = ordinalCell
      · exact hx.trans hy.symm
      · simp [hx, hy] at h
    · by_cases hy : y = ordinalCell
      · simp [hx, hy] at h
      · simpa [hx, hy] using h

def vertexCell : Stack := .inl ordinalCell
def pairOrdinalCell : Stack := .inr ()

theorem ordinal_routed : unitEmbedding ordinalCell = pairOrdinalCell := by
  simp [unitEmbedding, pairOrdinalCell]

theorem vertex_not_unit_range :
    ¬ ∃ x : PrefixSharedCore.Stack, unitEmbedding x = vertexCell := by
  rintro ⟨x, hx⟩
  by_cases h : x = ordinalCell
  · simp [unitEmbedding, h, vertexCell] at hx
  · have he : x = ordinalCell := by
      simp [unitEmbedding, h, vertexCell] at hx
    exact h he

noncomputable def pairBank (n vertex ordinal : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  bank unitEmbedding
    (fun x => if x = vertexCell then List.replicate vertex true else [])
    (PrefixGateReady.blank n ordinal saved output count)

theorem vertex_word (n vertex ordinal : Nat)
    (saved output count : List Bool) :
    pairBank n vertex ordinal saved output count vertexCell =
      List.replicate vertex true := by
  rw [pairBank, bank_outside _ _ _ _ vertex_not_unit_range]
  simp

theorem ordinal_word (n vertex ordinal : Nat)
    (saved output count : List Bool) :
    pairBank n vertex ordinal saved output count pairOrdinalCell =
      List.replicate ordinal true := by
  rw [← ordinal_routed, pairBank, bank_at]
  rfl

noncomputable def unitProgram (w ell : Nat) (sign : Bool) :=
  fun l => stackStmt unitEmbedding (PrefixUnitCycle.program w ell sign l)

theorem unit_run (n vertex ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ (SourceClauseFixedBatch.costPrefix
          (PrefixUnitClean.constantSize w ell) 3 + 1) +
        PrefixUnitRun.cost n ordinal w ell + 1 +
        PrefixSharedClear.cost
          (bank PrefixSharedCore.unitEmbedding
            (PrefixGateReady.blank n ordinal saved output count)
            (PrefixUnitRun.finished n ordinal w ell sign
              saved output count)) + 1,
      ((advance (unitProgram w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixUnitClean.constantSize w ell) 0))),
          (((), PrefixUnitRun.startControl), ((), none)),
          pairBank n vertex ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((), PrefixUnitRun.startControl), ((), none)),
          pairBank n vertex ordinal
            (PrefixSharedUnitHandoff.nextSaved n ordinal w ell sign saved)
            output (true :: count)⟩ := by
  obtain ⟨t, ht, hrun⟩ := PrefixUnitCycle.run n ordinal w ell sign
    saved output count
  have h := BitMachineStackRun.run unitEmbedding
    (fun x => if x = vertexCell then List.replicate vertex true else [])
    (PrefixUnitCycle.program w ell sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize w ell) 0))),
      (((), PrefixUnitRun.startControl), ((), none)),
      PrefixGateReady.blank n ordinal saved output count⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) _ _) t
  rw [hrun] at h
  exact ⟨t, ht, by simpa [unitProgram, pairBank] using h⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairUnitLift
