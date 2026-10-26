import EthInapproximability.CurrentPaper.SourceClausePrefixGateReady

/-! Source-faithful fixed-alphabet replacement for the two hard-coded `2`
operand words in the binary prefix gate preparer. The dynamic vertex word is
copied by the existing source-preserving physical broadcast. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateOperands

open Turing BitMachineEncoding
open scoped Classical
noncomputable section

abbrev Stack := SourceBooleanPrefix.PrefixSharedCore.Stack
open SourceBooleanPrefix

def constantSize (a s w : Nat) : Fin 5 → Nat
  | 0 => a
  | 1 => s
  | 2 => a
  | 3 => s
  | 4 => w

def fixed (a s w : Nat) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClauseFixedBatch.bankPrefix PrefixGateOperands.constantTarget
    (constantSize a s w) S 5

def prepared (a s w : Nat) (bits : List Bool)
    (S : Stack → List Bool) : Stack → List Bool :=
  PrefixGateOperands.copied bits (fixed a s w S)

def program (a s w : Nat) :=
  BitMachineRawSequence.program
    (SourceClauseFixedBatch.program PrefixGateOperands.constantTarget
      (constantSize a s w))
    (SourceClausePreservingBroadcast.program
      PrefixGateOperands.vertex PrefixGateOperands.temp
      PrefixGateOperands.vertexTargets)
    SourceClausePreservingBroadcast.Label.scan () ((), none)

def cost (a s w : Nat) (bits : List Bool) : Nat :=
  SourceClauseFixedBatch.costPrefix (constantSize a s w) 5 + 1 +
    (2 * bits.length + 3) + 1

theorem fixed_run (a s w : Nat) (S : Stack → List Bool) :
    ((advance (SourceClauseFixedBatch.program
      PrefixGateOperands.constantTarget (constantSize a s w)))^[
        SourceClauseFixedBatch.costPrefix (constantSize a s w) 5 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt (constantSize a s w) 0),(),S⟩) =
      ⟨none,(),fixed a s w S⟩ := by
  exact SourceClauseFixedBatch.run PrefixGateOperands.constantTarget
    (constantSize a s w) S

theorem fixed_vertex (a s w : Nat) (S : Stack → List Bool) :
    fixed a s w S PrefixGateOperands.vertex =
      S PrefixGateOperands.vertex := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [PrefixGateOperands.constantTarget_eq]
  exact Ne.symm (PrefixGateOperands.source_ne _
    (PrefixGateOperands.constant_not_core i))

theorem fixed_temp (a s w : Nat) (S : Stack → List Bool) :
    fixed a s w S PrefixGateOperands.temp = S PrefixGateOperands.temp := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [PrefixGateOperands.constantTarget_eq]
  intro h
  have hh := PrefixSharedCore.gateEmbedding.injective h.symm
  fin_cases i <;>
    simp [PrefixGateOperands.constantLocal,SourceClauseRowGate.temp,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding] at hh

theorem run (a s w : Nat) (bits : List Bool)
    (S : Stack → List Bool)
    (hvertex : S PrefixGateOperands.vertex = bits)
    (htemp : S PrefixGateOperands.temp = []) :
    ∃ T ≤ cost a s w bits,
      ((advance (program a s w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt (constantSize a s w) 0)),
          ((),((),none)),S⟩) =
        ⟨none,((),((),none)),prepared a s w bits S⟩ := by
  have hf := fixed_run a s w S
  have hc := PrefixGateOperands.vertex_copy_run bits (fixed a s w S)
    (by rw [fixed_vertex,hvertex])
    (by rw [fixed_temp,htemp])
  obtain ⟨T,hT,hr⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedBatch.program PrefixGateOperands.constantTarget
      (constantSize a s w))
    (SourceClausePreservingBroadcast.program
      PrefixGateOperands.vertex PrefixGateOperands.temp
      PrefixGateOperands.vertexTargets)
    (SourceClauseFixedBatch.labelAt (constantSize a s w) 0)
    SourceClausePreservingBroadcast.Label.scan
    () () ((),none) ((),none)
    S (fixed a s w S) (prepared a s w bits S)
    (SourceClauseFixedBatch.costPrefix (constantSize a s w) 5 + 1)
    (2 * bits.length + 3) hf hc
  exact ⟨T,by dsimp [cost]; omega,by simpa only [program,prepared] using hr⟩

#print axioms run

end
end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateOperands
