import CurrentAdditive.CodeDUpdatedEntryList
import CurrentAdditive.CodeDCompactClockV2
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
Physical ordered entry replacement followed by physical zero deletion. The
input is a V2 list of old-entry/new-weight pairs. An upstream arithmetic
controller must still produce those pairs from lambda and the Gauss vector.
-/

namespace CurrentAdditive.CodeDUpdatedCompactPipeline

open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    CodeDUpdatedEntryList.machine CodeDCompactJoinV2.machine

noncomputable def clock {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) : Nat :=
  let pairs := CodeDUpdatedEntryList.pairItems source updated
  let entries := (CodeDCompactSequentialBridge.updatedEntries source updated).map
    encodeEntry
  CodeDUpdatedEntryList.clock pairs +
    2*(CodeDCodecV2.encodeItems entries).length+2 +
    CodeDCompactJoinV2.clock entries

theorem outputs {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (hupdated : updated.all (fun w => decide (0 ≤ w)) = true) :
    machine.OutputsWithin
      (CodeDCodecV2.encodeItems (CodeDUpdatedEntryList.pairItems source updated))
      (encodedSource (CodeDCompactSequentialBridge.retainedSource source updated))
      (clock source updated) := by
  let entries := (CodeDCompactSequentialBridge.updatedEntries source updated).map
    encodeEntry
  have h₁ := CodeDUpdatedEntryList.writes_compactor_input source updated
  have h₂ := CodeDCompactJoinV2.outputs entries
  rw [CodeDCompactSequentialBridge.compact_updated_bytes source updated hupdated] at h₂
  have h := BitMachineComposition.composition_outputsWithin
    CodeDUpdatedEntryList.machine CodeDCompactJoinV2.machine h₁ h₂
  simpa only [machine, clock, entries] using h

theorem materialized_success {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : SequentialSourceCode.compressSourceOnceMaterialized n φ source = some out) :
    ∃ updated : Array ℚ,
      machine.OutputsWithin
        (CodeDCodecV2.encodeItems (CodeDUpdatedEntryList.pairItems source updated))
        (encodedSource out) (clock source updated) := by
  obtain ⟨updated, hnonneg, hout⟩ :=
    CodeDCompactSequentialBridge.materialized_success_updated φ source out h
  exact ⟨updated, hout ▸ outputs source updated hnonneg⟩

#print axioms outputs
#print axioms materialized_success

end CurrentAdditive.CodeDUpdatedCompactPipeline
