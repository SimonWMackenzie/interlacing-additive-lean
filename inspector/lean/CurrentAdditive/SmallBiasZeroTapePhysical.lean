import CurrentAdditive.SmallBiasDetTapeAdapter

/-!
# A zero-tape selected algorithm is a deterministic polynomial machine

The selected-pair carrier only certifies runs on `pair input []`. The
existing field writer turns any raw input into exactly that pair, and
ordinary finite-machine composition supplies a global polynomial clock.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

theorem zeroTapeOutputPolytime (A : Paper2.SelectedTape.Algorithm)
    (hz : ∀ x, A.tapeLength x = 0) :
    BitMachine.Polytime (fun x => A.output x []) := by
  refine ⟨BitMachineComposition.composition SourceFieldWriter.fieldMachine A.machine,
    8 + A.cT, A.dT + 1, ?_⟩
  intro x
  have hcR : A.cR = 0 := by
    have h := hz []
    simpa [Paper2.SelectedTape.Algorithm.tapeLength] using h
  have hr := A.runs x (fun _ => false)
  have hpair : pair x [] = field x := by simp [pair]
  have hrun : A.machine.OutputsWithin (field x) (A.output x [])
      (A.cT * (x.length + 1) ^ A.dT) := by
    convert hr using 1 <;> simp [hcR, pair]
  have hc := BitMachineComposition.composition_outputsWithin
    SourceFieldWriter.fieldMachine A.machine
    (SourceFieldWriter.field_outputs x) hrun
  have hlen : (field x).length = 2 * x.length + 1 := field_length x
  rw [hlen] at hc
  have hN : 1 ≤ x.length + 1 := by omega
  have hpow : 1 ≤ (x.length + 1) ^ A.dT := Nat.one_le_pow _ _ hN
  have hlinear : x.length + 1 ≤ (x.length + 1) ^ (A.dT + 1) := by
    rw [pow_succ]
    nlinarith
  have hpower : (x.length + 1) ^ A.dT ≤ (x.length + 1) ^ (A.dT + 1) := by
    rw [pow_succ]
    nlinarith
  apply BitMachine.outputsWithin_mono _ hc
  have h1 := Nat.mul_le_mul_left 8 hlinear
  have h2 := Nat.mul_le_mul_left A.cT hpower
  nlinarith

#print axioms CurrentAdditive.SmallBias.zeroTapeOutputPolytime

end CurrentAdditive.SmallBias
