import CurrentAdditive.GaussWholeMatrixMachine
import CurrentAdditive.CylinderGaussABI

namespace CurrentAdditive.GaussWholeRationalInput
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open EthInapproximability.CurrentPaper

theorem outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (h01 : ∀i j,B i j=0 ∨ B i j=1) (hm : 0 < m) :
    GaussWholeMatrixMachine.machine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
      (GaussControlTrace.statePacket (GaussControlTrace.after B k))
      (GaussWholeMatrixMachine.clock (GaussPhysical.encodeTypedMatrix B).length) := by
  let A : Matrix (Fin m) (Fin k) ℤ:=fun i j => if B i j=0 then 0 else 1
  have ha : ∀i j,A i j=0 ∨ A i j=1:=by intro i j; by_cases h : B i j=0 <;> simp [A,h]
  have he : (fun i j => (A i j : ℚ))=B := by
    funext i j
    rcases h01 i j with hz | ho
    · simp [A,hz]
    · simp [A,ho]
  simpa only [he] using GaussWholeMatrixMachine.outputs A ha hm

theorem packet_length {m k : Nat} (B : Fin m → Fin k → ℚ)
    (h01 : ∀i j,B i j=0 ∨ B i j=1) (hm : 0 < m) :
    (GaussControlTrace.statePacket (GaussControlTrace.after B k)).length ≤
      (GaussPhysical.encodeTypedMatrix B).length+
        GaussWholeMatrixMachine.clock (GaussPhysical.encodeTypedMatrix B).length*
          GaussWholeMatrixMachine.machine.pushBound :=
  BitMachine.output_length_bound _ (outputs B h01 hm)

#print axioms outputs
#print axioms packet_length
end
end CurrentAdditive.GaussWholeRationalInput
