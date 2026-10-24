import CurrentAdditive.GaussPostloopSerialized
import CurrentAdditive.GaussActualWorkListClock
import CurrentAdditive.GaussCellPolynomialClock
import CurrentAdditive.GaussInitialByteDimensions

namespace CurrentAdditive.GaussPostloopClock
noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open GaussCellPolynomialClock

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
attribute [local irreducible] PolynomialBound GaussCoefficientProgram.machine
  GaussCoefficientProgram.polynomialCoefficient UnaryBinaryEncoding.coefficient

def itemBytes (n : Nat) : Nat := 6*n+3
def coefficientTime (n : Nat) : Nat := GaussCoefficientProgram.polynomialCoefficient*(itemBytes n+1)^GaussCoefficientProgram.polynomialExponent
def coefficientBytes (n : Nat) : Nat := itemBytes n+coefficientTime n*GaussCoefficientProgram.machine.pushBound
def framedTime (n : Nat) : Nat := coefficientTime n+2*coefficientBytes n+2+
  (UnaryBinaryEncoding.coefficient+7)*(coefficientBytes n+1)^2
def framedBytes (n : Nat) : Nat := 3*coefficientBytes n+1
def itemCost (n : Nat) : Nat :=
  let M:=GaussVectorOuterWriter.framedMachine GaussCoefficientProgram.machine
  20*(itemBytes n+1)*(itemBytes n+1)+framedTime n+4*itemBytes n+framedBytes n+
    M.stackCount*(itemBytes n+framedTime n*M.pushBound+1)+9
def vectorCap (n : Nat) : Nat := n*(itemCost n+4*n+7+framedBytes n)+11*n+17
def workBytes (n : Nat) : Nat := 3*n*(itemBytes n+1)+1
def workCap (n : Nat) : Nat := GaussActualWorkListClock.clock n n
def bodyCap (n : Nat) : Nat := workCap n+
  MachineInvokeFull.uniformBound GaussWideVectorInvoke.VectorMachine
    (List.replicate (workBytes n) true) (vectorCap n)+1
def clock (n : Nat) : Nat := 5*(n+1)+bodyCap n+1

theorem vectorClock_le {m k : Nat} (B : Fin m → Fin k → ℚ) (f : Fin k)
    (n : Nat) (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ n) (hk : k ≤ n) :
    GaussAnyWidthVector.vectorClock B f ≤ vectorCap n := by
  let xs:=GaussCertificateWorkList.workPackets B f
  let F:=GaussCoefficientProgram.result
  let bound:=GaussCoefficientOuterJoin.itemClock
  let M:=GaussVectorOuterWriter.framedMachine GaussCoefficientProgram.machine
  have hin : ∀ x∈xs,x.length ≤ itemBytes n := by
    intro x hx
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hx
    have h:=GaussCertificateWorkList.workPacket_length_le B f j
    unfold itemBytes
    omega
  have htime : ∀ x∈xs,bound x ≤ coefficientTime n := by
    intro x hx
    have hi:=hin x hx
    unfold bound GaussCoefficientOuterJoin.itemClock coefficientTime
    gcongr
  have hout : ∀ x∈xs,(F x).length ≤ coefficientBytes n := by
    intro x hx
    have h:=BitMachine.output_length_bound GaussCoefficientProgram.machine (GaussCoefficientProgram.outputs_poly x)
    have hi:=hin x hx
    have ht:=htime x hx
    change (F x).length ≤ x.length+bound x*GaussCoefficientProgram.machine.pushBound at h
    exact h.trans (by unfold coefficientBytes; gcongr)
  have hresult : ∀ x∈xs,(SourceListMachineWriter.result true (F x)).length ≤ framedBytes n := by
    intro x hx
    have h:=SourceListMachineWriter.result_length true (F x)
    have hq:=hout x hx
    unfold framedBytes
    omega
  have hitem : ∀ x∈xs,
      SourceListMachineWork.itemCost M x (SourceListMachineWriter.result true (F x))
        (GaussVectorOuterWriter.itemClock F bound x) ≤ itemCost n := by
    intro x hx
    have ht : GaussVectorOuterWriter.itemClock F bound x ≤ framedTime n := by
      have hP:=htime x hx
      have hQ:=hout x hx
      unfold GaussVectorOuterWriter.itemClock framedTime
      gcongr
    exact SourceListMachineWork.itemCost_le_envelope M x _ _
      (itemBytes n) (framedBytes n) (framedTime n) (hin x hx) (hresult x hx) ht
  have hcount : xs.length ≤ n := by
    simpa [xs,GaussCertificateWorkList.workPackets] using hk
  have hdigits : xs.length.bits.length ≤ n := (UnaryBinaryEncoding.bits_length_le _).trans hcount
  have hh:=SourceListMachineOuter.canonicalBound_le_source M xs
    (fun x => SourceListMachineWriter.result true (F x))
    (GaussVectorOuterWriter.itemClock F bound) 0 (fun _ => n) (fun _ => n)
    (fun _ => itemCost n) (fun _ => framedBytes n) hcount hdigits hitem hresult
  exact hh

theorem workBytes_le {m k : Nat} (B : Fin m → Fin k → ℚ) (f : Fin k)
    (n : Nat) (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ n) (hk : k ≤ n) :
    (SourceListEncoding.encode (GaussWorkListComplete.workPackets B f)).length ≤ workBytes n := by
  rw [GaussWorkCoefficientBridge.workPackets_eq]
  have h:=GaussCertificateWorkList.workPackets_length B f
  apply h.trans
  unfold workBytes itemBytes
  calc _ ≤ 3*n*(2*(n+2*n)+4)+1 := by gcongr
       _ = _ := by ring

theorem workCap_mono {m k n : Nat} (hm : m ≤ n) (hk : k ≤ n) :
    GaussActualWorkListClock.clock m k ≤ workCap n := by
  unfold workCap GaussActualWorkListClock.clock GaussActualWorkListClock.headerCap
    GaussActualWorkListClock.roundCap GaussActualWorkListClock.accumCap
    GaussActualWorkListClock.fieldCap GaussActualWorkListClock.packetCap
    GaussActualWorkListClock.stateCap GaussPivotPrefixClock.prefixClock
    GaussPivotPrefixClock.stateCap GaussPivotPrefixClock.outerEnvelope
    GaussPivotPrefixClock.itemEnvelope GaussPivotPrefixClock.pairCap MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

theorem workCap_polynomial : PolynomialBound (fun _ n => workCap n) := by
  unfold workCap GaussActualWorkListClock.clock GaussActualWorkListClock.headerCap
    GaussActualWorkListClock.roundCap GaussActualWorkListClock.accumCap
    GaussActualWorkListClock.fieldCap GaussActualWorkListClock.packetCap
    GaussActualWorkListClock.stateCap GaussPivotPrefixClock.prefixClock
    GaussPivotPrefixClock.stateCap GaussPivotPrefixClock.outerEnvelope
    GaussPivotPrefixClock.itemEnvelope GaussPivotPrefixClock.pairCap
  simp only [MachineInvokeFull.uniformBound,List.length_replicate]
  repeat' first | exact second | exact (constant _) | apply add | apply mul | apply power

theorem clock_polynomial : PolynomialBound (fun _ n => clock n) := by
  have hi : PolynomialBound (fun _ n => itemBytes n) := by
    unfold itemBytes
    exact add (mul (constant 6) second) (constant 3)
  have hp : PolynomialBound (fun _ n => coefficientTime n) := by
    unfold coefficientTime
    exact mul (constant _) (power (add hi (constant 1)) _)
  have hq : PolynomialBound (fun _ n => coefficientBytes n) := by
    unfold coefficientBytes
    exact add hi (mul hp (constant _))
  have ht : PolynomialBound (fun _ n => framedTime n) := by
    unfold framedTime
    exact add (add (add hp (mul (constant 2) hq)) (constant 2))
      (mul (constant _) (power (add hq (constant 1)) 2))
  have hr : PolynomialBound (fun _ n => framedBytes n) := by
    unfold framedBytes
    exact add (mul (constant 3) hq) (constant 1)
  have hj : PolynomialBound (fun _ n => itemCost n) := by
    unfold itemCost
    exact add (add (add (add (add
      (mul (mul (constant 20) (add hi (constant 1))) (add hi (constant 1))) ht)
      (mul (constant 4) hi)) hr)
      (mul (constant _) (add (add hi (mul ht (constant _))) (constant 1)))) (constant 9)
  have hv : PolynomialBound (fun _ n => vectorCap n) := by
    unfold vectorCap
    exact add (add (mul second (add (add (add hj (mul (constant 4) second)) (constant 7)) hr))
      (mul (constant 11) second)) (constant 17)
  have hw : PolynomialBound (fun _ n => workBytes n) := by
    unfold workBytes
    exact add (mul (mul (constant 3) second) (add hi (constant 1))) (constant 1)
  have hb : PolynomialBound (fun _ n => bodyCap n) := by
    unfold bodyCap
    exact add (add workCap_polynomial (uniform_invocation _ hw hv)) (constant 1)
  unfold clock
  exact add (add (mul (constant 5) (add second (constant 1))) hb) (constant 1)

#print axioms vectorClock_le
#print axioms workCap_polynomial
#print axioms clock_polynomial

end
end CurrentAdditive.GaussPostloopClock
