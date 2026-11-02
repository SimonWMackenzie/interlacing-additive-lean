import CurrentAdditive.CodeDProductListV2
import EthInapproximability.CurrentPaper.SourceListMachineWork
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! Polynomial list clock for literal signed product calls. -/

namespace CurrentAdditive.CodeDProductListClockV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

private noncomputable def F :=
  SourceListMachineOuterFramed.itemMachine RationalProductSignedPhysical.machine

noncomputable def resultBound (L : Nat) : Nat :=
  L + 1300*(L+1)^2 * RationalProductSignedPhysical.machine.pushBound

noncomputable def frameBound (L : Nat) : Nat := 3*resultBound L+1

noncomputable def timeBound (L : Nat) : Nat :=
  1300*(L+1)^2 + 2*resultBound L+2 +
    (UnaryBinaryEncoding.coefficient+7)*(resultBound L+1)^2

noncomputable def itemEnvelope (L : Nat) : Nat :=
  20*(L+1)*(L+1)+timeBound L+4*L+frameBound L+
    F.stackCount*(L+timeBound L*F.pushBound+1)+9

noncomputable def polynomialClock (N L : Nat) : Nat :=
  N*(itemEnvelope L+4*(N+1)+7+frameBound L)+11*(N+1)+17

theorem result_length_le (input : List Bool) (L : Nat)
    (hL : input.length ≤ L) :
    (RationalProductSignedPhysical.result input).length ≤ resultBound L := by
  have ho := BitMachine.output_length_bound
    RationalProductSignedPhysical.machine
    (RationalProductSignedPhysical.outputs input)
  have hp : (input.length+1)^2 ≤ (L+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold resultBound
  have hm := Nat.mul_le_mul_right RationalProductSignedPhysical.machine.pushBound
    (Nat.mul_le_mul_left 1300 hp)
  omega

theorem framed_length_le (input : List Bool) (L : Nat)
    (hL : input.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput
      RationalProductSignedPhysical.result input).length ≤ frameBound L := by
  have hr := result_length_le input L hL
  have hf := EncodedGraph.natField_length_upper
    (RationalProductSignedPhysical.result input).length
  unfold SourceListMachineOuterFramed.framedOutput frameBound
  simp only [List.length_append]
  omega

theorem framed_time_le (input : List Bool) (L : Nat)
    (hL : input.length ≤ L) :
    SourceListMachineOuterFramed.framedBound
      RationalProductSignedPhysical.result
      (fun x => 1300*(x.length+1)^2) input ≤ timeBound L := by
  have hr := result_length_le input L hL
  have hp : (input.length+1)^2 ≤ (L+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hq : ((RationalProductSignedPhysical.result input).length+1)^2 ≤
      (resultBound L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  change
    1300*(input.length+1)^2 +
      2*(RationalProductSignedPhysical.result input).length+2 +
      (UnaryBinaryEncoding.coefficient+7)*
        ((RationalProductSignedPhysical.result input).length+1)^2 ≤
    1300*(L+1)^2 + 2*resultBound L+2 +
      (UnaryBinaryEncoding.coefficient+7)*(resultBound L+1)^2
  have hp' := Nat.mul_le_mul_left 1300 hp
  have hq' := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+7) hq
  omega

theorem clock_le_polynomial (pairs : List (CodeDCodec.RawRat × CodeDCodec.RawRat))
    (L : Nat)
    (hL : ∀ x ∈ CodeDProductListV2.productInputs pairs, x.length ≤ L) :
    CodeDProductListV2.clock pairs ≤ polynomialClock pairs.length L := by
  let xs := CodeDProductListV2.productInputs pairs
  have hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput RationalProductSignedPhysical.result x)
        (SourceListMachineOuterFramed.framedBound
          RationalProductSignedPhysical.result
          (fun x => 1300*(x.length+1)^2) x) ≤ itemEnvelope L := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope F x _ _ L
      (frameBound L) (timeBound L) (hL x hx)
      (framed_length_le x L (hL x hx))
      (framed_time_le x L (hL x hx))
  have hout : ∀ x ∈ xs,
      (SourceListMachineOuterFramed.framedOutput
        RationalProductSignedPhysical.result x).length ≤ frameBound L := by
    intro x hx
    exact framed_length_le x L (hL x hx)
  have hdigits : xs.length.bits.length ≤ xs.length+1 := by
    have hb := UnaryBinaryEncoding.bits_length_le xs.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source F xs
    (SourceListMachineOuterFramed.framedOutput RationalProductSignedPhysical.result)
    (SourceListMachineOuterFramed.framedBound
      RationalProductSignedPhysical.result
      (fun x => 1300*(x.length+1)^2))
    xs.length (fun n => n) (fun n => n+1)
    (fun _ => itemEnvelope L) (fun _ => frameBound L)
    (le_refl _) hdigits hitem hout
  change CodeDProductListV2.clock pairs ≤ polynomialClock xs.length L at h
  have hxlen : xs.length = pairs.length := by
    simp [xs, CodeDProductListV2.productInputs]
  simpa only [hxlen] using h

#print axioms clock_le_polynomial

end CurrentAdditive.CodeDProductListClockV2
