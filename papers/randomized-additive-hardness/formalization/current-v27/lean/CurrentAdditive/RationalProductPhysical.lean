import CurrentAdditive.RationalProductRepack

/-!
An end-to-end physical positive-rational product.  The first finite machine
computes two unreduced unsigned products in a twelve-field bank packet; the
second finite machine reverses the denominator and serializes the literal
three-field Code D `RawRat` packet.
-/

namespace EthInapproximability.CurrentPaper.RationalProductPhysical

open RationalProductPacket RationalProductRepack

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition RationalProductPacket.machine
    RationalProductRepack.machine

def result : List Bool → List Bool :=
  RationalProductRepack.result ∘ RationalProductPacket.result

theorem middle_length (input : List Bool) :
    (RationalProductPacket.result input).length ≤ 20*(input.length+1) := by
  cases hd : BitMachineBankCodec.decode 12 input with
  | none => simp [RationalProductPacket.result, BitMachineBankWrapper.result, hd]
  | some S =>
      have he := BitMachineBankCodec.encode_decode hd
      simp only [RationalProductPacket.result, BitMachineBankWrapper.result, hd]
      rw [← he]
      exact RationalProductPacket.size_bound S

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (1100*(input.length+1)^2) := by
  let middle := RationalProductPacket.result input
  have ha : RationalProductPacket.machine.OutputsWithin input middle
      (200*(input.length+1)^2) := by
    apply BitMachine.outputsWithin_mono RationalProductPacket.machine
      (RationalProductPacket.outputs input)
    have hp : 1 ≤ input.length+1 := by omega
    nlinarith
  have h := BitMachineComposition.composition_outputsWithin
    RationalProductPacket.machine RationalProductRepack.machine
    ha (RationalProductRepack.outputs middle)
  change machine.OutputsWithin input (result input)
    (200*(input.length+1)^2 + 2*middle.length+2 + 40*(middle.length+1)) at h
  apply BitMachine.outputsWithin_mono machine h
  have hm := middle_length input
  have hp : 1 ≤ input.length+1 := by omega
  nlinarith

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 1100, 2, ?_⟩
  intro input
  exact outputs input

theorem repack_read (packet : List Bool) (z : CurrentAdditive.CodeDCodec.RawRat)
    (h : RationalProductCodeDBridge.readOutput packet = some z) :
    RationalProductRepack.result packet =
      CurrentAdditive.CodeDCodec.encodeRawRat z := by
  cases hd : BitMachineBankCodec.decode 12 packet with
  | none => simp [RationalProductCodeDBridge.readOutput, hd] at h
  | some S =>
      have hz : z = ⟨false, S 0, (S 6).reverse⟩ := by
        simpa [RationalProductCodeDBridge.readOutput, hd] using h.symm
      subst z
      have he := BitMachineBankCodec.encode_decode hd
      rw [← he]
      exact RationalProductRepack.result_eq_rawRat S

theorem product_encoded (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : RationalProductCodeDBridge.Positive x)
    (hy : RationalProductCodeDBridge.Positive y) :
    ∃ z : CurrentAdditive.CodeDCodec.RawRat,
      result (RationalProductCodeDBridge.physicalInput x y) =
        CurrentAdditive.CodeDCodec.encodeRawRat z ∧
      CurrentAdditive.CodeDCodec.decodeRawRat
        (result (RationalProductCodeDBridge.physicalInput x y)) = some z ∧
      z.Valid ∧ z.value = x.value * y.value := by
  obtain ⟨z,hread,hvalid,hvalue⟩ :=
    RationalProductCodeDBridge.readOutput_product x y hx hy
  refine ⟨z, ?_, ?_, hvalid, hvalue⟩
  · exact repack_read _ z hread
  · change CurrentAdditive.CodeDCodec.decodeRawRat
      (RationalProductRepack.result
        (RationalProductPacket.result (RationalProductCodeDBridge.physicalInput x y))) = some z
    rw [repack_read _ z hread]
    exact CurrentAdditive.CodeDCodec.decodeRawRat_encodeRawRat z hvalid

end EthInapproximability.CurrentPaper.RationalProductPhysical
