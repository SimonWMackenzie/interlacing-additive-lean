import CurrentAdditive.CodeDAppendOperandsV2
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-!
Literal counted-list execution of the signed rational product machine.
The input is already a V2 list of flattened product Bank12 packets.  A
separate physical router must still construct that list from nested operand
pairs; this module contains no host-language machine callback.
-/

namespace CurrentAdditive.CodeDProductListV2

open EthInapproximability.CurrentPaper
open CodeDCodec
open RationalProductSignedPhysical

def productInputs (pairs : List (RawRat × RawRat)) : List (List Bool) :=
  pairs.map (fun p => productInput p.1 p.2)

def productOutputs (pairs : List (RawRat × RawRat)) : List (List Bool) :=
  pairs.map (fun p => encodeRawRat (productRat p.1 p.2))

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine RationalProductSignedPhysical.machine

noncomputable def clock (pairs : List (RawRat × RawRat)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine RationalProductSignedPhysical.machine)
    (productInputs pairs)
    (SourceListMachineOuterFramed.framedOutput RationalProductSignedPhysical.result)
    (SourceListMachineOuterFramed.framedBound
      RationalProductSignedPhysical.result
      (fun input => 1300*(input.length+1)^2))

theorem outputs (pairs : List (RawRat × RawRat)) :
    machine.OutputsWithin
      (CodeDCodecV2.encodeItems (productInputs pairs))
      (CodeDCodecV2.encodeItems (productOutputs pairs))
      (clock pairs) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    RationalProductSignedPhysical.machine (productInputs pairs)
    RationalProductSignedPhysical.result
    (fun input => 1300*(input.length+1)^2)
    (by intro input _; exact RationalProductSignedPhysical.outputs input)
  have hmap : (productInputs pairs).map RationalProductSignedPhysical.result =
      productOutputs pairs := by
    simp only [productInputs, productOutputs, List.map_map]
    apply List.map_congr_left
    intro p hp
    rcases p with ⟨x, y⟩
    exact RationalProductSignedPhysical.result_product x y
  rw [hmap] at h
  simpa only [machine, clock, CodeDCodecV2.encodeItems] using h

theorem output_values (pairs : List (RawRat × RawRat)) :
    (pairs.map (fun p => (productRat p.1 p.2).value)) =
      pairs.map (fun p => p.1.value * p.2.value) := by
  apply List.map_congr_left
  intro p _
  exact productRat_value p.1 p.2

#print axioms outputs
#print axioms output_values

end CurrentAdditive.CodeDProductListV2
