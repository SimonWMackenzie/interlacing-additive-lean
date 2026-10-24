import CurrentAdditive.CodeDProductListClockV2

/-!
Exact physical composition boundary for the signed-product list.  Every
listed program here is literal except the per-pair router `R`, supplied as
a machine plus a genuine `OutputsWithin` proof.  The theorem must not be
instantiated with a pure packet function in place of that proof.
-/

namespace CurrentAdditive.CodeDProductListJoinV2

open EthInapproximability.CurrentPaper
open CodeDCodec
open CodeDPairProductTargetV2
open RationalProductSignedPhysical

def pairInputs (pairs : List (RawRat × RawRat)) : List (List Bool) :=
  pairs.map (fun p => pairBytes p.1 p.2)

noncomputable def routerMachine (R : BitMachine.Machine) : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine R

noncomputable def routerClock (R : BitMachine.Machine)
    (bound : List Bool → Nat) (pairs : List (RawRat × RawRat)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine R)
    (pairInputs pairs)
    (SourceListMachineOuterFramed.framedOutput productPacket)
    (SourceListMachineOuterFramed.framedBound productPacket bound)

noncomputable def joinedMachine (R : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition (routerMachine R) CodeDProductListV2.machine

theorem router_list_outputs (R : BitMachine.Machine)
    (bound : List Bool → Nat) (pairs : List (RawRat × RawRat))
    (hvalid : ∀ p ∈ pairs, p.1.Valid ∧ p.2.Valid)
    (hrouter : ∀ p ∈ pairs,
      R.OutputsWithin (pairBytes p.1 p.2) (productPacket (pairBytes p.1 p.2))
        (bound (pairBytes p.1 p.2))) :
    (routerMachine R).OutputsWithin
      (CodeDCodecV2.encodeItems (pairInputs pairs))
      (CodeDCodecV2.encodeItems (CodeDProductListV2.productInputs pairs))
      (routerClock R bound pairs) := by
  have hitem : ∀ x ∈ pairInputs pairs,
      R.OutputsWithin x (productPacket x) (bound x) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hrouter p hp
  have h := SourceListMachineOuterFramed.outputsWithin R
    (pairInputs pairs) productPacket bound hitem
  have hmap : (pairInputs pairs).map productPacket =
      CodeDProductListV2.productInputs pairs := by
    simp only [pairInputs, CodeDProductListV2.productInputs, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact productPacket_pairBytes p.1 p.2
      (hvalid p hp).1 (hvalid p hp).2
  rw [hmap] at h
  simpa only [routerMachine, routerClock, CodeDCodecV2.encodeItems] using h

theorem joined_outputs (R : BitMachine.Machine)
    (bound : List Bool → Nat) (pairs : List (RawRat × RawRat))
    (hvalid : ∀ p ∈ pairs, p.1.Valid ∧ p.2.Valid)
    (hrouter : ∀ p ∈ pairs,
      R.OutputsWithin (pairBytes p.1 p.2) (productPacket (pairBytes p.1 p.2))
        (bound (pairBytes p.1 p.2))) :
    (joinedMachine R).OutputsWithin
      (CodeDCodecV2.encodeItems (pairInputs pairs))
      (CodeDCodecV2.encodeItems (CodeDProductListV2.productOutputs pairs))
      (routerClock R bound pairs +
        2*(CodeDCodecV2.encodeItems (CodeDProductListV2.productInputs pairs)).length + 2 +
        CodeDProductListV2.clock pairs) := by
  exact BitMachineComposition.composition_outputsWithin
    (routerMachine R) CodeDProductListV2.machine
    (router_list_outputs R bound pairs hvalid hrouter)
    (CodeDProductListV2.outputs pairs)

#print axioms router_list_outputs
#print axioms joined_outputs

end CurrentAdditive.CodeDProductListJoinV2
