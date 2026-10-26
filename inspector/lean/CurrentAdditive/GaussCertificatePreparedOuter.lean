import CurrentAdditive.GaussCertificateWorkList
import CurrentAdditive.GaussVectorOuterWriter

/-! Conditional, exact composition interface: a physical per-column machine
and the fixed vector outer writer produce the canonical direct-candidate
packet from the prepared work list.  The hypotheses state the remaining
per-column physical obligation explicitly; this is not an endpoint claim. -/

namespace CurrentAdditive.GaussCertificatePreparedOuter

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussCertificateWorkList
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI

theorem outputs_prepared_direct {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) (hf : f.val ≤ m)
    (M : BitMachine.Machine)
    (F : List Bool → List Bool) (bound : List Bool → Nat)
    (hF : ∀ j : Fin k,
      F (workPacket B f j) =
        coefficientPacket (directCandidate B f hf j))
    (hM : ∀ j : Fin k,
      M.OutputsWithin (workPacket B f j)
        (F (workPacket B f j)) (bound (workPacket B f j))) :
    (GaussVectorOuterWriter.machine M).OutputsWithin
      (SourceListEncoding.encode (workPackets B f))
      (vectorPacket (Array.ofFn (directCandidate B f hf)))
      (SourceListMachineOuter.canonicalBound
        (GaussVectorOuterWriter.framedMachine M)
        (workPackets B f)
        (fun x => SourceListMachineWriter.result true (F x))
        (GaussVectorOuterWriter.itemClock F bound)) := by
  have hMlist : ∀ x ∈ workPackets B f,
      M.OutputsWithin x (F x) (bound x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hM j
  have hmap : (workPackets B f).map F =
      (List.finRange k).map
        (fun j => coefficientPacket (directCandidate B f hf j)) := by
    simp only [workPackets, List.map_map]
    apply List.map_congr_left
    intro j hj
    exact hF j
  have h := GaussVectorOuterWriter.outputs_prepared M
    (workPackets B f) F bound hMlist
  rw [hmap] at h
  simpa [vectorPacket, CurrentAdditive.CodeDCodecV2.encodeItems,
    Array.toList_ofFn, List.ofFn_eq_map] using h

#print axioms outputs_prepared_direct

end CurrentAdditive.GaussCertificatePreparedOuter
