import CurrentAdditive.GaussSearchGridInput64
import CurrentAdditive.GaussPivotSearchSemantic

namespace CurrentAdditive.GaussSearchGridBridge64

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64

def rawGridBank {m k : Nat} (s : GaussControlTrace.State m k)
    (pivot : Nat) : Fin 4 → List Bool :=
  ![GaussPhysical.encodeTypedMatrix s.B, List.replicate s.r true,
    List.replicate pivot true, List.replicate s.c true]

theorem saved_high_empty {m k : Nat} (s : GaussControlTrace.State m k)
    (j : Bank) (hj : 59 ≤ j.val) (h63 : j ≠ 63) :
    GaussPivotPrepSave64.saved s j = [] := by
  have h30 : j ≠ 30 := by intro h; subst j; simp at hj
  have h12 : j ≠ 12 := by intro h; subst j; simp at hj
  have h13 : j ≠ 13 := by intro h; subst j; simp at hj
  have h31 : j ≠ 31 := by intro h; subst j; simp at hj
  have h53 : j ≠ 53 := by intro h; subst j; simp at hj
  have h55 : j ≠ 55 := by intro h; subst j; simp at hj
  have h56 : j ≠ 56 := by intro h; subst j; simp at hj
  have h58 : j ≠ 58 := by intro h; subst j; simp at hj
  unfold GaussPivotPrepSave64.saved GaussPivotPrepSave64.afterP
    GaussPivotPrepSave64.afterC GaussPivotPrepSave64.afterR
  rw [SourceClausePreservingBroadcast.other_preserved
    13 63 [58] _ _ j h13 h63 (by simpa using h58)]
  rw [SourceClausePreservingBroadcast.other_preserved
    31 63 [56] _ _ j h31 h63 (by simpa using h56)]
  rw [SourceClausePreservingBroadcast.other_preserved
    12 63 [55] _ _ j h12 h63 (by simpa using h55)]
  rw [SourceClausePreservingBroadcast.other_preserved
    30 63 [53] _ _ j h30 h63 (by simpa using h53)]
  exact GaussPivotPrepHigh64.prepared_high s j (by omega)

theorem searched_scratch_empty {m k : Nat}
    (s : GaussControlTrace.State m k) (Sf : Fin 32 → List Bool)
    (j : Bank) (hj : 59 ≤ j.val) (h63 : j ≠ 63) :
    GaussPivotSearchHigh64.searched s Sf j = [] := by
  rw [GaussPivotSearchHigh64.searched_high s Sf j (by omega)]
  exact saved_high_empty s j hj h63

theorem packet_exact {m k : Nat} (s : GaussControlTrace.State m k)
    (S : Bank → List Bool) (p : Nat)
    (h8 : S 8 = GaussPhysical.encodeTypedMatrix s.B)
    (h53 : S 53 = List.replicate s.r true)
    (h19 : S 19 = List.replicate p true)
    (h55 : S 55 = List.replicate s.c true) :
    GaussSearchGridInput64.packet S = BitMachineBankCodec.encode (rawGridBank s p) := by
  apply congrArg BitMachineBankCodec.encode
  funext j
  fin_cases j <;>
    simpa [GaussSearchGridInput64.words, GaussSearchGridInput64.location,
      rawGridBank] using (by first | exact h8 | exact h53 | exact h19 | exact h55)

/-- The numeric pivot selected by the flag machine is the typed first pivot. -/
theorem firstHit_pivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) (p : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩ = some p) :
    GaussFlagSearch.firstHit
      (GaussPivotSearchSemantic.flags s.B ⟨s.c,hc⟩) s.r = (true,p.val) := by
  have h := GaussPivotSearchSemantic.selected_pivot_val s.B ⟨s.c,hc⟩ s.r
  rw [hp] at h
  simp only [Option.map_some, GaussFlagSearch.selected] at h
  cases he : GaussFlagSearch.firstHit
      (GaussPivotSearchSemantic.flags s.B ⟨s.c,hc⟩) s.r with
  | mk found n =>
      cases found
      · simp [he] at h
      · simp [he] at h
        exact Prod.ext rfl h.symm

/-- The serializer's blanks are proved from the actual search frame, rather
than supplied as a new state assumption. -/
theorem searched_packet_run {m k : Nat} (s : GaussControlTrace.State m k)
    (Sf : Fin 32 → List Bool) :
    ∃ u ≤ 2 * (GaussSearchGridInput64.packet
          (GaussPivotSearchHigh64.searched s Sf)).length + 2,
      let out := ((advance GaussSearchGridInput64.program)^[u])
        (GaussSearchGridInput64.initial (GaussPivotSearchHigh64.searched s Sf))
      out.l = none ∧
      out.stk 62 = GaussSearchGridInput64.packet
        (GaussPivotSearchHigh64.searched s Sf) ∧
      out.stk 20 = (GaussPivotSearchHigh64.searched s Sf) 20 ∧
      out.stk 56 = GaussControlTrace.statePacket s := by
  obtain ⟨u,hu,hh,ho,htag,hstate,_⟩ :=
    GaussSearchGridInput64.physical_serialize
      (GaussPivotSearchHigh64.searched s Sf)
      (searched_scratch_empty s Sf 60 (by decide) (by decide))
      (searched_scratch_empty s Sf 61 (by decide) (by decide))
      (searched_scratch_empty s Sf 62 (by decide) (by decide))
  refine ⟨u,hu,hh,ho,htag,?_⟩
  rw [hstate,GaussPivotSearchHigh64.searched_high s Sf 56 (by decide)]
  exact GaussPivotPrepSave64.saved_packet s

#print axioms saved_high_empty
#print axioms searched_scratch_empty
#print axioms packet_exact
#print axioms firstHit_pivot
#print axioms searched_packet_run

end
end CurrentAdditive.GaussSearchGridBridge64
