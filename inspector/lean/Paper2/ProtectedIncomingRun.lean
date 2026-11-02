import Paper2.ProtectedIncomingFromFailure
import Paper2.ReferenceRunCorrectness
import Paper2.ReferencePublicDestinations

/-!
# Protected incoming receipts at physical reference destinations

The state and retained columns here are the original Items source. The
subtype protocols below are restrictions of the actual padded run nodes.
-/

namespace Paper2.ProtectedIncomingRun

open SourceMatrix SourceLaws SourceProfileParameters
open ReferenceCertificateTree ReferencePublicDestinations
open Workspace.Types.Protocol Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
/-- Every physical stopping position has incoming protected mass strictly
below its route-dependent row-ladder capacity, for any fixed original
contributor set. The protocol and correctness are inherited from the one
actual restricted source protocol. -/
theorem physical_incoming_mass_lt
    {X Y Vtx : Type*} [Fintype X] [Fintype Y]
    [Fintype Vtx] [Nonempty Vtx]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) Vtx →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := Vtx)
      (width L - 2) (outerWidth L) (width L) w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (E0 : Finset (Fin w))
    (hY : RestorationCoverParameters.theta Q ≤
      (((SourceLawBinding.matrixColumnLaw (V := Vtx) μ
        (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw).iid w).prob (· ∈ Y'))
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (I : Finset (Fin w))
    (v : (run (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r
      (actualPaddedState R0 Y' row0 col0 P E0 r)).Leaves) :
    (∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i
      ((run (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r
        (actualPaddedState R0 Y' row0 col0 P E0 r)).state v).rows) <
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
        (2 ^ (r - ((run (rawLaw ν (width L - 2) (outerWidth L)
          (width L)).toFiniteLaw ReferenceSourceInitial.input
          (ReferenceSchedule.floor w (x L)) 0 r
          (actualPaddedState R0 Y' row0 col0 P E0 r)).route v).length) : ℕ) := by
  classical
  let rawμ := (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let T := run rawμ ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
  let S := T.state v
  let t := r - (T.route v).length
  have hPpad : ∀ a ∈ st.rows, ∀ c ∈ Y', st.protocol.eval a c =
      fullInterlace (N base activity ξ₀) w a c := by
    intro a ha c hc
    have he := actualPaddedState_eval R0 Y' row0 col0 P E0 r
      ⟨a, ha⟩ ⟨c, hc⟩
    exact he.trans (hP ⟨a, ha⟩ ⟨c, hc⟩)
  have hlocal := ReferenceRunCorrectness.computes_on_original_rectangle
    rawμ ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
    (fullInterlace (N base activity ξ₀) w) Y' hPpad v
  have hbasecost : st.protocol.cost ≤ C - 1 + r := by
    have hpad := actualPaddedState_cost R0 Y' row0 col0 P E0 r
    have hpad' : st.protocol.cost ≤ max P.cost r := hpad
    omega
  have hcost := ReferenceRunCorrectness.remaining_cost rawμ
    ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) r (C - 1)
    st hbasecost v
  let Qnode : Protocol S.rows Y' Bool :=
    Workspace.UpperBound.Protocol.comap (fun a : S.rows => a.val)
      (fun c : Y' => c.val) S.protocol
  have hQnode : Qnode.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val) := by
    intro row col
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact hlocal row.val row.property col.val col.property
  have hQcost : Qnode.cost ≤ C - 1 + t := by
    simpa only [Qnode, Workspace.UpperBound.Protocol.comap_cost] using hcost
  by_contra hn
  have hfailed : (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) * (2 ^ t : ℕ) ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i S.rows := by
    exact le_of_not_gt hn
  have hfailed' : 1024 * (1 / 256 : ℝ) *
      RestorationCoverParameters.B2 Q * (r + 2) * width L *
      (2 ^ t : ℕ) ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i S.rows := by
    simpa only [mul_assoc] using hfailed
  by_cases hfinal : (T.route v).length = r
  · have ht : t = 0 := by dsimp [t]; omega
    have hshort : Qnode.cost ≤ C - 1 := by omega
    have hbad := ProtectedIncomingFromFailure.final_mass_failure_impossible
      μ ν base L d hd hD hp hinner houter hwide href activity ξ₀
      w r Q C 0 hw hQ hC hCeq S.rows Y' I hY hxsmall
      (by simpa only [ht, pow_zero, mul_one] using hfailed')
      Qnode hQnode hshort
    exact hbad
  · obtain ⟨htpos, query, left, right, hshape⟩ :=
      ReferenceRunCorrectness.before_depth_is_bob rawμ
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L))
        r st (by
          exact ReferencePrefix.padAlicePrefix_noEarlyLeaf r
            (actualOriginalState R0 Y' row0 col0 P E0).protocol)
        v hfinal
    let left' : Protocol S.rows Y' Bool :=
      Workspace.UpperBound.Protocol.comap (fun a : S.rows => a.val)
        (fun c : Y' => c.val) left
    let right' : Protocol S.rows Y' Bool :=
      Workspace.UpperBound.Protocol.comap (fun a : S.rows => a.val)
        (fun c : Y' => c.val) right
    have hnode : Qnode = Protocol.bNode (fun c : Y' => query c.val)
        left' right' := by
      dsimp [Qnode, left', right']
      rw [hshape]
      rfl
    have hnodeP : (Protocol.bNode (fun c : Y' => query c.val)
        left' right').Computes (fun row col =>
          fullInterlace (N base activity ξ₀) w row.val col.val) := by
      rw [← hnode]
      exact hQnode
    have hnodecost : (Protocol.bNode (fun c : Y' => query c.val)
        left' right').cost ≤ C + t - 1 := by
      rw [← hnode]
      omega
    exact ProtectedIncomingFromFailure.bob_mass_failure_impossible
      μ ν base L d hd hD hp hinner houter hwide href activity ξ₀
      w r Q C t hw hQ hC hCeq S.rows Y' I hY hxsmall
      hfailed' query left' right' hnodeP hnodecost

end Paper2.ProtectedIncomingRun

#print axioms Paper2.ProtectedIncomingRun.physical_incoming_mass_lt
