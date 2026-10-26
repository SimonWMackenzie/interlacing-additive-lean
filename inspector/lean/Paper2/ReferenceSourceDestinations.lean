import Paper2.ReferenceDestinations
import Paper2.ReferenceSourceInitial
import Paper2.RestorationPublicCovers

/-!
# Literal first-interlace reference destinations

The cover and initial certificate state are constructed from the retained
rectangle of the original source matrix. The actual padded protocol is then
run through `ReferenceDestinations.run_destinations`.
-/

namespace Paper2.ReferenceSourceDestinations

open Workspace.Types.Protocol SourceMatrix SourceLaws ReferenceCertificateTree
open Paper2.SourceSupportFrontier

variable {X Y V A : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype A]
  [Nonempty V] [Nonempty A]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

theorem source_destinations
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R0 : Set (ReferenceSourceInitial.Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (ReferenceSourceInitial.Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      ReferenceSourceInitial.sourceMatrix base activity ξ₀ row.val col.val))
    (r Q C : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 4 ≤ C)
    (hPcost : P.cost ≤ C + r - 1)
    (eta x : ℝ) (heta : 0 < eta) (heta1 : eta < 1) (hx : 0 < x)
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw.prob (· ∈ Y'))
    (hmargin : 2 * w * x + eta / (16 * (127 / 128 : ℝ)) < 1)
    (hprofile : RestrictionProfile
      (fun Z row => raw base activity row Z)
      (rawLaw ν q₁ q₂ s).toFiniteLaw
      (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw
      x ((C - 1 : ℕ) : ℤ)) :
    ∃ E0 : Finset (Fin w), E0.card ≤ RestorationPublicCovers.e0 Q eta ∧
      ∃ row0 : R0, ∃ col0 : Y', ∃ st : ReferenceCertificateTree.State
        (ReferenceSourceInitial.Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (ReferenceSourceInitial.Columns (X := X) (V := V) (A := A)
          (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (Fin w) (RawColumn q₁ q₂ s Y),
      st = ReferenceSourceInitial.initialState R0 Y' row0 col0 P E0 r ∧
      let T := run (rawLaw ν q₁ q₂ s).toFiniteLaw ReferenceSourceInitial.input
        (ReferenceSchedule.floor w x) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      w - ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
          ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) := by
  classical
  have hwpos : 0 < w := by rw [hw]; positivity
  have hYfinite : RestorationCoverParameters.theta Q ≤
      ((rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.iid w).prob (· ∈ Y') := by
    simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hY
  obtain ⟨E0, hE, _hsingle, hpair99, hpair18, hdyadic⟩ :=
    RestorationPublicCovers.exists_cover
      (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw
      w Q hQ eta heta heta1 Y' hYfinite
  obtain ⟨row0, col0, st, hst, hrows, hfam, hvalid, hunits, hreach,
    hfloor, hcompute, hcost⟩ :=
    ReferenceSourceInitial.exists_initial_state μ ν base activity ξ₀ R0 Y' P hP
      hwpos C r (by omega) hPcost eta x (RestorationCoverParameters.theta Q)
      (le_of_lt hx) (RestorationCoverParameters.theta_pos hQ) hR0 hY hmargin E0
  refine ⟨E0, hE, row0, col0, st, hst, ?_⟩
  have hscale : 2 * (2 : ℝ) ^ r * x ≤ 1 := by
    have hwreal : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
    have htail : 0 ≤ eta / (16 * (127 / 128 : ℝ)) := by positivity
    rw [← hwreal]
    linarith
  have hactive : st.family.active = Finset.univ \ E0 := by
    rw [hfam]
    rfl
  have hunits' : 2 * st.family.active.card ≤ ReferenceCertificates.units st.family := by
    rw [hunits, hactive]
    have hsub : E0.card ≤ w := by
      simpa using Finset.card_le_card (Finset.subset_univ E0)
    have hc : (Finset.univ \ E0).card = w - E0.card := by
      rw [Finset.card_sdiff]
      simp
    omega
  have hprefix : ReferencePrefix.NoEarlyLeaf r st.protocol := by
    rw [hst]
    exact ReferencePrefix.padAlicePrefix_noEarlyLeaf r _
  have hcost' : st.protocol.cost ≤ (C - 1) + r := by omega
  have hcompute' : ∀ row ∈ st.rows, ∀ y ∈ Y',
      st.protocol.eval row y = ReferenceSourceInitial.sourceMatrix base activity ξ₀ row y := by
    intro row hr y hy
    rw [hrows] at hr
    exact hcompute row hr y hy
  have hentry : ∀ i Z, ReferenceSourceInitial.input i Z ∈ st.rows →
      ∀ y ∈ Y', ReferenceSourceInitial.sourceMatrix base activity ξ₀
        (ReferenceSourceInitial.input i Z) y = raw base activity (y i) Z := by
    intro i Z _ y _
    rfl
  exact ReferenceDestinations.run_destinations
    (rawLaw ν q₁ q₂ s) (rowLaw (V := V) (A := A) μ q₁ q₂ s)
    (fun Z row => raw base activity row Z)
    (ReferenceSourceInitial.sourceMatrix base activity ξ₀)
    ReferenceSourceInitial.input Y' st E0 (RestorationPublicCovers.e0 Q eta)
    Q (C - 1) r x hw hE hQ (by omega) hx hscale hprofile hYfinite
    hpair99 hpair18 hdyadic hactive hvalid hunits' hreach hfloor
    hcompute' hentry hprefix hcost'

end Paper2.ReferenceSourceDestinations

#print axioms Paper2.ReferenceSourceDestinations.source_destinations
