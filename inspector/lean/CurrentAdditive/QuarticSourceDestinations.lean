import CurrentAdditive.QuarticRestorationRun
import Paper2.ReferenceSourceInitial

/-! Private v27 source-shaped instance of the actual reference-certificate
runner. The retained rectangle and protocol are explicit. -/

namespace CurrentAdditive.QuarticSourceDestinations

open Paper2
open Paper2.RestorationCoverParameters
open Workspace.Types.Protocol SourceMatrix SourceLaws ReferenceCertificateTree

variable {X Y V A : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype A]
  [Nonempty V] [Nonempty A]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

theorem source_destinations27
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R0 : Set (ReferenceSourceInitial.Rows (Y := Y)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (ReferenceSourceInitial.Columns (X := X)
      (V := V) (A := A) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      ReferenceSourceInitial.sourceMatrix base activity ξ₀ row.val col.val))
    (r Q C : ℕ) (η : ℚ) (hw : w = 2 ^ r)
    (hQ : 0 < Q) (hC : 4 ≤ C) (hPcost : P.cost ≤ C + r - 1)
    (hη : 0 < η) (hη1 : η < 1)
    (hquarter : QuarticSchedule.quarterCheck27Prop w Q η)
    (htstar : 4 * tStar Q ≤ w)
    (x : ℝ) (hx : 0 < x)
    (hR0 : 1 - (η : ℝ) / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : theta Q ≤
      ((rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw.prob (· ∈ Y'))
    (hmargin : 2 * w * x + (η : ℝ) / (16 * (127 / 128 : ℝ)) < 1)
    (hprofile : RestrictionProfile
      (fun Z row => raw base activity row Z)
      (rawLaw ν q₁ q₂ s).toFiniteLaw
      (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw
      x ((C - 1 : ℕ) : ℤ)) :
    ∃ E₀ : Finset (Fin w), E₀.card ≤ QuarticSchedule.e027 Q η ∧
      ∃ row0 : R0, ∃ col0 : Y', ∃ st : ReferenceCertificateTree.State
        (ReferenceSourceInitial.Rows (Y := Y)
          (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (ReferenceSourceInitial.Columns (X := X)
          (V := V) (A := A) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (Fin w) (RawColumn q₁ q₂ s Y),
      st = ReferenceSourceInitial.initialState R0 Y' row0 col0 P E₀ r ∧
      let T := run (rawLaw ν q₁ q₂ s).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w x) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      w - QuarticSchedule.E27 Q η ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
          QuarticSchedule.E27 Q η := by
  classical
  have hwpos : 0 < w := by rw [hw]; positivity
  have hYfinite : theta Q ≤
      ((rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.iid w).prob
        (· ∈ Y') := by
    simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hY
  obtain ⟨E₀, hE, _hsingle, hsmall⟩ :=
    QuarticRestorationCover.exists_v27_cover
      (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw
      w Q η hQ hη hη1 hquarter htstar Y' hYfinite
  have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
  obtain ⟨row0, col0, st, hst, hrows, hfam, hvalid, hunits,
    hreach, hfloor, hcompute, hcost⟩ :=
    ReferenceSourceInitial.exists_initial_state μ ν base activity ξ₀
      R0 Y' P hP hwpos C r (by omega) hPcost (η : ℝ) x (theta Q)
      (le_of_lt hx) (theta_pos hQ) hR0 hY hmargin E₀
  refine ⟨E₀, hE, row0, col0, st, hst, ?_⟩
  have hscale : 2 * (2 : ℝ) ^ r * x ≤ 1 := by
    have hwreal : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
    have htail : 0 ≤ (η : ℝ) / (16 * (127 / 128 : ℝ)) := by positivity
    rw [← hwreal]
    linarith
  have hactive : st.family.active = Finset.univ \ E₀ := by
    rw [hfam]
    rfl
  have hunits' : 2 * st.family.active.card ≤
      ReferenceCertificates.units st.family := by
    rw [hunits, hactive]
    have hsub : E₀.card ≤ w := by
      simpa using Finset.card_le_card (Finset.subset_univ E₀)
    have hc : (Finset.univ \ E₀).card = w - E₀.card := by
      rw [Finset.card_sdiff]
      simp
    omega
  have hprefix : ReferencePrefix.NoEarlyLeaf r st.protocol := by
    rw [hst]
    exact ReferencePrefix.padAlicePrefix_noEarlyLeaf r _
  have hcost' : st.protocol.cost ≤ (C - 1) + r := by omega
  have hcompute' : ∀ row ∈ st.rows, ∀ y ∈ Y',
      st.protocol.eval row y =
        ReferenceSourceInitial.sourceMatrix base activity ξ₀ row y := by
    intro row hr y hy
    rw [hrows] at hr
    exact hcompute row hr y hy
  have hentry : ∀ i Z, ReferenceSourceInitial.input i Z ∈ st.rows →
      ∀ y ∈ Y', ReferenceSourceInitial.sourceMatrix base activity ξ₀
        (ReferenceSourceInitial.input i Z) y = raw base activity (y i) Z := by
    intro i Z _ y _
    rfl
  exact QuarticRestorationRun.run_destinations27
    (rawLaw ν q₁ q₂ s) (rowLaw (V := V) (A := A) μ q₁ q₂ s)
    (fun Z row => raw base activity row Z)
    (ReferenceSourceInitial.sourceMatrix base activity ξ₀)
    ReferenceSourceInitial.input Y' st E₀ Q (C - 1) r η x
    hw hE hQ (by omega) hx hscale hprofile hYfinite hsmall
    hactive hvalid hunits' hreach hfloor hcompute' hentry hprefix hcost'

end CurrentAdditive.QuarticSourceDestinations

#print axioms CurrentAdditive.QuarticSourceDestinations.source_destinations27
