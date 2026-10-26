import CurrentAdditive.V39IndexedNearFull
import CurrentAdditive.V39IndexedItemNumber
import CurrentAdditive.V39GeneratedPrefix

/-! The current near-full deletion bound for literal finite SourceData.
The item numbering and the constructor's concrete selector permutation
are discharged internally; all three original Code D lists are unchanged. -/

namespace CurrentAdditive.V39GeneratedNearFull

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicIndexedMatrix CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge
open CurrentAdditive.V39IndexedItemNumber

variable {D t n m r nx ny : ℕ}
  [NeZero (2^t)] [NeZero (2^t-2)]
  [NeZero (LiteralEdgeEncoder.Width (2^t) m r)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

theorem restriction_lower
    (src : SourceData (D := D) (q₁ := 2^t-2)
      (q₂ := LiteralEdgeEncoder.Width (2^t) m r) (s := 2^t) μX μY)
    (hD : 8 ≤ D) (hs : 4 ≤ 2^t) (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (Δ : ℕ) (hΔ : 0 < Δ) (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, γ * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d ell : ℕ) (hd : 2 ≤ d)
    (hq₂ : LiteralEdgeEncoder.Width (2^t) m r = 2^ell)
    (hq2 : 2 ≤ LiteralEdgeEncoder.Width (2^t) m r)
    (x ρ η : ℝ) (hx : 0 < x) (hρ : 0 < ρ) (hη : 0 < η)
    (hηSmall : η < 1/100)
    (hηTemplate : (256/255 : ℝ)*(2^t : ℕ)*η ≤ 1/1000)
    (hηAllowance : η ≤ deletionAllowance (V := Fin n) (E := Fin m) γ Δ (2^t))
    (hassign : 4*((2^t : ℕ) : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*((2^t : ℕ) : ℝ)*(2^t-2 : ℕ) +
      1024*(2^t : ℕ)*η*LiteralEdgeEncoder.Width (2^t) m r <
      (γ/24)*LiteralEdgeEncoder.Width (2^t) m r/4)
    (hsmall : 2*(LiteralEdgeEncoder.Width (2^t) m r : ℝ)*x ≤ 1/8)
    (hprefixGap : 2*(2 : ℝ)^t*x < 999/1000)
    (hdominant : (998/1000 : ℝ) ≤ 999/1000 - 2*((2^t : ℕ)-1 : ℕ)*x)
    (hprofileR : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A (toSources src) R)
      src.gamma.law.toFiniteLaw
      (product (uniform (2^t-2)) μX).toFiniteLaw x ((d+t : ℕ) : ℤ))
    (hprofileT : V38RestrictionProfiles.TwoThresholdProfile (V39GeneratedPrefix.template src R)
      src.inner.law.toFiniteLaw
      (product (uniform (LiteralEdgeEncoder.Width (2^t) m r)) src.gamma.law).toFiniteLaw
      x ((d+t+ell : ℕ) : ℤ))
    (W : Set (src.Row (ni := 4*(2^t)*(n+(2^t-3))))) (U : Set src.Column)
    (hW : 1-η ≤ (src.rowLaw
      (μI := LiteralEdgeEncoder.indexedItemLaw (2^t) n hs hn)).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U)) :
    d+t+ell+t+1 ≤ Compression.restrictionD
      (fun c a => src.B R (LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ 2^t) edge) a c) U W := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : Nonempty (Fin (4*(2^t))) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (2^t-3)) := ⟨⟨0,by omega⟩⟩
  let ξ₀ : Tail (2^t) (Fin ny) := fun _ => Classical.choice μY.toFiniteLaw.nonempty
  let π := LiteralEdgeEncoder.selectorPermutation (2^t) m r
  let W' := (rowNumber src) ⁻¹' W
  have hW' : 1-η ≤ (Sources.rowLaw (toSources src)
      (DeterministicIndexedMatrix.itemLaw (G := Fin (4*(2^t)))
        (V := Fin n) (A := Fin (2^t-3)))).toFiniteLaw.prob (· ∈ W') := by
    simpa only [W',Set.mem_preimage,row_mass_eq src hs hn W] using hW
  have hU' : 1-η ≤ (V38IndexedTwoTag.law (toSources src)).toFiniteLaw.prob (· ∈ U) := by
    simpa only [columnLaw_eq] using hU
  have hA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A (toSources src) R)
      (toSources src).gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (2^t-2))).prod μX).toFiniteLaw
      x ((d+t : ℕ) : ℤ) := by
    simpa only [product_eq,uniform_eq] using hprofileA
  have hT : V38RestrictionProfiles.TwoThresholdProfile (Sources.T (toSources src) R)
      (toSources src).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (LiteralEdgeEncoder.Width (2^t) m r))).prod
        (toSources src).gamma.law).toFiniteLaw x ((d+t+ell : ℕ) : ℤ) := by
    simpa only [V39GeneratedPrefix.template_eq,product_eq,uniform_eq] using hprofileT
  have hlower := V39IndexedNearFull.restriction_lower (toSources src) hD π
    (LiteralEdgeEncoder.itemOrder (2^t) n) edge loopless hs r Δ hΔ rfl hdegree γ hγ
    (by simpa only [Fintype.card_fin] using hE)
    (by simpa only [Fintype.card_fin] using gap) R ξ₀ d ell hd (by omega) hq₂ hq2
    x ρ η hx hρ hη hηSmall hηTemplate hηAllowance hassign hmargin hsmall hprefixGap
    hdominant hprofileR hA hT W' U hW' hU'
  have hact : (fun i α => EdgeSourceMatrix.activity (LiteralEdgeEncoder.itemOrder (2^t) n)
      edge (by omega : 3 ≤ 2^t) r rfl i (π α)) =
      (fun i α => LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ 2^t) edge
        (LiteralEdgeEncoder.itemNumber (2^t) n i) α) := by
    funext i α
    have h := congrFun (congrFun (LiteralEdgeEncoder.activity_eq_owner
      (r := r) (by omega : 3 ≤ 2^t) edge) i) α
    simpa only [π,LiteralEdgeEncoder.indexedActivity,Equiv.symm_apply_apply,
      SourceCoordinateConjugacy.activityNew] using h.symm
  rw [hact] at hlower
  have he : V38IndexedTwoTag.matrix (toSources src) R
      (fun i α => LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ 2^t) edge
        (LiteralEdgeEncoder.itemNumber (2^t) n i) α) ξ₀ =
      (fun c a => src.B R (LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ 2^t) edge)
        (rowNumber src a) c) := by
    funext c a
    exact matrix_rowNumber src R _ ξ₀ c a
  rw [he] at hlower
  have hcost := restrictionD_pullback_preimage
    (fun c a => src.B R (LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ 2^t) edge) a c)
    id (rowNumber src) Function.surjective_id (rowNumber src).surjective U W
  simpa only [Set.preimage_id_eq] using hcost ▸ hlower

end CurrentAdditive.V39GeneratedNearFull

#print axioms CurrentAdditive.V39GeneratedNearFull.restriction_lower
