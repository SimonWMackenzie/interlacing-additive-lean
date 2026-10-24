import CurrentAdditive.V39ActualGeneratedSource
import CurrentAdditive.V39GeneratedAlignmentGuards

/-! Current internal-interlace theorem specialized to the actual three
computed SourceData streams, original finite labels and passing parameters.
The base matrix profile is the only profile premise. -/

namespace CurrentAdditive.V39ActualGeneratedInternal

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.DeterministicIndexedMatrix CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge
open CurrentAdditive.V39ActualGeneratedSource CurrentAdditive.V39GeneratedAlignmentGuards

private theorem law_ext {A : Type} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by cases μ; cases ν; cases h; rfl

variable {L n m nx ny rep : ℕ}
  [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  [NeZero (generatedW L)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
    (s := generatedS L) μX μY)

def W {μI : PositiveRationalLaw (Fin (4*(generatedS L)*(n+(generatedS L-3))))}
    (st : src.Streams (w := generatedW L) (μI := μI))
    (R : Fin nx → Fin ny → Bool)
    (act : Fin (4*(generatedS L)*(n+(generatedS L-3))) → Fin (generatedQ₂ L) → Option (Fin (generatedS L))) :
    st.Label → (Fin (generatedW L) × src.Column) → Bool :=
  fun label row => src.B R act (SourceData.Streams.decode src st label row.1) row.2

theorem internal_of_tests
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4 ≤ generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ)*m ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ))
    (st : src.Streams (w := generatedW L)
      (μI := LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)) :
    D (W src st R (activity hs hwidth edge)) = sourceCost d L+2*L ∧
    V38RestrictionProfiles.TwoThresholdProfile (W src st R (activity hs hwidth edge))
      (SourceData.Streams.law src st).toFiniteLaw
      (product (uniform (generatedW L)) src.columnLaw).toFiniteLaw
      (Theta L) (((sourceCost d L+2*L : ℕ) : ℤ)-1) ∧
    (∀ (U : Set st.Label) (Z : Set (Fin (generatedW L) × src.Column)),
      Theta L ≤ (SourceData.Streams.law src st).toFiniteLaw.prob (· ∈ U) →
      1-Eta c L/(16*(generatedW L)) ≤
        (product (uniform (generatedW L)) src.columnLaw).toFiniteLaw.prob (· ∈ Z) →
      sourceCost d L+2*L ≤ Compression.restrictionD (W src st R (activity hs hwidth edge)) U Z) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : Nonempty (Fin (4*generatedS L)) := ⟨⟨0,by have hh:=NeZero.pos (generatedS L); omega⟩⟩
  letI : Nonempty (Fin (generatedS L-3)) := ⟨⟨0,by omega⟩⟩
  let μI := LiteralEdgeEncoder.itemLaw (generatedS L) n hs hn
  let act := activity hs hwidth edge
  let actG := fun i α => act (LiteralEdgeEncoder.itemNumber (generatedS L) n i) α
  let ξ₀ : Tail (generatedS L) (Fin ny) := fun _ => Classical.choice μY.nonempty
  let S := toSources src
  let streams := V39ActualItemStreams.toItemStreams src hs hn st
  let N := V38IndexedTwoTag.matrix S R actG ξ₀
  let Nphys := fun col row => src.B R act row col
  have hguards := guards_of_tests c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m hc htests
  obtain ⟨_hDA,_hDT,hA,hT,hRef⟩ := V39GeneratedSourceProfiles.costs_and_profiles_of_tests
    S μI R actG ξ₀ d c (sourceDeltaV γ Δ n m) (sourceZeta γ) m htests hd hD hp
  have href : V38RestrictionProfiles.TwoThresholdProfile (Nref S R actG ξ₀)
      (ordinaryLaw S).toFiniteLaw (rowLaw S μI).toFiniteLaw (X L)
      ((d+quarterCeil L+4*L+quarterCeil L : ℕ) : ℤ) := by
    have hrow : V39IndexedReferenceProfile.rowLaw S μI=Sources.rowLaw S μI := by
      apply law_ext
      funext a
      cases a <;> rfl
    rw [hrow] at hRef
    exact hRef
  have hsource : ∀ (U : Set (V38IndexedTwoTag.Column S)) (Z : Set (Row (I := LiteralEdgeEncoder.Items (generatedS L) n) S)),
      1-Eta c L ≤ (V38IndexedTwoTag.law S).toFiniteLaw.prob (· ∈ U) →
      1-Eta c L ≤ (rowLaw S μI).toFiniteLaw.prob (· ∈ Z) →
      sourceCost d L ≤ Compression.restrictionD N U Z := by
    intro U Z hU hZ
    let Zphys := V39IndexedItemNumber.rowNumber src '' Z
    have hpred : (fun a => V39IndexedItemNumber.rowNumber src a ∈ Zphys)=(fun a => a ∈ Z) := by
      funext a
      apply propext
      constructor
      · rintro ⟨b,hb,heq⟩
        exact (V39IndexedItemNumber.rowNumber src).injective heq ▸ hb
      · intro ha; exact ⟨a,ha,rfl⟩
    have hmass := V39IndexedItemNumber.row_mass_eq src hs hn Zphys
    rw [V39IndexedItemNumber.itemLaw_eq (generatedS L) n hs hn,hpred] at hmass
    have hZphys : 1-Eta c L ≤
        (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)).toFiniteLaw.prob (· ∈ Zphys) := by
      rw [← hmass]
      exact hZ
    have hUphys : 1-Eta c L ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U) := by
      rw [← columnLaw_eq src]
      exact hU
    have hlower := nearfull_of_tests src γ c Δ hc hγ hΔ hn hm htests hs hwidth
      edge loopless hdegree gap R d hd hD hp Zphys U hZphys hUphys
    have hproject := SourceProjection.restrictionD_projected_le N Nphys id
      (V39IndexedItemNumber.rowNumber src) U Z U (by intro a ha; exact ha)
      (fun a _ b _ => V39IndexedItemNumber.matrix_rowNumber src R act ξ₀ a b)
    exact hlower.trans hproject
  have hsourceUpper : D N ≤ sourceCost d L := by
    have hpull := Workspace.ProofLemmas.SublemmaPrecompNoIncrease Nphys id
      (V39IndexedItemNumber.rowNumber src)
    have heq : (fun col row => Nphys (id col) (V39IndexedItemNumber.rowNumber src row))=N := by
      funext col row
      exact (V39IndexedItemNumber.matrix_rowNumber src R act ξ₀ col row).symm
    rw [heq] at hpull
    exact hpull.trans (source_upper src hs hwidth edge R d hD)
  have hcommon := V39IndexedAlignment.alignment S μI streams R actG ξ₀
    (d+quarterCeil L) (4*L) (quarterCeil L) (2*L)
    (e0 (generatedQlog L) (generatedEta c L)) (X L) (Theta L) (Eta c L)
    (by omega) hguards.r_ge hguards.w_pow hguards.q_pow hguards.s_pow
    hguards.x_pos hguards.theta_pos hguards.eta_pos hA hT href hsource
    hguards.cap hguards.exc hguards.receipt hguards.init hguards.wx hguards.two_x
    hguards.loss hguards.width hguards.foreign hguards.floor hguards.pair_margin
    hguards.small hguards.pair_small hguards.flag hguards.exception hguards.theta_le_one
    hguards.profile_exception hguards.profile_wx hsourceUpper
  have hWeq : V39TwoTagOwnerEmbedding.actualW S streams R actG ξ₀ = W src st R act := by
    funext label row
    exact V39ActualItemStreams.internal_entry_eq src hs hn st R act ξ₀ label row
  have hlaw := V39ActualItemStreams.law_eq src hs hn st
  have hcol : ((PositiveRationalLaw.uniform (Fin (generatedW L))).prod (V38IndexedTwoTag.law S)) =
      product (uniform (generatedW L)) src.columnLaw := by
    exact (congrArg₂ (fun a b => PositiveRationalLaw.prod a b)
      (uniform_eq (generatedW L)).symm (columnLaw_eq src)).trans (product_eq _ _).symm
  rcases hcommon with ⟨hcost,hprofile,hnear⟩
  rw [hWeq] at hcost hprofile hnear
  refine ⟨hcost,?_,?_⟩
  · simpa only [hlaw,hcol,sourceCost] using hprofile
  · intro U Z hU hZ
    apply hnear Z U
    · simpa only [V39IndexedTwoFamilyRun.firstRowLaw,hcol] using hZ
    · simpa only [hlaw] using hU

end CurrentAdditive.V39ActualGeneratedInternal

#print axioms CurrentAdditive.V39ActualGeneratedInternal.internal_of_tests
