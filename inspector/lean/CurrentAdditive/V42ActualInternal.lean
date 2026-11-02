import CurrentAdditive.V42IndexedAlignment
import CurrentAdditive.V42ActualItemStreams
import CurrentAdditive.V39RestorationWidth
import CurrentAdditive.V42FullIidRestoration

/-! The common v42 alignment theorem on the literal SourceData matrix and
its original complete-stream labels. The hypotheses concern the source
matrix and scalar margins, never the desired internal W conclusions. -/

namespace CurrentAdditive.V42ActualInternal

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge

private theorem law_ext {A : Type} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by cases μ; cases ν; cases h; rfl

variable {q₁ q₂ s w n nx ny : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def W {μI : PositiveRationalLaw (Fin (4*s*(n+(s-3))))}
    (st : src.Streams (w := w) (μI := μI))
    (R : Fin nx → Fin ny → Bool)
    (act : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s)) :
    st.Label → (Fin w × src.Column) → Bool :=
  fun label row => src.B R act (SourceData.Streams.decode src st label row.1) row.2

variable (hs₄ : 4 ≤ s) (hn : 0 < n)
local notation "S" => toSources src
local notation "μItem" => LiteralEdgeEncoder.itemLaw s n hs₄ hn

/-- Lower bounds for exactly the matrix decoded and printed by SourceData.
The source upper bound remains separate from all NO-side lower inputs. -/
theorem alignment
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn))
    (R₀ : Fin nx → Fin ny → Bool)
    (activity : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s (Fin ny)) (H ell b r e0 : ℕ) (x θ η : ℝ)
    (hH : 2 ≤ H) (hr : 2 ≤ r) (hwr : w=2^r) (hq : q₂=2^ell) (hs : s=2^b)
    (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A S R₀)
      (S).gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T S R₀)
      (S).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod (S).gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (href : V38RestrictionProfiles.TwoThresholdProfile
      (Nref S R₀ (fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α) ξ₀)
      (ordinaryLaw S).toFiniteLaw (rowLaw S μItem).toFiniteLaw x ((H+ell+b : ℕ) : ℤ))
    (hnearfull : ∀ (U : Set src.Column) (Z : Set (src.Row (ni := 4*s*(n+(s-3))))),
      1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn)).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD (fun col row => src.B R₀ activity row col) U Z)
    (hcap : V38Moments.exceptionCount θ (η/2) ≤ e0)
    (hexc : 4*(2*e0) ≤ w)
    (hexcReceipt : (2*(s : ℝ))*(2*e0) ≤ η*w/16)
    (hinit : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hloss : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hforeignWidth : 4*(1/256 : ℝ)*w*q₂*x ≤ η/32)
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hpairMargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairSmall : 2*q₂*x ≤ 1/8)
    (hflag : V42IncomingGuard.flagConstant/(s : ℝ)^128 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hθ1 : θ ≤ 1) (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwxProfile : (w : ℝ)*x < 1/256)
    (hsourceUpper : D (fun col row => src.B R₀ activity row col) ≤ H+ell+b+1) :
    D (W src st R₀ activity) = H+ell+b+1+r ∧
    V38RestrictionProfiles.TwoThresholdProfile (W src st R₀ activity)
      (SourceData.Streams.law src st).toFiniteLaw
      (product (uniform w) src.columnLaw).toFiniteLaw
      θ (((H+ell+b+1+r : ℕ) : ℤ)-1) ∧
    (∀ (U : Set st.Label) (Z : Set (Fin w × src.Column)),
      θ ≤ (SourceData.Streams.law src st).toFiniteLaw.prob (· ∈ U) →
      1-η/(16*w) ≤ (product (uniform w) src.columnLaw).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1+r ≤ Compression.restrictionD (W src st R₀ activity) U Z) := by
  classical
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (NeZero.pos w)
  letI : NeZero w := ⟨by rw [hwr]; positivity⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : Nonempty (Fin (4*s)) := ⟨⟨0,by have hh:=NeZero.pos s; omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0,by omega⟩⟩
  let actG := fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α
  let streams := V42ActualItemStreams.toItemStreams src hs₄ hn st
  let N := V38IndexedTwoTag.matrix S R₀ actG ξ₀
  let Nphys := fun col row => src.B R₀ activity row col
  have hsource : ∀ (U : Set (V38IndexedTwoTag.Column S))
      (Z : Set (Row (I := LiteralEdgeEncoder.Items s n) S)),
      1-η ≤ (V38IndexedTwoTag.law S).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (rowLaw S μItem).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD N U Z := by
    intro U Z hU hZ
    let Zphys := V39IndexedItemNumber.rowNumber src '' Z
    have hpred : (fun a => V39IndexedItemNumber.rowNumber src a ∈ Zphys)=(fun a => a ∈ Z) := by
      funext a
      apply propext
      constructor
      · rintro ⟨b,hb,heq⟩
        exact (V39IndexedItemNumber.rowNumber src).injective heq ▸ hb
      · intro ha; exact ⟨a,ha,rfl⟩
    have hmass := V39IndexedItemNumber.row_mass_eq src hs₄ hn Zphys
    rw [V39IndexedItemNumber.itemLaw_eq s n hs₄ hn,hpred] at hmass
    have hZphys : 1-η ≤
        (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn)).toFiniteLaw.prob (· ∈ Zphys) := by
      rw [← hmass]
      exact hZ
    have hUphys : 1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U) := by
      rw [← columnLaw_eq src]
      exact hU
    have hlower := hnearfull U Zphys hUphys hZphys
    have hproject := SourceProjection.restrictionD_projected_le N Nphys id
      (V39IndexedItemNumber.rowNumber src) U Z U (by intro a ha; exact ha)
      (fun a _ b _ => V39IndexedItemNumber.matrix_rowNumber src R₀ activity ξ₀ a b)
    exact hlower.trans hproject
  have hu : D N ≤ H+ell+b+1 := by
    have hpull := Workspace.ProofLemmas.SublemmaPrecompNoIncrease Nphys id
      (V39IndexedItemNumber.rowNumber src)
    have heq : (fun col row => Nphys (id col) (V39IndexedItemNumber.rowNumber src row))=N := by
      funext col row
      exact (V39IndexedItemNumber.matrix_rowNumber src R₀ activity ξ₀ col row).symm
    rw [heq] at hpull
    exact hpull.trans hsourceUpper
  have hcommon := V42IndexedAlignment.alignment S μItem streams R₀ actG ξ₀
    H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη hA hT href hsource
    hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth hfloor hpairMargin
    hsmall hpairSmall hflag hException hθ1 he hwxProfile hu
  have hWeq : V39TwoTagOwnerEmbedding.actualW S streams R₀ actG ξ₀ = W src st R₀ activity := by
    funext label row
    exact V42ActualItemStreams.internal_entry_eq src hs₄ hn st R₀ activity ξ₀ label row
  have hlaw := V42ActualItemStreams.law_eq src hs₄ hn st
  have hcol : ((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law S)) =
      product (uniform w) src.columnLaw := by
    exact (congrArg₂ (fun a b => PositiveRationalLaw.prod a b)
      (uniform_eq w).symm (columnLaw_eq src)).trans (product_eq _ _).symm
  rcases hcommon with ⟨hcost,hprofile,hnear⟩
  rw [hWeq] at hcost hprofile hnear
  refine ⟨hcost,?_,?_⟩
  · simpa only [hlaw,hcol] using hprofile
  · intro U Z hU hZ
    apply hnear Z U
    · simpa only [V39IndexedTwoFamilyRun.firstRowLaw,hcol] using hZ
    · simpa only [hlaw] using hU


/-- The actual seventh indexed source restores the deletion bounds on the
same successor printed by SourceData. -/
theorem indexed_restoration
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn))
    (R₀ : Fin nx → Fin ny → Bool)
    (activity : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s (Fin ny)) (H ell b r e0 : ℕ) (x θ η : ℝ)
    (hH : 2 ≤ H) (hr : 2 ≤ r) (hwr : w=2^r) (hq : q₂=2^ell) (hs : s=2^b)
    (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A S R₀)
      (S).gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T S R₀)
      (S).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod (S).gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (href : V38RestrictionProfiles.TwoThresholdProfile
      (Nref S R₀ (fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α) ξ₀)
      (ordinaryLaw S).toFiniteLaw (rowLaw S μItem).toFiniteLaw x ((H+ell+b : ℕ) : ℤ))
    (hnearfull : ∀ (U : Set src.Column) (Z : Set (src.Row (ni := 4*s*(n+(s-3))))),
      1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn)).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD (fun col row => src.B R₀ activity row col) U Z)
    (hcap : V38Moments.exceptionCount θ (η/2) ≤ e0)
    (hexc : 4*(2*e0) ≤ w)
    (hexcReceipt : (2*(s : ℝ))*(2*e0) ≤ η*w/16)
    (hinit : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hloss : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hforeignWidth : 4*(1/256 : ℝ)*w*q₂*x ≤ η/32)
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hpairMargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairSmall : 2*q₂*x ≤ 1/8)
    (hflag : V42IncomingGuard.flagConstant/(s : ℝ)^128 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hθ1 : θ ≤ 1) (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwxProfile : (w : ℝ)*x < 1/256)
    (hsourceUpper : D (fun col row => src.B R₀ activity row col) ≤ H+ell+b+1)
    (Q rQ : ℕ) [NeZero Q]
    (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (hQr : Q=2^rQ) (φ : ℝ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hrestorationWidth : 128*((V38Moments.exceptionCount φ ((η/(16*w))/2):ℝ)+1) ≤ Q)
    (hrestorationScale : (Q : ℝ)*θ ≤ 1/20) :
    D (src.successor st out R₀ activity) = H+ell+b+1+r+rQ ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (src.successor st out R₀ activity) out.law.toFiniteLaw
      (product (uniform Q) (SourceData.Streams.law src st)).toFiniteLaw
      φ ((H+ell+b+1+r+rQ:ℕ):ℤ) := by
  classical
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (NeZero.pos w)
  have hW := alignment src hs₄ hn st R₀ activity ξ₀ H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη
    hA hT href hnearfull hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth
    hfloor hpairMargin hsmall hpairSmall hflag hException hθ1 he hwxProfile hsourceUpper
  let C := H+ell+b+1+r
  have hC : 3 ≤ C := by dsimp [C]; omega
  have hprofile : V38RestrictionProfiles.TwoThresholdProfile (W src st R₀ activity)
      (SourceData.Streams.law src st).toFiniteLaw
      (product (uniform w) src.columnLaw).toFiniteLaw θ ((C-1:ℕ):ℤ) := by
    convert hW.2.1 using 1 <;> dsimp [C] <;> omega
  have hδ : 0 < η/(16*(w:ℝ)) := div_pos hη (by positivity)
  have hrest := V39TwoThresholdRestoration.restored_width
    (SourceData.Streams.law src st) (product (uniform w) src.columnLaw)
    (W src st R₀ activity) Q rQ C θ φ (η/(16*w)) out.source hQr
    hC hW.1 hθ hφ hφ1 hδ hrestorationWidth hrestorationScale hW.2.2 hprofile
  change D (src.successor st out R₀ activity) = C+rQ ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (src.successor st out R₀ activity) out.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin Q)).prod (SourceData.Streams.law src st)).toFiniteLaw
      φ ((C+rQ:ℕ):ℤ) at hrest
  have hlaw : ((PositiveRationalLaw.uniform (Fin Q)).prod (SourceData.Streams.law src st)) =
      product (uniform Q) (SourceData.Streams.law src st) := by
    rw [← uniform_eq]
    exact (product_eq _ _).symm
  rw [hlaw] at hrest
  exact hrest


/-- Full-product outer restoration on the same actual internal W. -/
theorem full_restoration
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn))
    (R₀ : Fin nx → Fin ny → Bool)
    (activity : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s (Fin ny)) (H ell b r e0 : ℕ) (x θ η : ℝ)
    (hH : 2 ≤ H) (hr : 2 ≤ r) (hwr : w=2^r) (hq : q₂=2^ell) (hs : s=2^b)
    (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A S R₀)
      (S).gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T S R₀)
      (S).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod (S).gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (href : V38RestrictionProfiles.TwoThresholdProfile
      (Nref S R₀ (fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α) ξ₀)
      (ordinaryLaw S).toFiniteLaw (rowLaw S μItem).toFiniteLaw x ((H+ell+b : ℕ) : ℤ))
    (hnearfull : ∀ (U : Set src.Column) (Z : Set (src.Row (ni := 4*s*(n+(s-3))))),
      1-η ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs₄ hn)).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD (fun col row => src.B R₀ activity row col) U Z)
    (hcap : V38Moments.exceptionCount θ (η/2) ≤ e0)
    (hexc : 4*(2*e0) ≤ w)
    (hexcReceipt : (2*(s : ℝ))*(2*e0) ≤ η*w/16)
    (hinit : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hloss : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hforeignWidth : 4*(1/256 : ℝ)*w*q₂*x ≤ η/32)
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hpairMargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairSmall : 2*q₂*x ≤ 1/8)
    (hflag : V42IncomingGuard.flagConstant/(s : ℝ)^128 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hθ1 : θ ≤ 1) (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwxProfile : (w : ℝ)*x < 1/256)
    (hsourceUpper : D (fun col row => src.B R₀ activity row col) ≤ H+ell+b+1)
    (rQ bOuter : ℕ) (hbOuter : 1 ≤ bOuter)
    (hδSmall : η/(16*(w:ℝ)) ≤ 1/64)
    (hrestorationWidth : 80*(bOuter:ℝ) ≤ (2:ℝ)^rQ*(η/(16*w)))
    (hrestorationScale : (2:ℝ)^rQ*θ ≤ 1/20) :
    D (V39FullIidRestoration.restored (W src st R₀ activity) rQ) = H+ell+b+1+r+rQ ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (V39FullIidRestoration.restored (W src st R₀ activity) rQ)
      ((product (uniform w) src.columnLaw).toFiniteLaw.iid (2^rQ))
      ((FiniteLaw.uniformFin (2^rQ) (Nat.two_pow_pos rQ)).prod
        (SourceData.Streams.law src st).toFiniteLaw)
      ((2:ℝ)^(-(bOuter:ℝ))) ((H+ell+b+1+r+rQ:ℕ):ℤ) := by
  classical
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (NeZero.pos w)
  letI : Nonempty st.Label := (SourceData.Streams.law src st).nonempty
  letI : Nonempty (Fin w × src.Column) := (product (uniform w) src.columnLaw).nonempty
  have hW := alignment src hs₄ hn st R₀ activity ξ₀ H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη
    hA hT href hnearfull hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth
    hfloor hpairMargin hsmall hpairSmall hflag hException hθ1 he hwxProfile hsourceUpper
  have hnear : RestrictionLowerBound (W src st R₀ activity)
      (SourceData.Streams.law src st).toFiniteLaw
      (product (uniform w) src.columnLaw).toFiniteLaw θ (1-η/(16*w))
      (D (W src st R₀ activity):ℤ) := by
    intro U Z hU hZ
    rw [hW.1]
    exact_mod_cast hW.2.2 U Z hU hZ
  have hprofile : V38RestrictionProfiles.TwoThresholdProfile (W src st R₀ activity)
      (SourceData.Streams.law src st).toFiniteLaw
      (product (uniform w) src.columnLaw).toFiniteLaw θ ((D (W src st R₀ activity):ℤ)-1) := by
    rw [hW.1]
    exact hW.2.1
  have hrest := V42FullIidRestoration.rational_restoration
    (SourceData.Streams.law src st) (product (uniform w) src.columnLaw)
    (W src st R₀ activity) rQ bOuter θ (η/(16*w))
    (by rw [hW.1]; omega) hbOuter hθ (div_pos hη (by positivity)) hδSmall
    hrestorationWidth hrestorationScale hnear hprofile
  simpa only [hW.1] using hrest

end CurrentAdditive.V42ActualInternal

#print axioms CurrentAdditive.V42ActualInternal.alignment


#print axioms CurrentAdditive.V42ActualInternal.indexed_restoration
#print axioms CurrentAdditive.V42ActualInternal.full_restoration


