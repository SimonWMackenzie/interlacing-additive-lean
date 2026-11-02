import CurrentAdditive.V39RareBoost
import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.IndexedIncomingFin

/-! Actual two-family internal-interlace receipt lower bound. Selected
diagonal image blocks are mapped into the original retained row set and
the fixed metadata/base selector section, with the current Fin 2 profile. -/

namespace CurrentAdditive.V39IndexedIncomingLocal

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

def internal (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    (Fin w × V38IndexedTwoTag.Column src) →
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) → Bool :=
  fun pc t => V38IndexedTwoTag.matrix src R₀ activity ξ₀ pc.2
    (InternalStreams.decode src streams t pc.1)

/-- The single protected receipt is exactly its part of the actual
two-family input law, measured in one-complete-copy units. -/
theorem diagonal_receipt_eq_actual_mass
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (i : Fin w) :
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
        (fun j => (i,Sum.inr j) ∈ R) =
      (V38IndexedTwoTag.law src).toFiniteLaw.prob
        (fun c => match c with
          | .inl _ => False
          | .inr _ => (i,c) ∈ R) := by
  rw [V38IndexedTwoTag.prob_split]
  simp only [FiniteLaw.prob_false,mul_zero,zero_add]
  rfl

/-- A selected diagonal row's entry at a fixed template metadata position
is literally A(gamma,z_i,alpha), independent of that fixed template bin. -/
theorem diagonal_section_entry
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label) (sel : streams.selectorStream.Label)
    (i : Fin w) (α : Fin q₂) (γ : src.gamma.Label) (p : Fin s)
    (hflag : streams.metadataStream.decode md i = .inl p) :
    internal src streams R₀ activity ξ₀ (i,.inr (α,γ)) (md,(base,sel)) =
      A src R₀ γ (src.inner.decode (streams.selectorStream.decode sel i) α) := by
  change V38IndexedTwoTag.matrix src R₀ activity ξ₀ (.inr (α,γ))
    (InternalStreams.decode src streams (md,(base,sel)) i) = _
  simp only [InternalStreams.decode,hflag]
  exact V38IndexedTwoTag.diagonal_template_diagram src R₀ activity ξ₀ p
    (streams.selectorStream.decode sel i) γ α

/-- Current rareboost lower cost on the actual retained two-tag node.
Rows, columns, finite laws and the protocol restriction all stay on the
same indexed source. Source profiles and the one chosen conditional
exception witness are explicit mathematical inputs. -/
theorem selected_diagonal_section_cost
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (md : streams.metadataStream.Label) (base : streams.baseStream.Label)
    (Good E : Finset (Fin (w*q₂))) (d a : ℕ) (x v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob
      (fun γ => ((incomingCoord (q₂ := q₂) (w := w) i).1,
        Sum.inr ((incomingCoord (q₂ := q₂) (w := w) i).2,γ)) ∈ R))
    (hflag : ∀ i ∈ Good, ∃ p : Fin s,
      streams.metadataStream.decode md (incomingCoord (q₂ := q₂) (w := w) i).1 = .inl p)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hsection : v ≤ streams.selectorStream.law.toFiniteLaw.prob
      (fun sel => (md,(base,sel)) ∈ Ystar))
    (hTV : ∀ J : Finset (Fin (w*q₂)), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.selectorStream.law.toFiniteLaw
          (fun sel => (md,(base,sel)) ∈ Ystar) (hv.trans_le hsection))
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
        (incomingDecode src streams) J ≤ V38Moments.epsilon v τ) :
    d+a ≤ Compression.restrictionD (internal src streams R₀ activity ξ₀) R Ystar := by
  classical
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let Rows : Fin (w*q₂) → Set src.gamma.Label :=
    fun i => {γ | ((e i).1,Sum.inr ((e i).2,γ)) ∈ R}
  let K : Set streams.selectorStream.Label := fun sel => (md,(base,sel)) ∈ Ystar
  let S := ArbitraryPrefix.rowRectangle Good Rows
  have hcond : (1/2 : ℝ) ≤
      streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) /
        streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) := by
    have hKpos : 0 < streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) := by
      simpa only [K] using hv.trans_le hsection
    rw [div_self (ne_of_gt hKpos)]
    norm_num
  have hlower := V38RareBoost.rareboost_two_threshold
    src.gamma.law.toFiniteLaw ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
    (A src R₀) streams.selectorStream.law.toFiniteLaw
    (incomingDecode src streams) (incoming_fin_dwise src streams)
    Good E Rows K K d a x v τ ha hd hx hscale hprofile hcount hOutside
    hrow hv hv1 hτ hsection (Set.Subset.rfl) hcond hTV
  let f : (Fin (w*q₂) × src.gamma.Label) →
      (Fin w × V38IndexedTwoTag.Column src) :=
    fun row => ((e row.1).1,Sum.inr ((e row.1).2,row.2))
  let g : streams.selectorStream.Label →
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) :=
    fun sel => (md,(base,sel))
  have hf : Set.MapsTo f S R := by
    intro row hr
    exact hr.2
  have hg : Set.MapsTo g K Ystar := by intro sel hs; exact hs
  have hmap := SourceProjection.restrictionD_map_le
    (internal src streams R₀ activity ξ₀) f g R Ystar S K hf hg
  have heq : Compression.restrictionD
      (fun row sel => A src R₀ row.2 (incomingDecode src streams sel row.1)) S K =
      Compression.restrictionD
        (fun row sel => internal src streams R₀ activity ξ₀ (f row) (g sel)) S K := by
    unfold Compression.restrictionD
    congr 1
    funext row sel
    obtain ⟨p,hp⟩ := hflag row.val.1 row.property.1
    exact (diagonal_section_entry src streams R₀ activity ξ₀ md base sel.val
      (e row.val.1).1 (e row.val.1).2 row.val.2 p hp).symm
  rw [← heq] at hmap
  exact hlower.trans hmap

end CurrentAdditive.V39IndexedIncomingLocal

#print axioms CurrentAdditive.V39IndexedIncomingLocal.diagonal_section_entry
#print axioms CurrentAdditive.V39IndexedIncomingLocal.diagonal_receipt_eq_actual_mass
#print axioms CurrentAdditive.V39IndexedIncomingLocal.selected_diagonal_section_cost
