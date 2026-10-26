import CurrentAdditive.V39SharedConditioning
import CurrentAdditive.V39ForeignSameException
import CurrentAdditive.V39IndexedIncomingLocal

/-! The exceptional set is selected before any frontier node, and the
same original event/witness supplies every local foreign receipt. -/

namespace CurrentAdditive.V39SharedReceiptJoin

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39TwoTagOwnerEmbedding

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
  {w : ℕ} (streams : InternalStreams src μI w)

/-- Incoming and foreign receipts use the same pointwise two-tag matrix,
in the two transposed orientations used by their protocol arguments. -/
theorem actualW_eq_internal_transpose (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    actualW src streams R₀ activity ξ₀ =
      fun t row => V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀ row t := rfl

theorem choose_exception_before_nodes
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (Yevent : Set (InternalLabel src streams))
    (H ell b : ℕ) (hH : 2 ≤ H) (hq : q₂=2^ell) (hs : s=2^b)
    (x θ η : ℝ) (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hmargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    ∃ E : Finset (Fin w), E.card ≤ V38Moments.exceptionCount θ (η/2) ∧
      (∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition streams.law.toFiniteLaw (· ∈ Yevent) (hθ.trans_le hY))
          (rowLaw src μI).toFiniteLaw (InternalStreams.decode src streams) J ≤
            conditioningEpsilonR 1024 θ (η/2)) ∧
      (∀ i : Fin w, i ∉ E →
        1-η/2 ≤ (rowLaw src μI).toFiniteLaw.prob
          (· ∈ (fun t => InternalStreams.decode src streams t i) '' Yevent)) ∧
      (∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (99/100 : ℝ) <
          ((rowLaw src μI).toFiniteLaw.prod (rowLaw src μI).toFiniteLaw).prob
            (· ∈ (fun t => (InternalStreams.decode src streams t i,
              InternalStreams.decode src streams t j)) '' Yevent)) ∧
      (∀ (Rnode : Set (Fin w × V38IndexedTwoTag.Column src)) (ε : ℝ)
        (i j : Fin w), i ≠ j → i ∉ E → j ∉ E →
        (1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
          (fun o => (i,.inl o) ∈ Rnode)) →
        (Compression.restrictionD (actualW src streams R₀ activity ξ₀) Yevent Rnode ≤
          H+ell+b) →
        (1/256 : ℝ)*
          (PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
            (fun f => (j,.inr f) ∈ Rnode) ≤ (1/256 : ℝ)*(2*q₂*x+4*ε)) := by
  have hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw :=
    internal_streams_row_dwise src μI streams
  obtain ⟨E,hE,hTV,hsingle,hpair⟩ := V39SharedConditioning.choose_shared_exception
    streams.law.toFiniteLaw (rowLaw src μI).toFiniteLaw
    (InternalStreams.decode src streams) hwise Yevent θ η hθ hη hY
  refine ⟨E,hE,hTV,hsingle,hpair,?_⟩
  intro Rnode ε i j hij hi hj hO hcost
  exact V39ForeignSameException.owner_to_owner_receipt_from_same_E src μI streams
    R₀ activity ξ₀ Yevent Rnode E H ell b hH hq hs x hx hA hT θ η hθ hY hη
    hTV hfloor hmargin ε hsmall hpairsmall i j hij hi hj hO hcost

end CurrentAdditive.V39SharedReceiptJoin

#print axioms CurrentAdditive.V39SharedReceiptJoin.actualW_eq_internal_transpose
#print axioms CurrentAdditive.V39SharedReceiptJoin.choose_exception_before_nodes
