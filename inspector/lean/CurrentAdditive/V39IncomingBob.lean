import CurrentAdditive.V39IncomingSharpBound
import Paper2.ReferenceColumnStep

namespace CurrentAdditive.V39IncomingBob

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- A genuine Bob query chooses its denser original indexed child before
any metadata/base selection. The query's bit charge supplies the strict
local budget used by the sharp 512*mu receipt contradiction. -/
theorem first_bob_diagonal_mass_lt
    (r κ d a : ℕ) (x θ : ℝ)
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (query : (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) → Bool)
    (left right : Protocol (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (hw : w = 2^r) (hκ : 1 ≤ κ) (ha : 1 ≤ a) (hd : 2 ≤ d)
    (hpow : 2^a = 2*s*κ*q₂) (hx : 0 < x) (hθ : 0 < θ)
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (d : ℤ))
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hguard : ∀ m : ℕ, 256*(s : ℝ)*κ ≤ m →
      2*((64 : ℝ)*m)^128 / (((255/256 : ℝ)-1/2)*m)^256 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      (Protocol.bNode query left right).eval row t =
        V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀ row t)
    (hcost : (Protocol.bNode query left right).cost ≤ d+a) :
    ∑ i ∈ I₀, V39IncomingDensity.receipt (diagonalLaw src).toFiniteLaw w R i <
      512*(1/256 : ℝ)*(r+2)*s*κ := by
  classical
  obtain ⟨b,hb⟩ := ReferenceColumnStep.exists_dense_projected_child
    streams.law.toFiniteLaw id Yevent query θ (by simpa only [Set.image_id] using hY)
  have hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob
      (· ∈ ReferenceColumnStep.columnChild Yevent query b) := by
    simpa only [Set.image_id] using hb
  have hchild := ReferenceColumnStep.restriction_add_one_le
    (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀)
    R Yevent query left right hcompute b
  have hnode : Compression.restrictionD
      (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀) R
      (ReferenceColumnStep.columnChild Yevent query b) < d+a := by omega
  exact V39IncomingSharpBound.incoming_diagonal_mass_lt src streams
    r κ d a x θ R I₀ (ReferenceColumnStep.columnChild Yevent query b)
    R₀ activity ξ₀ hw hκ ha hd hpow hx hθ hwidth hprofile hYstar
    hguard hException hnode

end CurrentAdditive.V39IncomingBob

#print axioms CurrentAdditive.V39IncomingBob.first_bob_diagonal_mass_lt
