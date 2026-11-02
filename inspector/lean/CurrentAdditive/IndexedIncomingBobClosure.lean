import CurrentAdditive.IndexedOwnerLocalCost

/-! The genuine first-Bob child selection and bit charge for the indexed
incoming protected-mass contradiction. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- Appendix I `det:incoming` at a genuine first-Bob node.  A child with
at least half of the full retained stream mass is selected inside the proof;
the query bit gives exactly the strict upper cost used to contradict the
source A rareboost lower bound. -/
theorem incoming_protected_mass_first_bob_lt
    (r κ H₁ a : ℕ) (x θ : ℝ)
    (R : Set (Fin w × Column src)) (I₀ : Finset (Fin w))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (query : (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) → Bool)
    (left right : Workspace.Types.Protocol.Protocol
      (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (hw : w = 2^r) (hs : 0 < s) (hκ : 1 ≤ κ)
    (ha : 1 ≤ a) (hd : 2 ≤ H₁) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x (H₁ : ℤ))
    (hblocks : 2^(a-1) ≤ s*κ*q₂)
    (hδscale : ∀ j : Fin (r+2),
      (2 : ℝ)^a * x ≤ ((1/2 : ℝ)^j.val)/4)
    (hθ : 0 < θ)
    (hYevent : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hguard : ∀ m : ℕ,
      256 * (s : ℝ) * κ ≤ m →
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ θ/4)
    (hException : ∀ j : Fin (r+2),
      conditioningExceptionCountR 1024 (θ/4)
        (((1/2 : ℝ)^j.val)/2) ≤ s*q₂)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t =
        W src streams R₀ activity ξ₀ t row)
    (hcost : (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H₁+a) :
    ∑ i ∈ I₀, protectedReceipt src w R i <
      1024 * (1/256 : ℝ) * (r+2) * s * κ := by
  obtain ⟨b, _hsub, hmass⟩ := owner_dense_bob_child src streams
    Yevent query (lt_of_lt_of_le hθ hYevent)
  let Ystar := Paper2.ReferenceColumnStep.columnChild Yevent query b
  have hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar) := by
    have hp := streams.law.toFiniteLaw.prob_nonneg (· ∈ Yevent)
    have hratio := (le_div_iff₀ (lt_of_lt_of_le hθ hYevent)).mp hmass
    nlinarith
  have hnode := owner_bob_child_budget src streams R₀ activity ξ₀
    R Yevent query left right H₁ a hcompute hcost b
  exact incoming_protected_mass_lt src streams r κ H₁ a x θ R I₀
    Ystar R₀ activity ξ₀ hw hs hκ ha hd hx hscale hprofile
    hblocks hδscale hθ hYstar hguard hException hnode

#print axioms incoming_protected_mass_first_bob_lt

end CurrentAdditive.DeterministicIndexedMatrix.Sources
