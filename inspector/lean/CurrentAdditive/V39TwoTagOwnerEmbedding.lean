import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.GeneratedOwnerTuple
import Lean.Util.CollectAxioms

/-! Pure pointwise embedding for v39 `res:foreign` and the two-stream
receipt proof. The target column alphabet has only the selected ordinary
and diagonal tags. Every map below uses original retained labels. -/

namespace CurrentAdditive.V39TwoTagOwnerEmbedding

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- The actual current two-tag W matrix. The original source's W is used
only as its pointwise entry evaluator; its old third tag is not an input. -/
def actualW (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (t : InternalLabel src streams)
    (row : Fin w × V38IndexedTwoTag.Column src) : Bool :=
  Sources.W src streams R₀ activity ξ₀ t
    (row.1, V38IndexedTwoTag.oldTag src row.2)

/-- An ordinary original label is evaluated at its owner copy. -/
theorem ordinary_entry
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i)
    (o : src.outer.Label × src.gamma.Label) :
    actualW src streams R₀ activity ξ₀ r.val (i, .inl o) =
      ownerRectangle src streams R₀ activity ξ₀ i j r (.inl o) := rfl

/-- A diagonal original label is evaluated at its foreign source copy. -/
theorem diagonal_entry
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w) (r : OwnerTemplateTuple src streams i) (f : J src) :
    actualW src streams R₀ activity ξ₀ r.val (j, .inr f) =
      ownerRectangle src streams R₀ activity ξ₀ i j r (.inr f) := rfl

/-- The local two-stream matrix is realised by the same actual retained
input labels. Restriction through these literal maps cannot increase cost.
No probability, profile, or protocol lower-bound premise is used. -/
theorem ownerRectangle_restriction_le_actualW
    (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (V : Set (Fin w × V38IndexedTwoTag.Column src))
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set (J src))
    (hO : ∀ o ∈ O, (i, .inl o) ∈ V)
    (hG : ∀ f ∈ G, (j, .inr f) ∈ V) :
    Compression.restrictionD
      (ownerRectangle src streams R₀ activity ξ₀ i j)
      (ownerRetained src streams i U)
      ((Sum.inl '' O) ∪ (Sum.inr '' G)) ≤
    Compression.restrictionD (actualW src streams R₀ activity ξ₀) U V := by
  classical
  let fr : OwnerTemplateTuple src streams i → InternalLabel src streams :=
    fun r => r.val
  let fc : ((src.outer.Label × src.gamma.Label) ⊕ J src) →
      Fin w × V38IndexedTwoTag.Column src
    | .inl o => (i, .inl o)
    | .inr f => (j, .inr f)
  have hrow : Set.MapsTo fr (ownerRetained src streams i U) U := by
    intro r hr
    exact hr
  have hcol : Set.MapsTo fc (TwoStreamInitial.retainedColumns O G) V := by
    intro c hc
    rcases c with o | f
    · exact hO o ((TwoStreamInitial.inl_mem O G o).mp hc)
    · exact hG f ((TwoStreamInitial.inr_mem O G f).mp hc)
  have h := SourceProjection.restrictionD_map_le
    (actualW src streams R₀ activity ξ₀) fr fc U V
    (ownerRetained src streams i U)
    (TwoStreamInitial.retainedColumns O G) hrow hcol
  have heq : (fun r c => actualW src streams R₀ activity ξ₀ (fr r) (fc c)) =
      ownerRectangle src streams R₀ activity ξ₀ i j := by
    funext r c
    cases c <;> rfl
  rw [heq] at h
  exact h

#print axioms actualW
#print axioms ordinary_entry
#print axioms diagonal_entry
#print axioms ownerRectangle_restriction_le_actualW

end CurrentAdditive.V39TwoTagOwnerEmbedding

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if (`CurrentAdditive.V39TwoTagOwnerEmbedding).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
  if declarations == 0 || theorems == 0 then
    throwError "Empty actual two-tag embedding proof import"
  logInfo m!"Two-tag owner embedding audit: {declarations} declarations, {theorems} theorems; only permitted axioms."
