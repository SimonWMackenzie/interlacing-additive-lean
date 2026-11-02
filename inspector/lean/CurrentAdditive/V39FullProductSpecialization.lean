import CurrentAdditive.V39FullProductTransport
import CurrentAdditive.V38RestrictionProfiles
import CurrentAdditive.DeterministicIndexedProfileEntries

/-! Exact transport of the original full-product source hypotheses and
internal-W conclusions. These are finite law/cost transport lemmas, not
additional lower-bound assumptions or a completion claim. -/

namespace CurrentAdditive.V39FullProductSources

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

theorem twoThreshold_pullback_iff
    {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (μA : FiniteLaw A) (μB : FiniteLaw B) (f : A → X) (g : B → Y)
    (hf : μA.PushesTo μX f) (hg : μB.PushesTo μY g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (θ : ℝ) (H : ℤ) :
    V38RestrictionProfiles.TwoThresholdProfile
      (fun a b => F (f a) (g b)) μA μB θ H ↔
    V38RestrictionProfiles.TwoThresholdProfile F μX μY θ H := by
  unfold V38RestrictionProfiles.TwoThresholdProfile
  apply forall_congr'
  intro j
  exact RestrictionLowerBound.pullback_iff F μX μY μA μB f g
    hf hg hfs hgs _ _ _

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)

theorem matrix_restriction_image
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (U : Set (V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)))
    (Z : Set (Row (I := I)
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))) :
    Compression.restrictionD
      (V38IndexedTwoTag.matrix _ R activity ξ₀) U Z =
    Compression.restrictionD
      (fun c a => raw R activity a (V38Matrix.forgetTag ξ₀ c))
      (columnMap (D := D) μX μY '' U) (rowEquiv (D := D) μX μY '' Z) := by
  have he := funext fun c => funext fun a =>
    matrix_entry (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) (I := I) μX μY R activity ξ₀ c a
  rw [he]
  exact restrictionD_pullback_image
    (fun c a => raw R activity a (V38Matrix.forgetTag ξ₀ c))
    (columnMap (D := D) μX μY) (rowEquiv (D := D) μX μY) U Z

theorem source_nearfull_pullback
    (μK : PositiveRationalLaw (RawRow q₁ q₂ s X I))
    (μIndexed : PositiveRationalLaw (Row (I := I)
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)))
    (hrow : μIndexed.toFiniteLaw.PushesTo μK.toFiniteLaw
      (rowEquiv (D := D) μX μY))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (C : ℕ) (η : ℝ)
    (hnear : ∀ (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
      (Z : Set (RawRow q₁ q₂ s X I)),
      1-η ≤ (V38Matrix.taggedLaw μY).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ μK.toFiniteLaw.prob (· ∈ Z) →
      C ≤ Compression.restrictionD
        (fun c a => raw R activity a (V38Matrix.forgetTag ξ₀ c)) U Z) :
    ∀ (U : Set (V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)))
      (Z : Set (Row (I := I)
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))),
      1-η ≤ (V38IndexedTwoTag.law _).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ μIndexed.toFiniteLaw.prob (· ∈ Z) →
      C ≤ Compression.restrictionD (V38IndexedTwoTag.matrix _ R activity ξ₀) U Z := by
  intro U Z hU hZ
  rw [matrix_restriction_image]
  apply hnear
  · exact hU.trans (FiniteLaw.prob_le_image _ _ _ (tagged_pushes (D := D) μX μY) U)
  · exact hZ.trans (FiniteLaw.prob_le_image _ _ _ hrow Z)

theorem reference_profile_pullback
    (μK : PositiveRationalLaw (RawRow q₁ q₂ s X I))
    (μIndexed : PositiveRationalLaw (Row (I := I)
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)))
    (hrow : μIndexed.toFiniteLaw.PushesTo μK.toFiniteLaw
      (rowEquiv (D := D) μX μY))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (x : ℝ) (H : ℤ)
    (href : V38RestrictionProfiles.TwoThresholdProfile
      (fun c a => raw R activity a c) (SourceLaws.rawLaw μY q₁ q₂ s).toFiniteLaw
      μK.toFiniteLaw x H) :
    V38RestrictionProfiles.TwoThresholdProfile
      (Nref (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) R activity ξ₀)
      (ordinaryLaw _).toFiniteLaw μIndexed.toFiniteLaw x H := by
  have he : Nref (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) R activity ξ₀ =
      fun c a => raw R activity (rowEquiv (D := D) μX μY a) (tail c.2,c.1) := by
    funext c a
    exact matrix_entry μX μY R activity ξ₀ (.inl c) a
  rw [he]
  intro j
  exact RestrictionLowerBound.pullback _ _ _ _ _ _ _
    (ordinary_pushes (D := D) μX μY) hrow _ _ _ (href j)

section Graph

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] [Nonempty Vertex]

theorem graph_row_pushes (hs : 4 ≤ s) :
    (rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (graphItemLaw (Vertex := Vertex) hs)).toFiniteLaw.PushesTo
      (V38Matrix.columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := Vertex) μX hs).toFiniteLaw
      (rowEquiv (D := D) μX μY) := by
  intro E
  change (rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (graphItemLaw (Vertex := Vertex) hs)).toFiniteLaw.prob E = _
  rw [raw_law_eq_current]
  rfl

end Graph

section Internal

variable {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  (μI : PositiveRationalLaw (G × (V ⊕ Aux))) (w : ℕ)

theorem actualW_D_eq (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    Workspace.Types.CommComplexity.D
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) R activity ξ₀) =
    Workspace.Types.CommComplexity.D (fullW (q₁ := q₁) (w := w) R activity ξ₀) := by
  have he := funext fun t => funext fun pc =>
    actualW_entry (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w R activity ξ₀ t pc
  rw [he]
  exact pullback_D_eq_of_surjective _ _ _
    (tupleMap_surjective (D := D) μX μY μI w)
    (copyColumnMap_surjective (D := D) μX μY)

theorem fullW_lowerBound_iff [NeZero w] (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (a b : ℝ) (C : ℤ) :
    RestrictionLowerBound
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) R activity ξ₀)
      (fullStreams (D := D) μX μY μI w).law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law _)).toFiniteLaw) a b C ↔
    RestrictionLowerBound (fullW (q₁ := q₁) (w := w) R activity ξ₀)
      ((rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).toFiniteLaw.iid w)
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY)).toFiniteLaw) a b C := by
  have he := funext fun t => funext fun pc =>
    actualW_entry (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w R activity ξ₀ t pc
  rw [he]
  exact RestrictionLowerBound.pullback_iff _ _ _ _ _ _ _
    (tuple_pushes (D := D) μX μY μI w) (copyColumn_pushes (D := D) μX μY)
    (tupleMap_surjective (D := D) μX μY μI w)
    (copyColumnMap_surjective (D := D) μX μY) a b C

theorem fullW_profile_iff [NeZero w] (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (θ : ℝ) (C : ℤ) :
    V38RestrictionProfiles.TwoThresholdProfile
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) R activity ξ₀)
      (fullStreams (D := D) μX μY μI w).law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law _)).toFiniteLaw) θ C ↔
    V38RestrictionProfiles.TwoThresholdProfile (fullW (q₁ := q₁) (w := w) R activity ξ₀)
      ((rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).toFiniteLaw.iid w)
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY)).toFiniteLaw) θ C := by
  unfold V38RestrictionProfiles.TwoThresholdProfile
  apply forall_congr'
  intro j
  exact fullW_lowerBound_iff (D := D) μX μY μI w R activity ξ₀ _ _ _

end Internal

#print axioms source_nearfull_pullback
#print axioms reference_profile_pullback
#print axioms graph_row_pushes
#print axioms actualW_D_eq
#print axioms fullW_profile_iff

end CurrentAdditive.V39FullProductSources

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`CurrentAdditive.V39FullProductSources).isPrefixOf name then
      count := count + 1
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
  if count == 0 then throwError "Empty specialization audit"
  logInfo m!"Full-product specialization audit: {count} declarations; only permitted axioms."
