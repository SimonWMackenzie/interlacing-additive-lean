import CurrentAdditive.V39FullProductStreams
import CurrentAdditive.V39TwoTagOwnerEmbedding
import Lean.Util.CollectAxioms

/-!
Selected v39 main.tex, `sec:internal-interlace`, auxiliary-space paragraph:
the independent complete-stream representation is an auxiliary probability
space for full products. Its decoder can forget unused values. Exact laws,
pointwise protocol simulation and restriction costs are transported along
that decoder; no bijection or enlargement of the printed alphabet is used.
-/

namespace CurrentAdditive.V39FullProductSources

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

/-- Exact pushforward to a positive finite law forces every target label
to have a preimage, but places no injectivity requirement on the decoder. -/
theorem surjective_of_positive_pushes
    {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : PositiveRationalLaw B) (f : A → B)
    (hf : μ.PushesTo ν.toFiniteLaw f) : Function.Surjective f := by
  classical
  intro b
  by_contra hn
  have he : (fun a => f a = b) = (fun _ : A => False) := by
    funext a
    apply propext
    exact ⟨fun h => hn ⟨a,h⟩, False.elim⟩
  have h := hf (fun y => y = b)
  rw [he, FiniteLaw.prob_false, FiniteLaw.prob_singleton] at h
  have hp : 0 < ν.toFiniteLaw.weight b := by
    change (0 : ℝ) < (ν.weight b : ℝ)
    exact_mod_cast ν.positive b
  linarith

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)

theorem columnMap_surjective : Function.Surjective
    (columnMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :=
  surjective_of_positive_pushes _ _ _ (tagged_pushes (D := D) μX μY)

/-- Copy labels are retained exactly; only the unused ordinary head is
forgotten by the column decoder. -/
noncomputable def copyColumnMap {w : ℕ}
    (pc : Fin w × V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) :
    Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y :=
  (pc.1, columnMap (D := D) μX μY pc.2)

theorem copyColumnMap_surjective {w : ℕ} : Function.Surjective
    (copyColumnMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) μX μY) := by
  rintro ⟨i,c⟩
  obtain ⟨a,ha⟩ := columnMap_surjective (D := D) μX μY c
  exact ⟨(i,a), Prod.ext rfl ha⟩

theorem copyColumn_pushes {w : ℕ} [NeZero w] :
    ((PositiveRationalLaw.uniform (Fin w)).prod
      (V38IndexedTwoTag.law
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))).toFiniteLaw.PushesTo
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY)).toFiniteLaw)
      (copyColumnMap (D := D) μX μY) := by
  intro E
  rw [PositiveRationalLaw.toFiniteLaw_prod, PositiveRationalLaw.toFiniteLaw_prod]
  change (_ : FiniteLaw (Fin w × V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))).prob
      (fun z => E (z.1, columnMap (D := D) μX μY z.2)) =
    (_ : FiniteLaw (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y)).prob
      (fun z => E (z.1,z.2))
  rw [FiniteLaw.prod_prob (PositiveRationalLaw.uniform (Fin w)).toFiniteLaw
      (V38IndexedTwoTag.law
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)).toFiniteLaw
      (fun i c => E (i, columnMap (D := D) μX μY c)),
    FiniteLaw.prod_prob (PositiveRationalLaw.uniform (Fin w)).toFiniteLaw
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY).toFiniteLaw
      (fun i c => E (i,c))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact tagged_pushes (D := D) μX μY (fun c => E (i,c))

/-- The original full-product W, on its original tuple and copy-column
alphabets. This definition is only an entry-level abbreviation. -/
def fullW {w : ℕ} (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    (Fin w → RawRow q₁ q₂ s X I) →
      (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) → Bool :=
  fun t pc => raw R activity (t pc.1) (V38Matrix.forgetTag ξ₀ pc.2)

theorem fullW_eq_transpose_interlace {w : ℕ} (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    fullW (q₁ := q₁) (w := w) R activity ξ₀ =
      fun t pc => fullInterlace
        (fun c a => raw R activity a (V38Matrix.forgetTag ξ₀ c)) w pc t := rfl

/-- The actual two-family indexed W has exactly the decoded full-product
entry at every pair of labels. This includes all ignored stream values. -/
theorem actualW_entry (μI : PositiveRationalLaw I) (w : ℕ)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (t : InternalLabel
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (fullStreams (D := D) μX μY μI w))
    (pc : Fin w × V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) :
    V39TwoTagOwnerEmbedding.actualW _
      (fullStreams (D := D) μX μY μI w) R activity ξ₀ t pc =
    fullW R activity ξ₀ (tupleMap (D := D) μX μY μI w t)
      (copyColumnMap (D := D) μX μY pc) := by
  change V38IndexedTwoTag.matrix _ R activity ξ₀ pc.2
      (InternalStreams.decode _ _ t pc.1) =
    raw R activity (Sources.decodeRow _ (InternalStreams.decode _ _ t pc.1))
      (V38Matrix.forgetTag ξ₀ (columnMap (D := D) μX μY pc.2))
  rw [decodeRow_eq_rowEquiv]
  exact matrix_entry μX μY R activity ξ₀ pc.2 _

noncomputable def pullbackProtocol (μI : PositiveRationalLaw I) (w : ℕ)
    (P : Protocol (Fin w → RawRow q₁ q₂ s X I)
      (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) Bool) :
    Protocol
      (InternalLabel
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
        (fullStreams (D := D) μX μY μI w))
      (Fin w × V38IndexedTwoTag.Column
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) Bool :=
  Workspace.UpperBound.Protocol.comap
    (tupleMap (D := D) μX μY μI w) (copyColumnMap (D := D) μX μY) P

theorem pullbackProtocol_cost (μI : PositiveRationalLaw I) (w : ℕ)
    (P : Protocol (Fin w → RawRow q₁ q₂ s X I)
      (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) Bool) :
    (pullbackProtocol (D := D) μX μY μI w P).cost = P.cost :=
  Workspace.UpperBound.Protocol.comap_cost _ _ _

theorem pullbackProtocol_eval (μI : PositiveRationalLaw I) (w : ℕ)
    (P : Protocol (Fin w → RawRow q₁ q₂ s X I)
      (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (t : InternalLabel
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (fullStreams (D := D) μX μY μI w))
    (pc : Fin w × V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) :
    (pullbackProtocol (D := D) μX μY μI w P).eval t pc =
      P.eval (tupleMap (D := D) μX μY μI w t)
        (copyColumnMap (D := D) μX μY pc) :=
  Workspace.UpperBound.Protocol.comap_eval _ _ _ _ _

theorem pullbackProtocol_computes (μI : PositiveRationalLaw I) (w : ℕ)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (P : Protocol (Fin w → RawRow q₁ q₂ s X I)
      (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (hP : P.Computes (fullW R activity ξ₀)) :
    (pullbackProtocol (D := D) μX μY μI w P).Computes
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) μX μY μI w) R activity ξ₀) := by
  intro t pc
  rw [pullbackProtocol_eval, actualW_entry]
  exact hP _ _

/-- Arbitrary surviving auxiliary labels map to their actual images.
No Cartesian closure or inclusion of unused stream data is assumed. -/
theorem actualW_restriction_image (μI : PositiveRationalLaw I) (w : ℕ)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U : Set (InternalLabel
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (fullStreams (D := D) μX μY μI w)))
    (V : Set (Fin w × V38IndexedTwoTag.Column
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))) :
    Compression.restrictionD
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) μX μY μI w) R activity ξ₀) U V =
      Compression.restrictionD (fullW R activity ξ₀)
        (tupleMap (D := D) μX μY μI w '' U)
        (copyColumnMap (D := D) μX μY '' V) := by
  have he := funext fun t => funext fun pc =>
    actualW_entry (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w R activity ξ₀ t pc
  rw [he]
  exact restrictionD_pullback_image _ _ _ U V

section GraphItems

variable {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  (μI : PositiveRationalLaw (G × (V ⊕ Aux))) (w : ℕ)

theorem tupleMap_surjective : Function.Surjective
    (tupleMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) := by
  apply surjective_of_positive_pushes _
    ((rowLaw
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).iid w)
  simpa only [PositiveRationalLaw.toFiniteLaw_iid] using
    tuple_pushes (D := D) μX μY μI w

/-- Pulling back any event on the original tuple alphabet preserves its
ambient mass. In particular this applies after a Bob-child event is chosen. -/
theorem tuple_event_prob
    (E : (Fin w → RawRow q₁ q₂ s X (G × (V ⊕ Aux))) → Prop) :
    (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w).law.toFiniteLaw.prob
      (fun t => E (tupleMap (D := D) μX μY μI w t)) =
      ((rowLaw
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).toFiniteLaw.iid w).prob E :=
  tuple_pushes (D := D) μX μY μI w E

/-- A protocol restricted to original inputs has exactly the same optimal
depth after all their auxiliary preimages are retained. -/
theorem actualW_restriction_preimage
    (R : X → Y → Bool) (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U : Set (Fin w → RawRow q₁ q₂ s X (G × (V ⊕ Aux))))
    (V₀ : Set (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y)) :
    Compression.restrictionD
      (V39TwoTagOwnerEmbedding.actualW _
        (fullStreams (D := D) μX μY μI w) R activity ξ₀)
      (tupleMap (D := D) μX μY μI w ⁻¹' U)
      (copyColumnMap (D := D) μX μY ⁻¹' V₀) =
    Compression.restrictionD (fullW R activity ξ₀) U V₀ := by
  rw [actualW_restriction_image,
    Set.image_preimage_eq _ (tupleMap_surjective (D := D) μX μY μI w),
    Set.image_preimage_eq _ (copyColumnMap_surjective (D := D) μX μY)]

end GraphItems

#print axioms columnMap_surjective
#print axioms copyColumn_pushes
#print axioms actualW_entry
#print axioms pullbackProtocol_computes
#print axioms tupleMap_surjective
#print axioms tuple_event_prob
#print axioms actualW_restriction_preimage

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
  if count == 0 then throwError "Empty full-product transport audit"
  logInfo m!"Full-product source/stream/transport audit: {count} declarations; only permitted axioms."
