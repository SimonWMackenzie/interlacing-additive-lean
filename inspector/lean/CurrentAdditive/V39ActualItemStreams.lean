import CurrentAdditive.V39GeneratedSourceBridge
import CurrentAdditive.V39IndexedItemNumber
import CurrentAdditive.V39IndexedAlignment

/-! Decode the physical finite item numbers back to graph items while
preserving every original complete-stream index and its exact weight. -/

namespace CurrentAdditive.V39ActualItemStreams

open Paper2 CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge

theorem pi_symm_pushes {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq J] (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (e : A ≃ B) (hweight : ∀ a, ν.weight (e a)=μ.weight a) :
    (FiniteLaw.pi (fun _ : J => ν.toFiniteLaw)).PushesTo
      (FiniteLaw.pi (fun _ : J => μ.toFiniteLaw)) (fun z i => e.symm (z i)) := by
  classical
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro y
  have hev : (fun z : J → B => (fun i => e.symm (z i))=y) =
      (fun z => ∀ i, z i=e (y i)) := by
    funext z
    apply propext
    constructor
    · intro h i
      simpa using congrArg e (congrFun h i)
    · intro h
      funext i
      simp [h i]
  rw [hev]
  rw [show (FiniteLaw.pi (fun _ : J => ν.toFiniteLaw)).prob
      (fun z => ∀ i, z i=e (y i)) = ∏ i, ν.toFiniteLaw.prob (fun z => z=e (y i)) from
    FiniteLaw.pi_prob_coordinatewise (fun _ : J => ν.toFiniteLaw) (fun i z => z=e (y i))]
  simp only [FiniteLaw.prob_singleton,FiniteLaw.pi,PositiveRationalLaw.toFiniteLaw,hweight]

def alphabetEquiv {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {D q : ℕ} (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (e : A ≃ B) (hweight : ∀ a, ν.weight (e a)=μ.weight a)
    (code : CodeSource D q B ν) : CodeSource D q A μ where
  Label := code.Label
  finite := code.finite
  decEq := code.decEq
  law := code.law
  decode label i := e.symm (code.decode label i)
  exactLaw := by
    intro J hJ E
    exact (code.exactLaw J hJ (fun z => E (fun i => e.symm (z i)))).trans
      (pi_symm_pushes μ ν e hweight E)

variable {D q₁ q₂ s nx ny n w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def metadataEquiv :
    (Fin s ⊕ LiteralEdgeEncoder.Items s n) ≃ (Fin s ⊕ Fin (4*s*(n+(s-3)))) :=
  Equiv.sumCongr (Equiv.refl _) (LiteralEdgeEncoder.itemNumber s n)

theorem metadata_weight (hs : 4 ≤ s) (hn : 0 < n)
    (a : Fin s ⊕ LiteralEdgeEncoder.Items s n) :
    (mixture (uniform s) (LiteralEdgeEncoder.indexedItemLaw s n hs hn)).weight
      (metadataEquiv a) =
      (metadataLaw (s := s) (LiteralEdgeEncoder.itemLaw s n hs hn)).weight a := by
  cases a with
  | inl p => simp [mixture,metadataLaw,uniform,PositiveRationalLaw.uniform,metadataEquiv]
  | inr i =>
    simp only [mixture,metadataLaw,metadataEquiv,Equiv.sumCongr_apply,Equiv.refl_apply,
      Sum.map_inr,LiteralEdgeEncoder.indexedItemLaw,Equiv.symm_apply_apply]

noncomputable def toItemStreams (hs : 4 ≤ s) (hn : 0 < n)
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn)) :
    InternalStreams (toSources src) (LiteralEdgeEncoder.itemLaw s n hs hn) w where
  metadataStream := alphabetEquiv _ _ metadataEquiv (metadata_weight hs hn)
    st.metadata.source
  baseStream := st.base.source
  selectorStream := st.selector.source

theorem law_eq (hs : 4 ≤ s) (hn : 0 < n)
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn)) :
    (toItemStreams src hs hn st).law = SourceData.Streams.law src st := by
  let law_ext {A : Type} [Fintype A] (μ ν : PositiveRationalLaw A)
      (h : μ.weight=ν.weight) : μ=ν := by cases μ; cases ν; cases h; rfl
  apply law_ext
  rfl

theorem decode_rowNumber (hs : 4 ≤ s) (hn : 0 < n)
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn))
    (label : st.Label) (i : Fin w) :
    V39IndexedItemNumber.rowNumber src
      (InternalStreams.decode (toSources src) (toItemStreams src hs hn st) label i) =
      SourceData.Streams.decode src st label i := by
  cases h : st.metadata.decode label.1 i <;>
    simp [InternalStreams.decode,toItemStreams,alphabetEquiv,metadataEquiv,
      SourceData.Streams.decode,h,ExactList.source,V39IndexedItemNumber.rowNumber] <;> rfl

theorem internal_entry_eq (hs : 4 ≤ s) (hn : 0 < n)
    (st : src.Streams (w := w) (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s (Fin ny)) (label : st.Label) (a : Fin w × src.Column) :
    V39TwoTagOwnerEmbedding.actualW (toSources src) (toItemStreams src hs hn st) R
      (fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α) ξ₀ label a =
      src.B R activity (SourceData.Streams.decode src st label a.1) a.2 := by
  change V38IndexedTwoTag.matrix (toSources src) R _ ξ₀ a.2 _ = _
  rw [V39IndexedItemNumber.matrix_rowNumber,decode_rowNumber]

end CurrentAdditive.V39ActualItemStreams

#print axioms CurrentAdditive.V39ActualItemStreams.alphabetEquiv
#print axioms CurrentAdditive.V39ActualItemStreams.toItemStreams
#print axioms CurrentAdditive.V39ActualItemStreams.law_eq
#print axioms CurrentAdditive.V39ActualItemStreams.internal_entry_eq
