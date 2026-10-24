import CurrentAdditive.V40StoredLawOperations

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40NumberedLawAlgebra
open Paper2 V39GeneratedConstruction
noncomputable section

theorem law_ext {A : Type*} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by
  cases μ
  cases ν
  cases h
  rfl

def prod {m n : ℕ} (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)) :=
  reindex finProdFinEquiv (product μ ν)
def mix {m n : ℕ} (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)) :=
  reindex finSumFinEquiv (mixture μ ν)

theorem reindex_refl {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    reindex (Equiv.refl _) μ=μ := by
  apply law_ext
  rfl

theorem product_numbering {A B : Type} [Fintype A] [Fintype B] {m n : ℕ}
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (e : A ≃ Fin m) (f : B ≃ Fin n) :
    prod (reindex e μ) (reindex f ν)=
      reindex ((Equiv.prodCongr e f).trans finProdFinEquiv) (product μ ν) := by
  apply law_ext
  rfl

theorem mixture_numbering {A B : Type} [Fintype A] [Fintype B] {m n : ℕ}
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (e : A ≃ Fin m) (f : B ≃ Fin n) :
    mix (reindex e μ) (reindex f ν)=
      reindex ((Equiv.sumCongr e f).trans finSumFinEquiv) (mixture μ ν) := by
  apply law_ext
  funext i
  cases h : finSumFinEquiv.symm i with
  | inl a => simp [mix,reindex,mixture,h]
  | inr b => simp [mix,reindex,mixture,h]

variable {D q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def column : PositiveRationalLaw
    (Fin (src.outer.size*src.gamma.size+q₂*src.gamma.size)) :=
  mix (prod src.outer.law src.gamma.law) (prod (uniform q₂) src.gamma.law)

theorem column_eq : column src=reindex src.columnOrder src.columnLaw :=
  mixture_numbering (product src.outer.law src.gamma.law)
    (product (uniform q₂) src.gamma.law) finProdFinEquiv finProdFinEquiv

variable (st : src.Streams (w := w) (μI := μI))

def stream : PositiveRationalLaw
    (Fin (st.metadata.size*(st.base.size*st.selector.size))) :=
  prod st.metadata.law (prod st.base.law st.selector.law)

theorem stream_eq : stream src st=reindex (SourceData.Streams.order src st)
    (SourceData.Streams.law src st) := by
  simpa only [reindex_refl] using product_numbering st.metadata.law
    (product st.base.law st.selector.law) (Equiv.refl _) finProdFinEquiv

theorem final_input_law : prod (uniform w) (column src)=
    reindex ((Equiv.prodCongr (Equiv.refl _) src.columnOrder).trans finProdFinEquiv)
      (product (uniform w) src.columnLaw) := by
  rw [column_eq]
  simpa only [reindex_refl] using product_numbering (uniform w) src.columnLaw
    (Equiv.refl _) src.columnOrder

theorem successor_column_law : prod (uniform Q) (stream src st)=
    reindex (SourceData.successorColumnOrder src st)
      (product (uniform Q) (SourceData.Streams.law src st)) := by
  rw [stream_eq]
  simpa only [reindex_refl] using product_numbering (uniform Q)
    (SourceData.Streams.law src st) (Equiv.refl _) (SourceData.Streams.order src st)

#print axioms column_eq
#print axioms final_input_law
#print axioms successor_column_law
end
end CurrentAdditive.V40NumberedLawAlgebra
