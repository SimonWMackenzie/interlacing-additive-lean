import CurrentAdditive.V39StoredGenerated

/-! Explicit nested polynomial bounds on the *actual* stored dimensions.
These count labels, Boolean entries and rational weight slots; they do not
bound rational bit lengths or physical execution time. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2

def gammaBudget (q₁ s ny : ℕ) := (1+(q₁+s+1)*ny)^8192
def innerBudget (q₁ q₂ nx : ℕ) := (1+q₂*(q₁*nx))^8192
def outerBudget (q₁ q₂ s ny : ℕ) := (1+s*(q₂*gammaBudget q₁ s ny))^8192
def metadataBudget (s w ni : ℕ) := (1+w*(s+ni))^8192
def baseBudget (w nx : ℕ) := (1+w*nx)^8192
def selectorBudget (q₁ q₂ w nx : ℕ) := (1+w*innerBudget q₁ q₂ nx)^8192

def rowBudget (q₁ q₂ s w Q ny : ℕ) :=
  (1+Q*(w*(outerBudget q₁ q₂ s ny*gammaBudget q₁ s ny+
    q₂*gammaBudget q₁ s ny)))^8192

def colBudget (q₁ q₂ s w Q nx ni : ℕ) :=
  Q*(metadataBudget s w ni*(baseBudget w nx*selectorBudget q₁ q₂ w nx))

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

theorem executableStep_dimensions (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) :
    (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows ≤
      rowBudget q₁ q₂ s w Q R.cols ∧
    (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols ≤
      colBudget q₁ q₂ s w Q R.rows ni := by
  let c := executableCodeD 8192
  let src := sourceData (q₁ := q₁) (q₂ := q₂) (s := s) c R.rowLaw R.colLaw
  let st := SourceData.streams (w := w) c src (μI := μI)
  let out := SourceData.final (w := w) (Q := Q) c src
  have hg : src.gamma.size ≤ gammaBudget q₁ s R.cols :=
    executable_size 8192 (q₁+s+1) R.cols R.colLaw
  have hi : src.inner.size ≤ innerBudget q₁ q₂ R.rows :=
    executable_call_size 8192 q₂ (q₁*R.rows) finProdFinEquiv
      (product (uniform q₁) R.rowLaw)
  have hj₀ : src.outer.size ≤ (1+s*(q₂*src.gamma.size))^8192 :=
    executable_call_size 8192 s (q₂*src.gamma.size) finProdFinEquiv
      (product (uniform q₂) src.gamma.law)
  have hj : src.outer.size ≤ outerBudget q₁ q₂ s R.cols := by
    apply hj₀.trans
    unfold outerBudget
    gcongr
  have hm : st.metadata.size ≤ metadataBudget s w ni :=
    executable_call_size 8192 w (s+ni) finSumFinEquiv (mixture (uniform s) μI)
  have hb : st.base.size ≤ baseBudget w R.rows :=
    executable_size 8192 w R.rows R.rowLaw
  have hs₀ : st.selector.size ≤ (1+w*src.inner.size)^8192 :=
    executable_size 8192 w src.inner.size src.inner.law
  have hs : st.selector.size ≤ selectorBudget q₁ q₂ w R.rows := by
    apply hs₀.trans
    unfold selectorBudget
    gcongr
  have ho : out.size ≤
      (1+Q*(w*(src.outer.size*src.gamma.size+q₂*src.gamma.size)))^8192 :=
    executable_call_size 8192 Q
      (w*(src.outer.size*src.gamma.size+q₂*src.gamma.size))
      ((Equiv.prodCongr (Equiv.refl _) src.columnOrder).trans finProdFinEquiv)
      (product (uniform w) src.columnLaw)
  constructor
  · change out.size ≤ rowBudget q₁ q₂ s w Q R.cols
    apply ho.trans
    unfold rowBudget
    gcongr
  · change Q*(st.metadata.size*(st.base.size*st.selector.size)) ≤
      colBudget q₁ q₂ s w Q R.rows ni
    unfold colBudget
    gcongr

theorem storedStep_dimensions (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows ≤
      rowBudget q₁ q₂ s w Q R.cols ∧
    (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols ≤
      colBudget q₁ q₂ s w Q R.rows ni :=
  executableStep_dimensions μI activity R.numbered

theorem storedStep_cells (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cells.toArray.size ≤
      rowBudget q₁ q₂ s w Q R.cols*colBudget q₁ q₂ s w Q R.rows ni := by
  have h := storedStep_dimensions (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R
  simpa only [Vector.size_toArray] using Nat.mul_le_mul h.1 h.2

end CurrentAdditive.V39GeneratedConstruction
