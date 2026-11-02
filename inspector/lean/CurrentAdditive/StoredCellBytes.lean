import CurrentAdditive.StoredStepContext
import CurrentAdditive.StoredSuccessorOrderedSpec
import CurrentAdditive.CylinderProductionProjection

/-! Literal byte inputs for one current generated successor cell. Source
tuples contain their original flat alphabet labels. Decoder companions keep
the original product and sum indices, so no quotient/injective decoder is
used. These are data definitions, with no run or matrix-property receipt. -/

namespace CurrentAdditive.StoredCellBytes
open Paper2 EthInapproximability.CurrentPaper
open V39GeneratedConstruction

def tuple {q : Nat} (f : Fin q → Nat) : List Bool :=
  SourceListEncoding.encode (List.ofFn (fun p => (f p).bits))

def words {q n : Nat} (f : Fin n → Fin q → Nat) : List (List Bool) :=
  List.ofFn (fun i => tuple (f i))

def productCompanions (m n : Nat) : List (List Bool) :=
  List.ofFn (fun k : Fin (m*n) =>
    let ij := finProdFinEquiv.symm k
    BitMachineBankCodec.encode ![ij.1.val.bits,ij.2.val.bits])

def sumCompanions (m n : Nat) : List (List Bool) :=
  List.ofFn (fun k : Fin (m+n) =>
    match finSumFinEquiv.symm k with
    | .inl i => BitMachineBankCodec.encode ![[false],i.val.bits]
    | .inr j => BitMachineBankCodec.encode ![[true],j.val.bits])

@[simp] theorem words_length {q n : Nat} (f : Fin n → Fin q → Nat) :
    (words f).length=n := by simp [words]

@[simp] theorem productCompanions_length (m n : Nat) :
    (productCompanions m n).length=m*n := by simp [productCompanions]

@[simp] theorem sumCompanions_length (m n : Nat) :
    (sumCompanions m n).length=m+n := by simp [sumCompanions]

section Sources
variable {D q₁ q₂ s w Q nx ny ni : Nat}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))

def gammaWords := words (fun i p => (src.gamma.decode i p).val)
def innerWords := words (fun i p => (finProdFinEquiv (src.inner.decode i p)).val)
def outerWords := words (fun i p => (finProdFinEquiv (src.outer.decode i p)).val)
def metadataWords := words (fun i p => (finSumFinEquiv (st.metadata.decode i p)).val)
def baseWords := words (fun i p => (st.base.decode i p).val)
def selectorWords := words (fun i p => (st.selector.decode i p).val)
def finalWords := words (fun i p =>
  (finProdFinEquiv ((out.decode i p).1,src.columnOrder (out.decode i p).2)).val)

def sources : List Bool := BitMachineBankCodec.encode ![
  SourceListEncoding.encode (gammaWords src),SourceListEncoding.encode (innerWords src),
  SourceListEncoding.encode (outerWords src),SourceListEncoding.encode (metadataWords src st),
  SourceListEncoding.encode (baseWords src st),SourceListEncoding.encode (selectorWords src st),
  SourceListEncoding.encode (finalWords src out)]

/-- The diagonal-column product decoder is the same q2-by-gamma decoder
already used by the outer source. The six tables contain every flat index. -/
def companions : List Bool := BitMachineBankCodec.encode ![
  SourceListEncoding.encode (productCompanions q₁ nx),
  SourceListEncoding.encode (productCompanions q₂ src.gamma.size),
  SourceListEncoding.encode (sumCompanions s ni),
  SourceListEncoding.encode (productCompanions src.outer.size src.gamma.size),
  SourceListEncoding.encode (sumCompanions (src.outer.size*src.gamma.size) (q₂*src.gamma.size)),
  SourceListEncoding.encode (productCompanions w (src.outer.size*src.gamma.size+q₂*src.gamma.size))]

def baseState (R : Fin nx → Fin ny → Bool) : List Bool :=
  BitMachineBankCodec.encode ![MatrixMaterialization.rowMajor R,
    StoredWeightedState.lawBytes μX,StoredWeightedState.lawBytes μY]

def context (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s)) :=
  BitMachineBankCodec.encode ![StoredStepContext.context q₁ w Q μI activity,
    baseState (μX := μX) (μY := μY) R,sources src st out,companions src (ni := ni) (w := w)]

def input (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (selected : Fin w × src.Column) (m : Fin st.metadata.size)
    (b : Fin st.base.size) (z : Fin st.selector.size) : List Bool :=
  BitMachineBankCodec.encode ![context src st out R activity,
    (finProdFinEquiv (selected.1,src.columnOrder selected.2)).val.bits,
    tuple (fun p => (finSumFinEquiv (st.metadata.decode m p)).val),
    tuple (fun p => (st.base.decode b p).val),
    tuple (fun p => (st.selector.decode z p).val)]

theorem finalWords_entry (r : Fin out.size) :
    (finalWords src out)[r.val]?.getD [] =
      tuple (fun j => (finProdFinEquiv ((out.decode r j).1,
        src.columnOrder (out.decode r j).2)).val) := by
  simp [finalWords,words]

end Sources
end CurrentAdditive.StoredCellBytes

#print axioms CurrentAdditive.StoredCellBytes.finalWords_entry
