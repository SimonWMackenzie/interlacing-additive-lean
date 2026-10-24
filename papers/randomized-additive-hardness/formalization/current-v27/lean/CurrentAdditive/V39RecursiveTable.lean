import CurrentAdditive.V39RecursiveGenerator
import Paper2.RecursiveLabelCodec
import Paper2.YaoMaterializationTable
import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-! Selected v39, appendix access and section sampling.  Exact current-label
codecs, the one-request evaluator, and the literal encoded row-major word.
This is an executable semantic join.  It does not assert that the physical
rounded interpreter or the physical current edge-activity evaluator exists. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39RecursiveTable

open Paper2 Paper2.SourceMatrix Paper2.RecursiveLabelCodecScratch
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.V39RecursiveGenerator

variable (n p₀ q₁ q₂ s w Q : ℕ)

/-- Only the ordinary and diagonal tags are encoded. -/
def twoTagCodec {Y : Type} (cy : PrefixCodec Y) :
    PrefixCodec (V38Matrix.TaggedColumn q₁ q₂ s Y) :=
  sumCodec (rawColumnCodec q₁ q₂ s cy) (outerColumnCodec q₁ q₂ s cy)

/-- Both complete recursive labels, with every stored coordinate retained. -/
def codecs : (k : ℕ) →
    PrefixCodec (Row n p₀ q₁ q₂ s w Q k) ×
      PrefixCodec (Column n p₀ q₁ q₂ s w Q k)
  | 0 => (piCodec boolCodec p₀, finCodec p₀)
  | k + 1 =>
    let c := codecs k
    (piCodec (prodCodec (finCodec w) (twoTagCodec q₁ q₂ s c.2)) Q,
      prodCodec (finCodec Q)
        (piCodec (rawRowCodec q₁ q₂ s c.1 (defaultItemCodec n s)) w))

def sampleCodec (k m : ℕ) :
    PrefixCodec ((Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :=
  prodCodec (piCodec (codecs n p₀ q₁ q₂ s w Q k).1 m)
    (piCodec (codecs n p₀ q₁ q₂ s w Q k).2 m)

theorem sample_roundtrip (k m : ℕ)
    (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) (suffix : List Bool) :
    (sampleCodec n p₀ q₁ q₂ s w Q k m).decode
      ((sampleCodec n p₀ q₁ q₂ s w Q k m).encode z ++ suffix) =
      some (z, suffix) :=
  (sampleCodec n p₀ q₁ q₂ s w Q k m).roundtrip z suffix

theorem sample_maxLen (k m : ℕ) :
    (sampleCodec n p₀ q₁ q₂ s w Q k m).maxLen =
      m * ((codecs n p₀ q₁ q₂ s w Q k).1.maxLen +
        (codecs n p₀ q₁ q₂ s w Q k).2.maxLen) := by
  simp only [sampleCodec, prodCodec, piCodec_maxLen]
  ring

variable {n p₀ q₁ q₂ s w Q}

/-- Expanding a diagonal tag copies an existing word; it generates no
additional inputs or random choices. -/
def eraseTag {Y : Type} : V38Matrix.TaggedColumn q₁ q₂ s Y →
    RawColumn q₁ q₂ s Y
  | .inl Z => Z
  | .inr j => (tail j.2, fun _ => j)

theorem eraseTag_eq_forgetTag {Y : Type} (ξ : Tail s Y)
    (Z : V38Matrix.TaggedColumn q₁ q₂ s Y) :
    eraseTag Z = V38Matrix.forgetTag ξ Z := by cases Z <;> rfl

variable [NeZero s]

/-- The current entry asks for one earlier row/column pair. -/
def request (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q (k + 1))
    (y : Column n p₀ q₁ q₂ s w Q (k + 1)) :
    Row n p₀ q₁ q₂ s w Q k × Column n p₀ q₁ q₂ s w Q k :=
  let pair := x y.1
  baseRequest activity (y.2 pair.1) (eraseTag pair.2)

def matrix (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) :
    (k : ℕ) → Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → Bool
  | 0 => LookupSeed.matrix p₀
  | k + 1 => fun x y =>
    let pair := x y.1
    raw (matrix activity k) activity (y.2 pair.1) (eraseTag pair.2)

def seedRequest (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) :
    (k : ℕ) → Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k →
      (Fin p₀ → Bool) × Fin p₀
  | 0 => fun x y => (x, y)
  | k + 1 => fun x y =>
    let p := request activity k x y
    seedRequest activity k p.1 p.2

def evaluate (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k)
    (y : Column n p₀ q₁ q₂ s w Q k) : Bool :=
  let p := seedRequest activity k x y
  p.1 p.2

theorem evaluate_eq_matrix
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k)
    (y : Column n p₀ q₁ q₂ s w Q k) :
    evaluate activity k x y = matrix activity k x y := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (request activity k x y).1 (request activity k x y).2

/-- Bind the recursive formula to the selected manuscript's actual two-tag
source matrix. The arbitrary coordinate equivalence remains proof-side
source indexing; no physical implementation of it is asserted here. -/
theorem matrix_succ_eq_source {E : Type} [Fintype E]
    (order : EdgeSourceMatrix.Items s (Fin n) ≃
      Fin (Fintype.card (EdgeSourceMatrix.Items s (Fin n))))
    (edge : E → Bool → Fin n) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (k : ℕ) (ξ : Tail s (Column n p₀ q₁ q₂ s w Q k))
    (x : Row n p₀ q₁ q₂ s w Q (k + 1))
    (y : Column n p₀ q₁ q₂ s w Q (k + 1)) :
    matrix (EdgeSourceMatrix.activity order edge hs r hq) (k + 1) x y =
      V38Matrix.matrix order edge hs r hq
        (matrix (EdgeSourceMatrix.activity order edge hs r hq) k) ξ
        (x y.1).2 (y.2 (x y.1).1) := by
  change raw _ _ _ (eraseTag _) = raw _ _ _ (V38Matrix.forgetTag ξ _)
  rw [eraseTag_eq_forgetTag ξ]

/-- The descent count is a semantic call count, not a Turing clock. -/
def descentCount (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) :
    (k : ℕ) → Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → ℕ
  | 0 => fun _ _ => 0
  | k + 1 => fun x y =>
    let p := request activity k x y
    1 + descentCount activity k p.1 p.2

theorem descentCount_eq
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k)
    (y : Column n p₀ q₁ q₂ s w Q k) : descentCount activity k x y = k := by
  induction k with
  | zero => rfl
  | succ k ih => change 1 + descentCount activity k _ _ = k + 1; rw [ih]; omega

def sampledTable (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) : YaoMaterialization.SerializedTable m m :=
  YaoMaterialization.tabulate (fun i j => evaluate activity k (z.1 i) (z.2 j))

theorem sampledTable_entry
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) (i j : Fin m) :
    (sampledTable activity k m z).matrix i j = matrix activity k (z.1 i) (z.2 j) := by
  exact (YaoMaterialization.tabulate_matrix _ i j).trans (evaluate_eq_matrix activity k _ _)

def tableInstance (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m B : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) : EncodedCommunication.Instance :=
  ⟨m, m, B, (sampledTable activity k m z).bits⟩

def outputWord (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m B : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) : List Bool :=
  encodeInstance (tableInstance activity k m B z)

theorem decode_outputWord
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m B : ℕ) (hm : 0 < m) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :
    decodeInstance (outputWord activity k m B z) = some (tableInstance activity k m B z) := by
  apply decode_encode
  exact ⟨hm, hm, (sampledTable activity k m z).length⟩

theorem outputWord_length
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m B : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :
    (outputWord activity k m B z).length =
      2 * (m.bits.length + m.bits.length + B.bits.length) + 3 + m * m := by
  exact (encodeInstance_length _).trans (by simp only [tableInstance, (sampledTable activity k m z).length])

/-- Natural-number entry getter expected by the existing physical writer.
This is a definition of the target, not an assumed physical callback. -/
def natEntry (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) (i j : ℕ) : Bool :=
  if hi : i < m then if hj : j < m then evaluate activity k (z.1 ⟨i, hi⟩) (z.2 ⟨j, hj⟩)
    else false else false

theorem writer_target_exact
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (k m : ℕ) (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :
    MatrixTableWriter.tableWord (natEntry activity k m z) m 0 m =
      (sampledTable activity k m z).bits := by
  rw [MatrixTableWriter.tableWord_eq_rowMajor m m _
    (fun i j => evaluate activity k (z.1 i) (z.2 j))
    (by intro i j; simp [natEntry])]
  rfl

#print axioms sample_roundtrip
#print axioms evaluate_eq_matrix
#print axioms matrix_succ_eq_source
#print axioms descentCount_eq
#print axioms sampledTable_entry
#print axioms decode_outputWord
#print axioms writer_target_exact

end CurrentAdditive.V39RecursiveTable
