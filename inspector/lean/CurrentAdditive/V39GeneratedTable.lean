import CurrentAdditive.V39GeneratedConstruction
import EthInapproximability.CurrentPaper.MatrixMaterialization
import EthInapproximability.CurrentPaper.EncodedCommunication

/-! The actual numbered table, complete row-major Boolean word, and iteration
of the selected manuscript's two-family generated construction. This is a
functional construction. Physical bit-machine clocks are not claimed. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper

structure NumberedMatrix where
  rows : ℕ
  cols : ℕ
  rowLaw : PositiveRationalLaw (Fin rows)
  colLaw : PositiveRationalLaw (Fin cols)
  entry : Fin rows → Fin cols → Bool

theorem law_size_pos {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  subst n
  have ht := μ.total
  simp at ht

namespace SourceData

variable {D q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column)
    (product (uniform w) src.columnLaw))

def successorColumnOrder : (Fin Q × st.Label) ≃
    Fin (Q*(st.metadata.size*(st.base.size*st.selector.size))) :=
  (Equiv.prodCongr (Equiv.refl _) (Streams.order src st)).trans finProdFinEquiv

def numberedEntry (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Fin out.size → Fin (Q*(st.metadata.size*(st.base.size*st.selector.size))) → Bool :=
  fun j a => src.successor st out R activity j
    ((successorColumnOrder src st).symm a)

def numbered (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) : NumberedMatrix where
  rows := out.size
  cols := Q*(st.metadata.size*(st.base.size*st.selector.size))
  rowLaw := out.law
  colLaw := reindex (successorColumnOrder src st)
    (product (uniform Q) (Streams.law src st))
  entry := numberedEntry src st out R activity

theorem numbered_cost (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Workspace.Types.CommComplexity.D (src.numbered st out R activity).entry =
      Workspace.Types.CommComplexity.D (src.successor st out R activity) := by
  exact NPCC.D_equiv_invariance (src.successor st out R activity)
    (Equiv.refl _) (successorColumnOrder src st).symm

theorem numbered_upper (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Workspace.Types.CommComplexity.D (src.numbered st out R activity).entry ≤ Workspace.Types.CommComplexity.D R +
      (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+s+1)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  rw [numbered_cost]
  exact src.successor_upper st out R activity

theorem numbered_yes (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (assign : Fin ni → Fin s) (hc : CollisionFree assign activity) :
    Workspace.Types.CommComplexity.D (src.numbered st out R activity).entry ≤ Workspace.Types.CommComplexity.D R +
      (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  rw [numbered_cost]
  exact src.successor_yes st out R activity assign hc

end SourceData

namespace NumberedMatrix

variable {D q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

/-- The same seven source calls and indexed evaluator on every round. -/
def step (c : CodeD D) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) :
    NumberedMatrix :=
  let src := sourceData (q₁ := q₁) (q₂ := q₂) (s := s) c R.rowLaw R.colLaw
  let st := SourceData.streams (w := w) c src (μI := μI)
  let out := SourceData.final (w := w) (Q := Q) c src
  SourceData.numbered src st out R.entry activity

def iterate (c : CodeD D) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (k : ℕ) (R : NumberedMatrix) : NumberedMatrix :=
  Nat.rec R (fun _ M => step (q₁ := q₁) (s := s) (w := w) (Q := Q)
    c μI activity M) k

theorem step_upper (c : CodeD D) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) :
    Workspace.Types.CommComplexity.D (step (q₁ := q₁) (s := s) (w := w) (Q := Q) c μI activity R).entry ≤
      Workspace.Types.CommComplexity.D R.entry + (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+s+1)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  exact SourceData.numbered_upper _ _ _ R.entry activity

theorem step_yes (c : CodeD D) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix)
    (assign : Fin ni → Fin s) (hc : CollisionFree assign activity) :
    Workspace.Types.CommComplexity.D (step (q₁ := q₁) (s := s) (w := w) (Q := Q) c μI activity R).entry ≤
      Workspace.Types.CommComplexity.D R.entry + (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  exact SourceData.numbered_yes _ _ _ R.entry activity assign hc

theorem iterate_yes (c : CodeD D) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix)
    (assign : Fin ni → Fin s) (hc : CollisionFree assign activity) (k : ℕ) :
    Workspace.Types.CommComplexity.D (iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) c μI activity k R).entry ≤
      Workspace.Types.CommComplexity.D R.entry + k*(Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  induction k with
  | zero =>
    simpa only [iterate, Nat.zero_mul, Nat.add_zero] using
      (Nat.le_refl (Workspace.Types.CommComplexity.D R.entry))
  | succ k ih =>
    have hs := step_yes (q₁ := q₁) (s := s) (w := w) (Q := Q)
      c μI activity (iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) c μI activity k R)
      assign hc
    simpa only [iterate, Nat.succ_mul, Nat.add_assoc] using
      hs.trans (Nat.add_le_add_right ih _)

def rectangle (R : NumberedMatrix) (b : ℕ) : EncodedCommunication.Instance :=
  ⟨R.rows, R.cols, b, MatrixMaterialization.rowMajor R.entry⟩

theorem rectangle_valid (R : NumberedMatrix) (b : ℕ) : (R.rectangle b).Valid :=
  ⟨law_size_pos R.rowLaw, law_size_pos R.colLaw, MatrixMaterialization.rowMajor_length _⟩

theorem rectangle_entry (R : NumberedMatrix) (b : ℕ)
    (r : Fin R.rows) (c : Fin R.cols) :
    (R.rectangle b).table[r.val*R.cols+c.val]? = some (R.entry r c) :=
  MatrixMaterialization.rowMajor_entry _ r c

theorem rectangle_decode (R : NumberedMatrix) (b : ℕ) :
    EncodedCommunication.decodeInstance (EncodedCommunication.encodeInstance (R.rectangle b)) =
      some (R.rectangle b) := EncodedCommunication.decode_encode _ (R.rectangle_valid b)

theorem rectangle_encoding_length (R : NumberedMatrix) (b : ℕ) :
    (EncodedCommunication.encodeInstance (R.rectangle b)).length =
      2*(R.rows.bits.length+R.cols.bits.length+b.bits.length)+3+R.rows*R.cols := by
  rw [EncodedCommunication.encodeInstance_length]
  simp [rectangle]

end NumberedMatrix
end CurrentAdditive.V39GeneratedConstruction
