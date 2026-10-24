import Paper2.RecursiveSamplingReachability
import Paper2.RecursiveSamplingTape
import Paper2.YaoMaterializationTable

/-!
# Row-major output of the ordinary-model recursive sampler

Frozen v12 Appendix D, generating and printing the final sampled table.
Only the generic serialized-table datatype and its proved output loop are
reused from `YaoMaterializationTable`; no strictly alternating communication
bound is used. The actual bounded-tape output is evaluated into a Boolean
list, whose getters, unrestricted communication complexity, all-event law,
length and output-loop counters are proved below. These counters charge
entry calls and list cells, not the cost of generating labels, evaluating
an entry, accessing stored tuples, or executing a machine program.
-/

namespace Paper2.RecursiveSamplingMaterialization

open SourceMatrix RecursiveEntries RecursiveSamplingExecution
open Workspace.Types.CommComplexity
open YaoMaterialization (SerializedTable tabulate tabulate_matrix tabulate_length
  CountedOutput countedTabulate countedTabulate_bits countedTabulate_entryCalls
  countedTabulate_consCells)

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- The actual row-major Boolean-list output of the capped sampler. No
colouring, optimal protocol, target lower bound, or success event selects it. -/
def materialize (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) : SerializedTable mX mY :=
  tabulate (run order hs p hp activity ξ k mX mY t)

theorem materialize_length (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (materialize order hs p hp activity ξ k mX mY t).bits.length = mX * mY :=
  tabulate_length _

/-- Each getter of the printed list is exactly the same capped matrix entry. -/
theorem materialize_entry (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) (i : Fin mX) (j : Fin mY) :
    (materialize order hs p hp activity ξ k mX mY t).matrix i j =
      run order hs p hp activity ξ k mX mY t i j :=
  tabulate_matrix _ i j

theorem materialize_matrix (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (materialize order hs p hp activity ξ k mX mY t).matrix =
      run order hs p hp activity ξ k mX mY t := by
  funext i j
  exact materialize_entry order hs p hp activity ξ k mX mY t i j

/-- Exact unrestricted communication complexity; serialization introduces
neither a change of model nor an extra communication bit. -/
theorem materialize_D (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    D (materialize order hs p hp activity ξ k mX mY t).matrix =
      D (run order hs p hp activity ξ k mX mY t) := by
  rw [materialize_matrix]

/-- Every tape prints a restriction of no larger communication complexity,
or a constant table on abort. The source upper bound is not an assumption. -/
theorem materialize_D_le (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    D (materialize order hs p hp activity ξ k mX mY t).matrix ≤
      D (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) := by
  rw [materialize_D]
  exact run_D_le order hs p hp activity ξ k mX mY t

/-- Probability transfer for every event of the literal output list. The
ideal comparison prints the exact same sampled recursive source entries. -/
theorem materialize_bits_event_error (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => (materialize order hs p hp activity ξ k mX mY t).bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := V) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
        (fun z => (tabulate (sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) z.2 z.1)).bits ∈ E)|
      ≤ (1 / 2 : ℝ) ^ 13 := by
  exact run_event_error order hs p hp activity ξ k mX mY
    {F | (tabulate F).bits ∈ E}

/-- In particular the matrix decoded from the printed bits has exactly the
same all-event comparison; no claim about conditioned successful tapes is made. -/
theorem materialize_matrix_event_error (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => (materialize order hs p hp activity ξ k mX mY t).matrix ∈ E) -
      (RecursiveSampling.sampleLaw (V := V) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
        (fun z => sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) z.2 z.1 ∈ E)|
      ≤ (1 / 2 : ℝ) ^ 13 := by
  simp_rw [materialize_matrix]
  exact run_event_error order hs p hp activity ξ k mX mY E

/-- The concrete output loop, with the generic loop's generated counters.
An entry call means one call to the completed matrix's entry function. -/
def countedMaterialize (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) : CountedOutput :=
  countedTabulate (run order hs p hp activity ξ k mX mY t)

theorem countedMaterialize_bits (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (countedMaterialize order hs p hp activity ξ k mX mY t).bits =
      (materialize order hs p hp activity ξ k mX mY t).bits :=
  countedTabulate_bits _

theorem countedMaterialize_counts (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (countedMaterialize order hs p hp activity ξ k mX mY t).entryCalls = mX * mY ∧
      (countedMaterialize order hs p hp activity ξ k mX mY t).consCells = mX * mY :=
  ⟨countedTabulate_entryCalls _, countedTabulate_consCells _⟩

/-- Literal fair-bit input lists for the same already-announced public tape. -/
abbrev TapeList (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) :=
  RecursiveSamplingTape.SerializedTape
    (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p))
    (rejectionAttemptCap (drawCap s q₁ q₂ w Q p k mX mY))
    (drawCap s q₁ q₂ w Q p k mX mY)

def inputBitCount (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) : ℕ :=
  RecursiveSamplingTape.bitCount
    (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p))
    (rejectionAttemptCap (drawCap s q₁ q₂ w Q p k mX mY))
    (drawCap s q₁ q₂ w Q p k mX mY)

/-- Read a correctly sized bit list and print the actual capped output. -/
def materializeTapeList (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : TapeList V s q₁ q₂ w Q p k mX mY) : SerializedTable mX mY :=
  materialize order hs p hp activity ξ k mX mY (RecursiveSamplingTape.readTape _ _ _ bits)

theorem materializeTapeList_length (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : TapeList V s q₁ q₂ w Q p k mX mY) :
    (materializeTapeList order hs p hp activity ξ k mX mY bits).bits.length = mX * mY :=
  materialize_length order hs p hp activity ξ k mX mY _

theorem materializeTapeList_D_le (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : TapeList V s q₁ q₂ w Q p k mX mY) :
    D (materializeTapeList order hs p hp activity ξ k mX mY bits).matrix ≤
      D (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) :=
  materialize_D_le order hs p hp activity ξ k mX mY _

/-- Total raw-list parser: only the public length is tested. A wrong input
length is distinct from rejection exhaustion on a correctly sized tape. -/
def materializeList (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : List Bool) : Option (SerializedTable mX mY) :=
  if h : bits.length = inputBitCount V s q₁ q₂ w Q p k mX mY then
    some (materializeTapeList order hs p hp activity ξ k mX mY ⟨bits, h⟩)
  else none

theorem materializeList_valid (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : TapeList V s q₁ q₂ w Q p k mX mY) :
    materializeList order hs p hp activity ξ k mX mY bits.val =
      some (materializeTapeList order hs p hp activity ξ k mX mY bits) := by
  simp [materializeList, inputBitCount, bits.property]

theorem materializeList_invalid (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : List Bool)
    (h : bits.length ≠ inputBitCount V s q₁ q₂ w Q p k mX mY) :
    materializeList order hs p hp activity ξ k mX mY bits = none := by
  simp [materializeList, h]

noncomputable def tapeListLaw (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) :
    FiniteLaw (TapeList V s q₁ q₂ w Q p k mX mY) :=
  RecursiveSamplingTape.serializedTapeLaw _ _ _

/-- Uniform literal input lists have the same output-event comparison,
including abort, as the already-proved finite fair-tape interpreter. -/
theorem materializeTapeList_event_error (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    |(tapeListLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun bits => (materializeTapeList order hs p hp activity ξ k mX mY bits).bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := V) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
        (fun z => (tabulate (sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) z.2 z.1)).bits ∈ E)|
      ≤ (1 / 2 : ℝ) ^ 13 := by
  unfold tapeListLaw materializeTapeList
  rw [RecursiveSamplingTape.serializedTapeLaw_prob _ _ _
    (fun t => (materialize order hs p hp activity ξ k mX mY t).bits ∈ E)]
  exact materialize_bits_event_error order hs p hp activity ξ k mX mY E

end Paper2.RecursiveSamplingMaterialization

#print axioms Paper2.RecursiveSamplingMaterialization.materialize_D_le
#print axioms Paper2.RecursiveSamplingMaterialization.materialize_bits_event_error
#print axioms Paper2.RecursiveSamplingMaterialization.countedMaterialize_counts
#print axioms Paper2.RecursiveSamplingMaterialization.materializeTapeList_D_le
#print axioms Paper2.RecursiveSamplingMaterialization.materializeTapeList_event_error
