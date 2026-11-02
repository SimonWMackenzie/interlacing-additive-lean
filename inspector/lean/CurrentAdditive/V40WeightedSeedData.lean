import CurrentAdditive.V40SeedCells
import CurrentAdditive.V40UniformLawClock

namespace CurrentAdditive.V40WeightedSeedData
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper BitMachineComposition
open V39GeneratedConstruction

abbrev Producer := PhysicalConcat.Producer

def concat (A B : Producer) : Producer where
  machine := PhysicalConcat.machine (A:=A) (B:=B)
  result x := A.result x++B.result x
  clock := PhysicalConcat.clock (A:=A) (B:=B)
  outputs := PhysicalConcat.outputs (A:=A) (B:=B)

def field (A : Producer) : Producer where
  machine := composition A.machine SourceFieldWriter.fieldMachine
  result x := EncodedCommunication.field (A.result x)
  clock x := A.clock x+2*(A.result x).length+2+(4*(A.result x).length+4)
  outputs x := composition_outputsWithin A.machine SourceFieldWriter.fieldMachine
    (A.outputs x) (SourceFieldWriter.field_outputs (A.result x))

def cells : Producer where
  machine := V40SeedCells.machine .cells
  result x := StoredWeightedState.cells (storedLookupSeed x.length)
  clock x := V40SeedCells.clock x.length
  outputs x := by simpa only [V40SeedCells.result_cells] using V40SeedCells.outputs .cells x

def rows (L : Nat) := 2^LookupSeed.width L
def columns (L : Nat) := LookupSeed.width L

theorem rows_pos (L : Nat) : 0<rows L := Nat.two_pow_pos _
theorem columns_pos (L : Nat) : 0<columns L := Nat.two_pow_pos _

def rowLaw : Producer where
  machine := composition (V40SeedCells.machine .rows) V40UniformLaw.machine
  result x := V40UniformLaw.word (rows x.length)
  clock x := V40SeedCells.clock x.length+2*rows x.length+2+V40UniformLaw.clock (rows x.length)
  outputs x := by
    have h := V40SeedCells.outputs .rows x
    rw [V40SeedCells.result_rows] at h
    simpa only [rows,List.length_replicate] using
      composition_outputsWithin (V40SeedCells.machine .rows) V40UniformLaw.machine
        h (V40UniformLaw.outputs_word (rows x.length) (rows_pos _))

def columnLaw : Producer where
  machine := composition (V40SeedCells.machine .columns) V40UniformLaw.machine
  result x := V40UniformLaw.word (columns x.length)
  clock x := V40SeedCells.clock x.length+2*columns x.length+2+V40UniformLaw.clock (columns x.length)
  outputs x := by
    have h := V40SeedCells.outputs .columns x
    rw [V40SeedCells.result_columns] at h
    simpa only [columns,List.length_replicate] using
      composition_outputsWithin (V40SeedCells.machine .columns) V40UniformLaw.machine
        h (V40UniformLaw.outputs_word (columns x.length) (columns_pos _))

theorem law_word (n : Nat) (μ : PositiveRationalLaw (Fin n))
    (hμ : ∀ i, μ.weight i=(n:ℚ)⁻¹) :
    V40UniformLaw.word n=StoredWeightedState.lawBytes μ := by
  have he : V40UniformLawLoop.entries n n=
      List.ofFn (fun i:Fin n => CodeDTargetV2.alphabetEntry (i.val,(n:ℚ)⁻¹)) := by
    apply List.ext_getElem
    · simp [V40UniformLawLoop.entries]
    · intro i hi hj
      simp [V40UniformLawLoop.entries]
  unfold V40UniformLaw.word StoredWeightedState.lawBytes StoredWeightedState.lawAlphabet
    CodeDTargetV2.alphabetBytes
  simp only [Array.toList_ofFn,List.map_ofFn,CodeDCodecV2.encodeItems,Function.comp_def]
  apply congrArg SourceListEncoding.encode
  rw [he]
  apply congrArg List.ofFn
  funext i
  rw [hμ i]

theorem rowLaw_result (L : Nat) :
    V40UniformLaw.word (rows L)=StoredWeightedState.lawBytes (storedLookupSeed L).rowLaw := by
  apply law_word (rows L) (storedLookupSeed L).rowLaw
  intro i
  change (Vector.ofFn (fun _ : Fin (rows L) => (rows L:ℚ)⁻¹))[i.val]=(rows L:ℚ)⁻¹
  rw [Vector.getElem_ofFn]

theorem columnLaw_result (L : Nat) :
    V40UniformLaw.word (columns L)=StoredWeightedState.lawBytes (storedLookupSeed L).colLaw := by
  apply law_word (columns L) (storedLookupSeed L).colLaw
  intro i
  change (Vector.ofFn (fun _ : Fin (columns L) => (columns L:ℚ)⁻¹))[i.val]=(columns L:ℚ)⁻¹
  rw [Vector.getElem_ofFn]

def producer : Producer := concat (field cells) (concat (field rowLaw) (field columnLaw))
def machine := producer.machine
def clock (L : Nat) := producer.clock (List.replicate L true)

theorem result (x : List Bool) :
    producer.result x=StoredWeightedState.encode (storedLookupSeed x.length) := by
  simp only [producer,concat,field,cells,rowLaw,columnLaw]
  rw [rowLaw_result,columnLaw_result]
  simp [StoredWeightedState.encode,BitMachineBankCodec.encode,BitMachineBankCodec.encodeFrom]

theorem outputs (L : Nat) :
    machine.OutputsWithin (List.replicate L true)
      (StoredWeightedState.encode (storedLookupSeed L)) (clock L) := by
  have h := producer.outputs (List.replicate L true)
  rw [result,List.length_replicate] at h
  exact h

#print axioms outputs
end
end CurrentAdditive.V40WeightedSeedData
