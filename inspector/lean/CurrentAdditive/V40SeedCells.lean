import Paper2.SeedTableFinal
import CurrentAdditive.V39GraphGenerated
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import CurrentAdditive.StoredWeightedState

/-! The same fixed accepted seed program, with three fixed choices of output
port. The public level is supplied physically through a power-of-two call. -/
namespace CurrentAdditive.V40SeedCells
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper BitMachineEncoding BitMachineComposition
open SeedT45.SeedTable

inductive Port where | cells | rows | columns
  deriving DecidableEq

def outputPort : Port → J | .cells => outC | .rows => rowsC | .columns => colsC

def nativeMachine (port : Port) : BitMachine.Machine :=
  ofFinite (ιL Paper2.LProducer.nC) (outputPort port) qStart qInit Q

def nativeResult (port : Port) (n : Nat) : List Bool :=
  match port with
  | .cells => MatrixMaterialization.rowMajor (seedTable (Paper2.LookupSeed.width (Nat.clog 2 n)))
  | .rows => List.replicate (2^Paper2.LookupSeed.width (Nat.clog 2 n)) true
  | .columns => List.replicate (Paper2.LookupSeed.width (Nat.clog 2 n)) true

theorem native_outputs (port : Port) (n : Nat) :
    (nativeMachine port).OutputsWithin (List.replicate n true) (nativeResult port n) (seedBound n) := by
  obtain ⟨t,ht,hl,hcells,hcolumns,hrows⟩ := seed_raw_run n
  apply outputsWithin_of_raw_run _ _ _ _ Q _ _ t _ ht hl
  cases port with
  | cells => exact hcells
  | rows => exact hrows
  | columns => exact hcolumns

def machine (port : Port) := composition MatrixUnaryPower.machine (nativeMachine port)
def result (port : Port) (L : Nat) := nativeResult port (2^L)
def clock (L : Nat) := 16*2^L+2*2^L+2+seedBound (2^L)

theorem outputs (port : Port) (input : List Bool) :
    (machine port).OutputsWithin input (result port input.length) (clock input.length) := by
  simpa only [machine,result,clock,List.length_replicate] using
    composition_outputsWithin MatrixUnaryPower.machine (nativeMachine port)
      (MatrixUnaryPower.outputs input) (native_outputs port (2^input.length))

theorem result_cells (L : Nat) : result .cells L=
    StoredWeightedState.cells (V39GeneratedConstruction.storedLookupSeed L) := by
  change MatrixMaterialization.rowMajor (seedTable (Paper2.LookupSeed.width (Nat.clog 2 (2^L))))=_
  rw [Nat.clog_pow 2 L (by omega)]
  unfold StoredWeightedState.cells
  congr 1
  funext r c
  exact (V39GeneratedConstruction.StoredMatrix.ofNumbered_entry
    (V39GeneratedConstruction.lookupSeed L) r c).symm

theorem result_rows (L : Nat) : result .rows L=List.replicate (2^Paper2.LookupSeed.width L) true := by
  simp [result,nativeResult,Nat.clog_pow 2 L (by omega)]

theorem result_columns (L : Nat) : result .columns L=List.replicate (Paper2.LookupSeed.width L) true := by
  simp [result,nativeResult,Nat.clog_pow 2 L (by omega)]

#print axioms outputs
#print axioms result_cells
end
end CurrentAdditive.V40SeedCells
