import CurrentAdditive.V40StoredThreshold
import CurrentAdditive.StoredWeightedState

namespace CurrentAdditive.V40StoredRectangle
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction PhysicalProducer V40StoredOutputPrimitives

def input (L K : Nat) (context : List Bool) (R : StoredMatrix) :=
  V40StoredThreshold.input L K (BitMachineBankCodec.encode ![context,StoredWeightedState.encode R])

def state := compose (PhysicalProducer.projection (2 : Fin 3)) (PhysicalProducer.projection (1 : Fin 2))
def cells := compose state (PhysicalProducer.projection (0 : Fin 3))
def rowLaw := compose state (PhysicalProducer.projection (1 : Fin 3))
def colLaw := compose state (PhysicalProducer.projection (2 : Fin 3))
def rowHeader := compose rowLaw header
def colHeader := compose colLaw header

def rectangle := concat rowHeader (concat colHeader (concat V40StoredThreshold.fieldProducer cells))
def machine := rectangle.machine

def rectangleInstance (L K : Nat) (R : StoredMatrix) : Instance :=
  ⟨R.rows,R.cols,V40StoredThreshold.thresholdNumber L K,StoredWeightedState.cells R⟩

theorem law_header {n : Nat} (μ : PositiveRationalLaw (Fin n)) :
    header.result (StoredWeightedState.lawBytes μ)=natField n := by
  change header.result (SourceListEncoding.encode
    ((StoredWeightedState.lawAlphabet μ).toList.map CodeDTargetV2.alphabetEntry))=natField n
  rw [SourceListEncoding.encode]
  have hlen : ((StoredWeightedState.lawAlphabet μ).toList.map CodeDTargetV2.alphabetEntry).length=n := by simp
  rw [hlen]
  exact header_field n.bits _

theorem state_result (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    state.result (input L K context R)=StoredWeightedState.encode R := by
  simp [state,compose,PhysicalProducer.projection,input,V40StoredThreshold.input,BankFieldProjection.result_encode]

theorem cells_result (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    cells.result (input L K context R)=StoredWeightedState.cells R := by
  simp only [cells,compose,Function.comp_apply,state_result,PhysicalProducer.projection,StoredWeightedState.encode,
    BankFieldProjection.result_encode,Matrix.cons_val_zero]

theorem row_result (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    rowHeader.result (input L K context R)=natField R.rows := by
  simp only [rowHeader,rowLaw,compose,Function.comp_apply,state_result,PhysicalProducer.projection,StoredWeightedState.encode,
    BankFieldProjection.result_encode,Matrix.cons_val_one]
  exact law_header R.rowLaw

theorem col_result (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    colHeader.result (input L K context R)=natField R.cols := by
  simp only [colHeader,colLaw,compose,Function.comp_apply,state_result,PhysicalProducer.projection,StoredWeightedState.encode,
    BankFieldProjection.result_encode,Matrix.cons_val_two]
  exact law_header R.colLaw

theorem rectangle_result (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    rectangle.result (input L K context R)=encodeInstance (rectangleInstance L K R) := by
  simp only [rectangle,concat]
  rw [row_result,col_result,cells_result]
  rw [show V40StoredThreshold.fieldProducer.result (input L K context R)=
    natField (V40StoredThreshold.thresholdNumber L K) from V40StoredThreshold.field_result_input L K _]
  simp [encodeInstance,rectangleInstance,List.append_assoc]

/-- Dimensions and cells come from the actual stored state; the threshold is
physically computed from the retained unary L/K inputs. -/
theorem outputs (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    machine.OutputsWithin (input L K context R) (encodeInstance (rectangleInstance L K R))
      (rectangle.coefficient*((input L K context R).length+1)^rectangle.degree) := by
  simpa only [machine,rectangle_result] using rectangle.outputs (input L K context R)

theorem public_outputs (p : SourceConstants) (floor : Nat) {n m : Nat}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (K : Nat) (context : List Bool) :
    let L := publicLogFrom p floor n m hn hlow hdegree
    let R := publicGraphRunFrom p floor hn hlow hdegree edge K
    machine.OutputsWithin (input L K context R)
      (encodeInstance ⟨R.rows,R.cols,
        publicGraphThresholdFrom p floor n m hn hlow hdegree K,
        MatrixMaterialization.rowMajor R.entry⟩)
      (rectangle.coefficient*((input L K context R).length+1)^rectangle.degree) :=
  outputs _ _ _ _

#print axioms law_header
#print axioms outputs
#print axioms public_outputs
end
end CurrentAdditive.V40StoredRectangle
