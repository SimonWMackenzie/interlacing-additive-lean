import CurrentAdditive.V40DeterministicRounds
import CurrentAdditive.DeterministicETHSourceBridge
import Paper2.A4Kof
import Paper2.E4Front

/-! Actual all-input formula routing and source input framing. Fixed-gap
routing preserves the entire CNF language. The separate sparse router is
used only by the ETH consumer. Original variables supply the floor/round. -/
namespace CurrentAdditive.V40DeterministicSourcePack
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open PhysicalProducer V40StoredOutputPrimitives
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def ofPolytime (f : List Bool → List Bool) (hf : BitMachine.Polytime f) : Producer where
  machine := Classical.choose hf
  result := f
  coefficient := Classical.choose (Classical.choose_spec hf)
  degree := Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
  outputs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf))

def route (cutoff : ℕ) (hcut : 1 ≤ cutoff) : Producer where
  machine := BitMachineComposition.composition CNFValidator.machine (Front.scanMachine cutoff)
  result := Front.scanTarget cutoff
  coefficient := 260
  degree := 3
  outputs w := by
    have h:=BitMachineComposition.composition_outputsWithin _ _
      (CNFValidator.Runtime.outputs w) (Front.scan_outputs hcut w)
    apply BitMachine.outputsWithin_mono _ h
    have hr:=AFront.Route.result_length w
    have hp : w.length+1 ≤ (w.length+1)^3 := Nat.le_self_pow (by decide) _
    nlinarith

def originalVariables := V40BoundedFormatter.bounded SourceOriginalVariableCapture.machine 3 1

theorem original_result (Φ : EncodedCNF.Formula) :
    originalVariables.result (EncodedCNF.encode Φ)=List.replicate Φ.variables true := by
  apply V40BoundedFormatter.result_of_run
  apply BitMachine.outputsWithin_mono _ (SourceOriginalVariableCapture.canonical_outputs Φ)
  have h:=SourceOriginalVariableCapture.original_n_le_input Φ
  simp only [pow_one]
  omega

def bank3 (A B C : Producer) := concat (compose A field)
  (concat (compose B field) (compose C field))

theorem bank3_result (A B C : Producer) (x : List Bool) :
    (bank3 A B C).result x=BitMachineBankCodec.encode ![A.result x,B.result x,C.result x] := by
  simp [bank3,concat,compose,PhysicalProducer.field,BitMachineBankCodec.encode_eq_list]

def graphInput (g : EncodedGraph.Graph) (floor K : ℕ) :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate floor true,List.replicate K true]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def graph := ofPolytime (CNFGraphGuard.graphWord D B (by decide : 1≤1))
  (DeterministicETHSourceBridge.fixed_graph_compiler D B 1 (by decide))

theorem graph_result (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (graph D B).result (EncodedCNF.encode Φ.val)=EncodedGraph.encode (t10Graph D B Φ) :=
  DeterministicETHSourceBridge.fixed_graph_word_eq D B 1 (by decide) Φ hN

def fixedPack (K : ℕ) := bank3 (graph D B) originalVariables (UnaryProducer.constant K).producer

def growingRound (amp : ℕ) := compose originalVariables (V40DeterministicRounds.roundUnary amp).producer
def growingPack (amp : ℕ) := bank3 (graph D B) originalVariables (growingRound amp)

theorem fixed_result (K : ℕ) (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (fixedPack D B K).result (EncodedCNF.encode Φ.val)=
      graphInput (t10Graph D B Φ) Φ.val.variables K := by
  rw [fixedPack,bank3_result,graph_result D B Φ hN,original_result]
  rfl

theorem growing_result (amp : ℕ) (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (growingPack D B amp).result (EncodedCNF.encode Φ.val)=
      graphInput (t10Graph D B Φ) Φ.val.variables (V39RuntimeETHNumerics.rounds amp Φ.val.variables) := by
  rw [growingPack,bank3_result,graph_result D B Φ hN,original_result]
  change BitMachineBankCodec.encode ![_,_,
    (V40DeterministicRounds.roundUnary amp).producer.result
      (originalVariables.result (EncodedCNF.encode Φ.val))]=_
  rw [original_result,(V40DeterministicRounds.roundUnary amp).result_eq,V40DeterministicRounds.round_value]
  simp only [List.length_replicate]
  rfl

/-- The fixed-round NP front never rejects merely for having many clauses. -/
def fixedFront (K : ℕ) := compose (route 1 (by decide)) (fixedPack D B K)

def fixedFormula (w : List Bool) : ValidFormula := AFront.T10.routed (by decide : 1≤1) w

theorem fixed_front_result (K : ℕ) (w : List Bool) :
    (fixedFront D B K).result w=graphInput (t10Graph D B (fixedFormula w))
      (fixedFormula w).val.variables K := by
  change (fixedPack D B K).result (Front.scanTarget 1 w)=_
  rw [AFront.Route.scanTarget_eq_encode]
  exact fixed_result D B K (fixedFormula w) (AFront.Route.routedFormula_variables w)

theorem fixed_front_sat_iff (w : List Bool) :
    EncodedCNF.Satisfiable (fixedFormula w).val ↔ w∈EncodedCNF.Language :=
  AFront.Route.routedFormula_sat_iff (by decide : 1≤1) w

/-- The existing sparse guard supplies valid finite YES/NO replacements.
It is distinct from the all-language fixed-gap routing above. -/
def sparseRoute (cs cutoff : ℕ) (hcut : 1≤cutoff) : Producer where
  machine := AEth4.route3 (cs+2) cutoff
  result := AEth4.route3Out (cs+2) cutoff
  coefficient := 3000+30*AEth4.phiLen cutoff
  degree := 3
  outputs w := AEth4.route3_outputs (cs+2) cutoff hcut w

def sparseFront (amp cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  compose (sparseRoute cs cutoff hcut) (growingPack D B amp)

def sparseFormula (cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :=
  (⟨AEth4.routed4 (cs+2) cutoff w, AEth4.routed4_valid (cs+2) hcut w⟩ : ValidFormula)

theorem sparse_front_result (amp cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :
    (sparseFront D B amp cs cutoff hcut).result w=
      graphInput (t10Graph D B (sparseFormula cs cutoff hcut w))
        (sparseFormula cs cutoff hcut w).val.variables
        (V39RuntimeETHNumerics.rounds amp (sparseFormula cs cutoff hcut w).val.variables) := by
  change (growingPack D B amp).result (AEth4.route3Out (cs+2) cutoff w)=_
  rw [AEth4.route3Out_eq]
  exact growing_result D B amp (sparseFormula cs cutoff hcut w)
    (hcut.trans (AEth4.routed4_variables (cs+2) cutoff w))

theorem sparse_front_outputs (amp cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :
    (sparseFront D B amp cs cutoff hcut).machine.OutputsWithin w
      (graphInput (t10Graph D B (sparseFormula cs cutoff hcut w))
        (sparseFormula cs cutoff hcut w).val.variables
        (V39RuntimeETHNumerics.rounds amp (sparseFormula cs cutoff hcut w).val.variables))
      ((sparseFront D B amp cs cutoff hcut).coefficient*(w.length+1)^
        (sparseFront D B amp cs cutoff hcut).degree) := by
  simpa only [sparse_front_result] using (sparseFront D B amp cs cutoff hcut).outputs w

#print axioms fixed_front_result
#print axioms fixed_front_sat_iff
#print axioms sparse_front_outputs
end
end CurrentAdditive.V40DeterministicSourcePack
