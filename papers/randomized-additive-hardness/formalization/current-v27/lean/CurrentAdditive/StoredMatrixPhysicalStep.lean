import CurrentAdditive.StoredRoundFinishRoutes

/-! One actual stored-matrix round, including all seven constructed sources,
the complete Boolean table, and both canonical rational weight vectors. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredMatrixPhysicalStep
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open PhysicalProducer V40LawJobsClock StoredRoundData
noncomputable section

def next (a : Data) := StoredMatrix.step (q₁ := a.parameters.q₁)
  (s := a.parameters.s) (w := a.parameters.w) (Q := a.parameters.Q)
  a.parameters.μI a.activity a.parameters.R
def output (a : Data) := StoredStepContext.packet a.parameters.q₁ a.parameters.w a.parameters.Q
  a.parameters.μI a.activity (next a)
def cells (a : Data) := MatrixMaterialization.rowMajor
  ((src a).numberedEntry (streams a) (final a) a.parameters.R.entry a.activity)
def columnOutput (a : Data) := V40SuccessorColumnLaw.output (StoredRoundFinishRoutes.columnData a)
def w0 (a : Data) := V40LawPacket.packet (state a 7)
  (V40SuccessorColumnLaw.input (StoredRoundFinishRoutes.columnData a))
def w1 (a : Data) := V40LawPacket.packet (state a 7) (columnOutput a)
def w2 (a : Data) := V40LawPacket.packet (w1 a)
  (StoredActualCells.input (src a) (streams a) (final a) a.parameters.R.entry a.activity)
def w3 (a : Data) := V40LawPacket.packet (w1 a) (cells a)

def routeColumn := pair identity StoredRoundFinishRoutes.columnRequest
def routeCells := pair identity
  (PhysicalProducer.compose (projection (0 : Fin 2)) StoredRoundFinishRoutes.prepared)
def retained := PhysicalProducer.compose (projection (0 : Fin 2)) (projection (0 : Fin 2))
def newCells := projection (1 : Fin 2)
def newRow := PhysicalProducer.compose retained (StoredRoundRoutes.phaseLaw 6)
def newColumn := PhysicalProducer.compose
  (PhysicalProducer.compose (projection (0 : Fin 2)) (projection (1 : Fin 2)))
  (projection (1 : Fin 3))
def finish := pair (PhysicalProducer.compose retained StoredRoundRoutes.context)
  (triple newCells newRow newColumn)

def first := BitMachineComposition.composition StoredRoundStages.machine routeColumn.machine
def second := BitMachineComposition.composition first (V40LawBankMap.liftMachine V40SuccessorColumnLaw.machine)
def third := BitMachineComposition.composition second routeCells.machine
def fourth := BitMachineComposition.composition third (V40LawBankMap.liftMachine StoredActualCells.machine)
def machine := BitMachineComposition.composition fourth finish.machine

theorem routeColumn_result (a : Data) : routeColumn.result (state a 7)=w0 a := by
  simp [routeColumn,w0,StoredRoundFinishRoutes.columnRequest_result]

theorem routeCells_result (a : Data) : routeCells.result (w1 a)=w2 a := by
  simp [routeCells,w1,w2,PhysicalProducer.compose,projection,packet_eq,
    StoredRoundFinishRoutes.prepared_result]

theorem next_bytes (a : Data) : StoredWeightedState.encode (next a)=
    BitMachineBankCodec.encode ![cells a,StoredWeightedState.lawBytes (final a).law,
      StoredWeightedState.lawBytes (V40SuccessorColumnLaw.law
        (StoredRoundFinishRoutes.columnData a))] := by
  have h := StoredWeightedState.SourceData.stored_successor_bytes
    (src a) (streams a) (final a) a.parameters.R.entry a.activity
  rw [←V40SuccessorColumnLaw.actual_column (src a) (streams a)] at h
  exact h

theorem finish_result (a : Data) : finish.result (w3 a)=output a := by
  have hr : (StoredRoundRoutes.phaseLaw 6).result (state a 7)=
      StoredWeightedState.lawBytes (final a).law := by
    rw [StoredRoundRoutes.phaseLaw_result a 6 7 (by decide)]
    rfl
  simp only [finish,pair_result,triple_result,newCells,newRow,newColumn,retained,
    PhysicalProducer.compose,Function.comp_apply,projection,w3,w1,packet_eq,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,hr,StoredRoundRoutes.context_result]
  change BitMachineBankCodec.encode ![_,BitMachineBankCodec.encode ![_,_,_]]=_
  rw [output,StoredStepContext.packet,next_bytes]
  simp [columnOutput,V40SuccessorColumnLaw.output]

theorem realizes : Realizes machine input output := by
  have h0 := producer routeColumn (fun a : Data=>state a 7)
  simp only [routeColumn_result] at h0
  have hc : Realizes V40SuccessorColumnLaw.machine
      (fun a : Data=>V40SuccessorColumnLaw.input (StoredRoundFinishRoutes.columnData a)) columnOutput := by
    obtain ⟨C,E,h⟩ := V40SuccessorColumnLaw.realizes
    exact ⟨C,E,fun a=>h (StoredRoundFinishRoutes.columnData a)⟩
  have h1 := bank_map _ (fun a : Data=>state a 7) _ _ hc
  have h2 := producer routeCells w1
  simp only [routeCells_result] at h2
  have ht : Realizes StoredActualCells.machine
      (fun a : Data=>StoredActualCells.input (src a) (streams a) (final a) a.parameters.R.entry a.activity) cells :=
    ⟨StoredActualCells.coefficient,StoredActualCells.degree,
      fun a=>StoredActualCells.outputs (src a) (streams a) (final a) a.parameters.R.entry a.activity⟩
  have h3 := bank_map _ w1 _ _ ht
  have h4 := producer finish w3
  simp only [finish_result] at h4
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _
          (V40LawJobsClock.compose _ _ _ _ _ StoredRoundStages.realizes h0) h1) h2) h3) h4

def coefficient := Classical.choose realizes
def degree := Classical.choose (Classical.choose_spec realizes)
theorem outputs (a : Data) : machine.OutputsWithin (input a) (output a)
    (coefficient*((input a).length+1)^degree) :=
  Classical.choose_spec (Classical.choose_spec realizes) a

end
end CurrentAdditive.StoredMatrixPhysicalStep

#print axioms CurrentAdditive.StoredMatrixPhysicalStep.outputs
