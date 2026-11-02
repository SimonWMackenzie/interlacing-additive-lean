import CurrentAdditive.StoredRoundCompanions
import CurrentAdditive.StoredActualCells

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundProjection
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open StoredRoundData
noncomputable section

/-- The literal packet physically framed from state slot zero and the seven
actual source-phase records. This definition supplies no execution proof. -/
def prepared (a : Data) := BitMachineBankCodec.encode ![
  BitMachineBankCodec.encode ![
    StoredStepContext.context a.parameters.q₁ a.parameters.w a.parameters.Q a.parameters.μI a.activity,
    StoredWeightedState.encode a.parameters.R,sourcePacket a,companionPacket a],
  StoredSourcePhase.tupleBytes (call a 6)]

theorem oldState_eq (a : Data) : StoredWeightedState.encode a.parameters.R=
    StoredCellBytes.baseState (μX := a.parameters.R.rowLaw) (μY := a.parameters.R.colLaw)
      a.parameters.R.entry := rfl

theorem prepared_eq (a : Data) : prepared a=
    StoredActualCells.input (src a) (streams a) (final a) a.parameters.R.entry a.activity := by
  unfold prepared StoredActualCells.input StoredActualCells.push StoredCellBytes.context
  rw [sourcePacket_eq,companionPacket_eq,final_tuples,oldState_eq]

end
end CurrentAdditive.StoredRoundProjection

#print axioms CurrentAdditive.StoredRoundProjection.prepared_eq
