import CurrentAdditive.V39WRawFields
import CurrentAdditive.V39ThreePortFrame

/-! The raw caller starts with exactly three literal words. The fixed bank
enumeration places these last, permitting the existing physical prefixer. -/
namespace CurrentAdditive.V39WRaw
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 16384
open Paper2 EthInapproximability.CurrentPaper
local instance rawInitialStackDecEq : DecidableEq Stack := Classical.decEq _

def graphPort : Stack := .inl (.inl V22RawSamplerJoin.graphPort)
def kPort : Stack := .inl (.inl V22RawSamplerJoin.kPort)
def tapePort : Stack := .inl (.inl V22RawSamplerJoin.tapePort)

theorem graph_ne_k : graphPort ≠ kPort := by
  simp [graphPort,kPort,V22RawSamplerJoin.graphPort,V22RawSamplerJoin.kPort,
    V22FullScheduleBatch.graphPort,V22FullScheduleBatch.kPort]
theorem graph_ne_tape : graphPort ≠ tapePort := by
  simp [graphPort,tapePort,V22RawSamplerJoin.graphPort,V22RawSamplerJoin.tapePort]
theorem k_ne_tape : kPort ≠ tapePort := by
  simp [kPort,tapePort,V22RawSamplerJoin.kPort,V22RawSamplerJoin.tapePort]

theorem initial_only_inputs (graph : List Bool) (K : Nat) (tape : List Bool) :
    initial (V22PublicRepeat.initial (V22RawSamplerJoin.initial graph K tape))=
      V39ThreePortFrame.inputBank graphPort kPort tapePort graph (List.replicate K true) tape := by
  funext j
  rcases j with (r | r) | r
  · simpa only [initial,V22PublicRepeat.initial,Sum.elim_inl,V39ThreePortFrame.inputBank,
      graphPort,kPort,tapePort,Sum.inl.injEq] using V22RawSamplerJoin.initial_only_inputs graph K tape r
  · simp [initial,V22PublicRepeat.initial,V39ThreePortFrame.inputBank,graphPort,kPort,tapePort]
  · simp [initial,V39ThreePortFrame.inputBank,graphPort,kPort,tapePort]

#print axioms initial_only_inputs
end
end CurrentAdditive.V39WRaw
