import CurrentAdditive.V42RawMidpointRequest
import CurrentAdditive.V42WRawInitial
namespace CurrentAdditive.V42RawRequestPacket
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
open Turing EthInapproximability.CurrentPaper
open V42RawMidpointRequest

def labelType {S L V : Type} (_ : L → TM2.Stmt (fun _ : S => Bool) L V) : Type := L
def controlType {S L V : Type} (_ : L → TM2.Stmt (fun _ : S => Bool) L V) : Type := V
abbrev Label := labelType V42RawMidpointRequest.program
abbrev Control := controlType V42RawMidpointRequest.program
instance stackFintype : Fintype V42RawMidpointRequest.Stack := by infer_instance
instance labelFintype : Fintype Label := by unfold Label labelType; infer_instance
instance controlFintype : Fintype Control := by unfold Control controlType; infer_instance
end
end CurrentAdditive.V42RawRequestPacket

