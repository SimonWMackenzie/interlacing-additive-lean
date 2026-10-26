import Paper2.BrPacket

/-! Lane a-bridge-owner-1: finiteness of the label and control types of the
segment-1 controller (needed by the admitted finite-program bank wrapper and
by the admitted stack-growth bound). Pure type-level instances; no machine,
no premise. The recursive list-indexed types of `CopyList` and
`SamplerAlphabetMachine` get their instances by the same recursion. -/

set_option maxHeartbeats 4000000

deriving instance Fintype for Paper2.SamplerLoopDraw.Label

namespace Paper2.ABridge

open Turing EthInapproximability.CurrentPaper

@[reducible] def ftCopyLabel {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Label xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => @instFintypeSum _ _ inferInstance (@instFintypeSum Unit _ _ (ftCopyLabel xs))

@[reducible] def ftCopyControl {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Control xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => @instFintypeProd _ _ inferInstance (ftCopyControl xs)

instance instFtCopyLabel {K : Type} [DecidableEq K] (xs : List (Fin 3 ↪ K)) :
    Fintype (CopyList.Label xs) := ftCopyLabel xs
instance instFtCopyControl {K : Type} [DecidableEq K] (xs : List (Fin 3 ↪ K)) :
    Fintype (CopyList.Control xs) := ftCopyControl xs

@[reducible] def ftAlphaLabel : (xs : List SamplerAlphabetMachine.Source) →
    Fintype (SamplerAlphabetMachine.Label xs)
  | [] => inferInstanceAs (Fintype (SourceClauseFixedUnary.Label 514))
  | _ :: xs => @instFintypeSum _ _ (ftAlphaLabel xs) (@instFintypeSum Unit _ _ inferInstance)

@[reducible] def ftAlphaControl : (xs : List SamplerAlphabetMachine.Source) →
    Fintype (SamplerAlphabetMachine.Control xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => @instFintypeProd _ _ (ftAlphaControl xs) inferInstance

instance instFtAlphaLabel (xs : List SamplerAlphabetMachine.Source) :
    Fintype (SamplerAlphabetMachine.Label xs) := ftAlphaLabel xs
instance instFtAlphaControl (xs : List SamplerAlphabetMachine.Source) :
    Fintype (SamplerAlphabetMachine.Control xs) := ftAlphaControl xs

noncomputable section
abbrev labelT {K L V : Type} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type := L
abbrev ctlT {K L V : Type} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type := V
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instFtPacketLabel (a b Δ : ℕ) : Fintype (labelT (packetProgram a b Δ)) := by
  unfold labelT; infer_instance
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instFtPacketCtl (a b Δ : ℕ) : Fintype (ctlT (packetProgram a b Δ)) := by
  unfold ctlT; infer_instance
/-- The per-transition push bound of the segment-1 controller. -/
def packetPerStep (a b Δ : ℕ) : ℕ :=
  letI := instFtPacketLabel a b Δ
  BitMachineStackGrowth.perStep (packetProgram a b Δ)

/-- Admitted stack-growth bound, instantiated at the segment-1 controller. -/
theorem packet_growth (a b Δ : ℕ)
    (c : TM2.Cfg (fun _ : FullFront.JF => Bool) (labelT (packetProgram a b Δ))
      (ctlT (packetProgram a b Δ))) (t : ℕ) (x : FullFront.JF) :
    ((((BitMachineEncoding.advance (packetProgram a b Δ))^[t]) c).stk x).length ≤
      (c.stk x).length + packetPerStep a b Δ * t := by
  letI := instFtPacketLabel a b Δ
  exact BitMachineStackGrowth.run_growth (packetProgram a b Δ) c t x
end

end Paper2.ABridge
