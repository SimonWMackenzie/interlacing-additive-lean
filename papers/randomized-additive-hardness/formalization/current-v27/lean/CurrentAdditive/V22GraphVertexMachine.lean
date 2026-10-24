import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
import EthInapproximability.CurrentPaper.BitMachineEncoding

namespace V22GraphVertexMachine
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open SourceNormalizationMachineDecode
noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl (0 : Fin 8) : Stack) (.inr 0)
    (.inr Admin.capScan) (SourceNormalizationMachineField.initialControl,Phase.count,none)
    program
theorem outputs (g : EncodedGraph.Graph) (hg : g.Valid) :
    machine.OutputsWithin (EncodedGraph.encode g) (List.replicate g.vertices true)
      (100*((EncodedGraph.encode g).length+1)^3) := by
  obtain ⟨t,ht,hr⟩ := decode_valid_run g hg
  have hi : rawInit (.inl (0 : Fin 8) : Stack) (.inr Admin.capScan)
      (SourceNormalizationMachineField.initialControl,Phase.count,none) (EncodedGraph.encode g)=
      start (EncodedGraph.encode g) := by
    unfold rawInit start
    congr 1
    funext j
    cases j with
    | inl j => fin_cases j <;> rfl
    | inr j => fin_cases j <;> rfl
  apply outputsWithin_of_raw_run (.inl (0 : Fin 8) : Stack) (.inr 0)
    (.inr Admin.capScan) (SourceNormalizationMachineField.initialControl,Phase.count,none)
    program (EncodedGraph.encode g) (List.replicate g.vertices true) t _
    (ht.trans (graphCost_polynomial g hg))
  · rw [hi]
    have h := congrArg TM2.Cfg.l hr
    exact h
  · rw [hi]
    have h := congrArg (fun c : Config => c.stk (.inr 0)) hr
    exact h

#print axioms outputs
end V22GraphVertexMachine
