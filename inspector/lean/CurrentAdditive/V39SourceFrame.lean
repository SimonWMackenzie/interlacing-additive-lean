import CurrentAdditive.V39SourcePacket
import CurrentAdditive.V39ThreePortFrame
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39SourceFront
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  {S : Type} [Fintype S] [DecidableEq S]
  (gPort kPort tPort : S) (hgk : gPort ≠ kPort) (hgt : gPort ≠ tPort) (hkt : kPort ≠ tPort)

def framedBank {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :=
  fun i => V39ThreePortFrame.inputBank gPort kPort tPort
    (EncodedGraph.encode (graph D B hcutoff w)) (List.replicate (gap hcutoff w) true) tape
    ((V39ThreePortFrame.number gPort kPort tPort hgk hgt hkt).symm i)

/-- Every work cell is physically framed blank. The only nonblank inputs
are the computed source graph, computed unary k and retained raw tape. -/
theorem all_input_framed {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ w tape : List Bool,
      M.OutputsWithin (EncodedComplexity.pair w tape)
        (BitMachineBankCodec.encode (framedBank D B gPort kPort tPort hgk hgt hkt hcutoff w tape))
        (C*((EncodedComplexity.pair w tape).length+1)^E) := by
  obtain ⟨M,C,E,hM⟩ := all_input_packet D B hcutoff
  let a := V39ThreePortFrame.workCount gPort kPort tPort
  refine ⟨BitMachineComposition.composition M (Unit4Post.Pre.machine a),
    C+2*(C*M.pushBound+1)+(a+1),E+1,?_⟩
  intro w tape
  have h1 := hM w tape
  have h2 := V39ThreePortFrame.frame_outputs gPort kPort tPort hgk hgt hkt
    (EncodedGraph.encode (graph D B hcutoff w)) (List.replicate (gap hcutoff w) true) tape
  have hc := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  apply BitMachine.outputsWithin_mono _ hc
  have hl := BitMachine.output_length_bound M h1
  have h := BitMachineCompositionArithmetic.composition_time_bound
    (EncodedComplexity.pair w tape).length C E (a+1) 0 M.pushBound
    (packet D B hcutoff w tape).length hl
  simpa only [pow_zero,mul_one,Nat.add_zero,Nat.zero_add] using h

end
end CurrentAdditive.V39SourceFront

#print axioms CurrentAdditive.V39SourceFront.all_input_framed
