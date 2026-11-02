import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCost
import EthInapproximability.CurrentPaper.EncodedETHSourceComposition

/-! The cited Dinur bit machine lifted over the second field of a canonical
original-size-bearing packet. The output is CSP bits, not Boolean CNF bits. -/

namespace EthInapproximability.CurrentPaper.SourceDinurPacketMachine

theorem exists_canonical_machine (D : EncodedETHSource.DinurReduction) :
    ∃ (M : BitMachine.Machine) (C E : ℕ),
      ∀ (f : EncodedETHSource.ValidFormula) (originalN : ℕ),
        M.OutputsWithin
          (SourceOriginalBranchPackets.packet originalN (EncodedCNF.encode f.val))
          (SourceOriginalBranchPackets.packet originalN
            (EncodedETHSource.constraintBits (D.reduce f)))
          (C * ((SourceOriginalBranchPackets.packet originalN
            (EncodedCNF.encode f.val)).length + 3)^E) := by
  obtain ⟨N,c,d,hN⟩ := D.polytime
  refine ⟨SourceOriginalPacketLiftMachine.liftMachine N,
    10 * (c+1) * (N.pushBound+1), d+1, ?_⟩
  intro f originalN
  have h := SourceOriginalPacketLiftCost.outputs_polynomial_canonical
    N D.bitFunction c d originalN (EncodedCNF.encode f.val) hN
  rw [D.bitFunction_valid f] at h
  exact h

noncomputable def machine (D : EncodedETHSource.DinurReduction) :
    BitMachine.Machine := (exists_canonical_machine D).choose

theorem machine_outputs (D : EncodedETHSource.DinurReduction) :
    ∃ C E : ℕ,
      ∀ (f : EncodedETHSource.ValidFormula) (originalN : ℕ),
        (machine D).OutputsWithin
          (SourceOriginalBranchPackets.packet originalN (EncodedCNF.encode f.val))
          (SourceOriginalBranchPackets.packet originalN
            (EncodedETHSource.constraintBits (D.reduce f)))
          (C * ((SourceOriginalBranchPackets.packet originalN
            (EncodedCNF.encode f.val)).length + 3)^E) :=
  (exists_canonical_machine D).choose_spec

end EthInapproximability.CurrentPaper.SourceDinurPacketMachine
