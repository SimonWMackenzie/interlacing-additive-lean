import EthInapproximability.CurrentPaper.WeightedQCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Actual m production and physical q₂-to-threshold-input copying on one
Fin64 ⊕ Fin15 Boolean-stack bank. -/

namespace EthInapproximability.CurrentPaper.WeightedMQJoin

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := WeightedMWidth.Stack

def program := BitMachineRawSequence.program
  WeightedMJoin.program WeightedQCopy.program BitMachineCopy.Label.scan
  WeightedMJoin.initial (none : Option Bool)
def initial := (WeightedMJoin.initial,(none : Option Bool))

def cost (a rx q : ℕ) : ℕ := WeightedMJoin.cost a rx + (2*q+2) + 1

theorem run (S : Stack → List Bool) (a rx q : ℕ)
    (ha : S (WeightedMWidth.writer 54) = List.replicate a true)
    (hrx : S (WeightedMWidth.writer 17) = List.replicate rx true)
    (hq : S (WeightedMWidth.writer 56) = List.replicate q true)
    (h0 : S (WeightedMWidth.scalar 0) = [])
    (h2 : S (WeightedMWidth.scalar 2) = [])
    (h3 : S WeightedMWidth.width = [])
    (h4 : S (WeightedMWidth.scalar 4) = [])
    (h5 : S (WeightedMWidth.scalar 5) = [])
    (h6 : S (WeightedMWidth.scalar 6) = [])
    (h10 : S (WeightedMWidth.scalar 10) = []) :
    ∃ t ≤ cost a rx q,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel (Sum.inr false))))),
          initial,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,initial,
          Function.update
            (Function.update S (WeightedMWidth.scalar 2)
              (List.replicate (Construction.qOne a * rx) true))
            (WeightedMWidth.scalar 0) (List.replicate q true)⟩ := by
  let M := Function.update S (WeightedMWidth.scalar 2)
    (List.replicate (Construction.qOne a * rx) true)
  obtain ⟨tm,htm,hm⟩ := WeightedMJoin.run S a rx
    ha hrx h2 h3 h4 h5 h6
  have hqM : M (WeightedMWidth.writer 56) =
      List.replicate q true := by
    simpa [M,WeightedMWidth.writer,WeightedMWidth.scalar] using hq
  have h0M : M (WeightedMWidth.scalar 0) = [] := by
    simpa [M,WeightedMWidth.scalar] using h0
  have h10M : M (WeightedMWidth.scalar 10) = [] := by
    simpa [M,WeightedMWidth.scalar] using h10
  have hcopy := WeightedQCopy.run M q hqM h0M h10M
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    WeightedMJoin.program WeightedQCopy.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (Sum.inr false))))
    BitMachineCopy.Label.scan
    WeightedMJoin.initial WeightedMJoin.initial
    (none : Option Bool) none
    S M (Function.update M (WeightedMWidth.scalar 0)
      (List.replicate q true))
    tm (2*q+2) (by simpa only [M] using hm) hcopy
  refine ⟨t,by dsimp [cost]; omega,?_⟩
  simpa only [program,initial,M] using hr

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedMQJoin
