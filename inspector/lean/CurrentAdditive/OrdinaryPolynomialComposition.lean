import CurrentAdditive.OrdinaryBankFork
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

namespace CurrentAdditive.OrdinaryPolynomialComposition
noncomputable section
open EthInapproximability.CurrentPaper

def coefficient (F : BitMachine.Machine) (a b e : Nat) : Nat :=
  a+2*(a*F.pushBound+1)+b*(a*F.pushBound+1)^e
def degree (d e : Nat) : Nat := (d+1)*(e+1)

/-- A pointwise physical composition theorem. The two child runs are needed
only for the actual intermediate word, rather than for every bit string. -/
theorem outputsWithin (F G : BitMachine.Machine) {x y z : List Bool} {a d b e : Nat}
    (hF : F.OutputsWithin x y (a*(x.length+1)^d))
    (hG : G.OutputsWithin y z (b*(y.length+1)^e)) :
    (BitMachineComposition.composition F G).OutputsWithin x z
      (coefficient F a b e*(x.length+1)^degree d e) := by
  apply BitMachine.outputsWithin_mono _ (BitMachineComposition.composition_outputsWithin F G hF hG)
  exact BitMachineCompositionArithmetic.composition_time_bound x.length a d b e
    F.pushBound y.length (BitMachine.output_length_bound F hF)

theorem fork_outputsWithin (F G : BitMachine.Machine) {x f g : List Bool} {a d b e : Nat}
    (hF : F.OutputsWithin x f (a*(x.length+1)^d))
    (hG : G.OutputsWithin x g (b*(x.length+1)^e)) :
    (OrdinaryBankFork.machine F G).OutputsWithin x (OrdinaryBankFork.packet f g)
      (OrdinaryBankFork.coefficient F G a b*(x.length+1)^OrdinaryBankFork.degree d e) :=
  BitMachine.outputsWithin_mono _ (OrdinaryBankFork.outputsWithin F G hF hG)
    (OrdinaryBankFork.clock_le_polynomial F G x.length a d b e)

#print axioms outputsWithin
#print axioms fork_outputsWithin
end
end CurrentAdditive.OrdinaryPolynomialComposition
