import CurrentAdditive.QuarticTailComposition
import Paper2.E6Cut
import Paper2.E3Inner

/-!
The fixed decision-machine skeleton for the literal v27 square word.  The
core theorem exposes the tail run as a premise so the large physical header
clock does not enter elaboration of the routing/cutter proof.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

set_option maxHeartbeats 2000000

noncomputable def sourceCore27 (tail : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition
    (Paper2.Unit4Shell.PairMap.machine Paper2.AEth3.Fst.machine) tail

noncomputable def sourceCoreClock27 (Φ : EncodedCNF.Formula)
    (raw : List Bool) (Ttail : ℕ) : ℕ :=
  let e := EncodedCNF.encode Φ
  let f := Paper2.AEth3.fOut Φ
  let Tfst := 2 * e.length + 3
  let Tmap := 2 * f.length + Tfst + 2 * e.length + 6
  Tmap + 2 * (EncodedComplexity.pair e raw).length + 2 + Ttail

theorem sourceCore27_outputs (tail : BitMachine.Machine)
    (Φ : EncodedCNF.Formula) (raw w : List Bool) (Ttail : ℕ)
    (htail : tail.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw) w Ttail) :
    (sourceCore27 tail).OutputsWithin
      (EncodedComplexity.pair (Paper2.AEth3.fOut Φ) raw) w
      (sourceCoreClock27 Φ raw Ttail) := by
  have hfst := Paper2.AEth3.Fst.machine_outputs (EncodedCNF.encode Φ)
    (EncodedComplexity.pair
      (List.replicate (Paper2.AEth.expLen Φ.variables) true) [])
  have hmap := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := Paper2.AEth3.Fst.machine)
    (Paper2.AEth3.fOut Φ) (EncodedCNF.encode Φ) raw _ hfst
  have hcore := BitMachineComposition.composition_outputsWithin
    (Paper2.Unit4Shell.PairMap.machine Paper2.AEth3.Fst.machine)
    tail hmap htail
  simpa only [sourceCore27, sourceCoreClock27] using hcore

#print axioms sourceCore27_outputs

end Paper2.CurrentAdditive.QuarticClassEndpoint
