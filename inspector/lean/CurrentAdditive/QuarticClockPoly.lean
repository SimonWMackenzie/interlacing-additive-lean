import CurrentAdditive.QuarticClockEnvelope
import Paper2.E6DecClock

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem decisionEnvelope_poly27 (C : Paper2.SelectedTape.Algorithm) :
    Paper2.Unit4Shell.Poly.PolyIn id
      (fun Z => 5000 * (Z + 1) + Paper2.AEth5.clsTime C Z Z) := by
  unfold Paper2.AEth5.clsTime NPOwner1.Trunc.timeBound
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

#print axioms decisionEnvelope_poly27

end Paper2.CurrentAdditive.QuarticClassEndpoint
