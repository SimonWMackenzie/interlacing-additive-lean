import CurrentAdditive.V2ItemFrameLayouts
import CurrentAdditive.V2ItemFrameClock

/-! The fixed Fin64 and Fin32 physical framers have an explicit quadratic
clock in the payload and the disposable bank contents. -/

namespace CurrentAdditive.V2ItemFramePolyLayouts

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open V2ItemFrameCore V2ItemFrameLayouts V2ItemFrameClock

theorem run64 (S : Fin 64 → List Bool) (raw : List Bool)
    (hs : S 23 = raw) :
    ∃ u ≤ coefficient*(inputSize slots64 S raw+1)^2,
      ((advance (program slots64))^[u])
        (⟨some (start slots64), control slots64, S⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
        ⟨none, control slots64,
          Function.update (cleared slots64 S) 5
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  obtain ⟨u, hu, hr⟩ := V2ItemFrameLayouts.run64 S raw hs
  exact ⟨u, hu.trans (time_le slots64 S raw), hr⟩

theorem run32 (S : Fin 32 → List Bool) (raw : List Bool)
    (hs : S 30 = raw) :
    ∃ u ≤ coefficient*(inputSize slots32 S raw+1)^2,
      ((advance (program slots32))^[u])
        (⟨some (start slots32), control slots32, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) _ _) =
        ⟨none, control slots32,
          Function.update (cleared slots32 S) 5
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  obtain ⟨u, hu, hr⟩ := V2ItemFrameLayouts.run32 S raw hs
  exact ⟨u, hu.trans (time_le slots32 S raw), hr⟩

#print axioms run64
#print axioms run32

end CurrentAdditive.V2ItemFramePolyLayouts
