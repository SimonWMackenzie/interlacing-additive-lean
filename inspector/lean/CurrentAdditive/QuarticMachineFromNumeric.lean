import CurrentAdditive.QuarticFrontComposition
import CurrentAdditive.QuarticMachineWrapper

/-! A single remaining physical numeric-preparer premise feeds the exact
v27 local machine and its charged external bit-machine wrapper. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticMachineFromNumeric

open Turing
open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontComposition
open Paper2.CurrentAdditive.QuarticMachineWrapper

theorem H_A3_27_of_numeric (FS : Type) [Fintype FS] [DecidableEq FS]
    (A B : FS) (hAB : A ≠ B)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    {L V : Type} [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (s : L) (v : V) (C E : ℕ)
    (hPrep : NumericPrep27 FS A B Δ γ P s v C E) :
    H_A3_27 Δ γ := by
  exact H_A3_27_of_front FS Δ γ hΔ hγ
    (frontProg27 FS A B Δ γ P v)
    (BitMachineRawSequence.leftLabel s)
    (v, CheckBit.ctl0 (QuarticCheckBit.NA27 Δ γ)
      (QuarticCheckBit.NB27 Δ γ))
    (frontClockC27 FS A B Δ γ C) (frontClockE27 E)
    (frontClockC27 FS A B Δ γ C) (frontClockE27 E)
    (front_of_numeric27 FS A B hAB Δ γ hγ hΔ P s v C E hPrep)

#print axioms H_A3_27_of_numeric

end Paper2.CurrentAdditive.QuarticMachineFromNumeric
