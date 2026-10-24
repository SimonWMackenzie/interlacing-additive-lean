import CurrentAdditive.GaussPackedClock64
import CurrentAdditive.ClockedPackedWrapper

/-! The checked all-input timeout stage for the fixed packed getter. -/

namespace CurrentAdditive.GaussPackedTimeout

open EthInapproximability.CurrentPaper

noncomputable def result (input : List Bool) : List Bool :=
  ClockedPackedWrapper.result GaussPackedMachine64.machine input

theorem polytime : BitMachine.Polytime result := by
  refine ⟨ClockedPackedWrapper.machine GaussPackedMachine64.machine,
    ClockedPackedWrapper.clockCoefficient GaussPackedMachine64.machine,
    1, ?_⟩
  intro input
  simpa only [result, pow_one] using
    ClockedPackedWrapper.outputs_all_linear
      GaussPackedMachine64.machine input

theorem canonical_packed {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    let bits := GaussPackedFetch64.input B i j
    result (BoundedBitMachine.packed ((bits.length+2)^12) bits) =
      CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j)) := by
  dsimp only
  have h := GaussPackedClock64.canonical_outputs_budget B i j
  have hh := BitMachine.outputsWithin_at_bound
    GaussPackedMachine64.machine h
  rw [result, ClockedPackedWrapper.result_packed, hh.1,
    if_pos rfl, hh.2]

#print axioms polytime
#print axioms canonical_packed

end CurrentAdditive.GaussPackedTimeout
