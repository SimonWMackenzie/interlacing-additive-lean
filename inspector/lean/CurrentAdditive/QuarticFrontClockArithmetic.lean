import CurrentAdditive.QuarticFrontSizeTransfer

/-! Linear arithmetic for the fixed outer copy phases. -/

namespace Paper2.CurrentAdditive.QuarticFrontClockArithmetic

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CurrentAdditive.QuarticFrontLift

noncomputable section

theorem front_clock_linear (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (P : Fin 3 → List Bool) (B : FS → List Bool)
    (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode P).length ≤ Z)
    (hRaw : QuarticNumericFront.Raw27.clock g Δ γ k (P 2) ≤ Z)
    (hAfter : (BitMachineBankCodec.encode (afterRaw P B)).length ≤ Z) :
    clock g Δ γ k P B ≤
      (20 + 5 * Fintype.card SuccessOrient.Stack) * Z := by
  have h1 : 2 * (BitMachineBankCodec.encode P).length + 3 ≤ 5 * Z := by omega
  have h2 : 2 * (BitMachineBankCodec.encode (afterRaw P B)).length + 3 ≤
      5 * Z := by omega
  have hM := Nat.mul_le_mul_left (Fintype.card SuccessOrient.Stack) h2
  have hBefore : clock g Δ γ k P B ≤
      20 * Z + Fintype.card SuccessOrient.Stack * (5 * Z) := by
    unfold clock copyPacketClock copyMasterClock
    omega
  calc
    _ ≤ 20 * Z + Fintype.card SuccessOrient.Stack * (5 * Z) := hBefore
    _ = (20 + 5 * Fintype.card SuccessOrient.Stack) * Z := by ring

#print axioms front_clock_linear

end
end Paper2.CurrentAdditive.QuarticFrontClockArithmetic
