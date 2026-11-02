import CurrentAdditive.GaussPivotInputCharge32

/-! Uniform quadratic time in bytes already present in the initial Fin32 bank. -/

namespace CurrentAdditive.GaussPivotInputOnlyClock32

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

noncomputable section

def inputCoefficient : Nat :=
  GaussPivotQuadraticClock32.totalCoefficient * 101^2

theorem raw_pivot_input_quadratic_clock {m k : Nat}
    (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c,hc⟩ = some pivot)
    (hcount : s.r = s.pivots.length)
    (foreign : Stack → List Bool)
    (hblank : ∀ q : Fin 4,
      foreign (GaussBranchFields32.dest q) = [])
    (htag : foreign 20 = [true])
    (h22 : foreign 22 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B)
    (h25 : foreign 25 = [])
    (h23 : foreign 23 = []) (h24 : foreign 24 = [])
    (h26 : foreign 26 = []) (h27 : foreign 27 = [])
    (h28 : foreign 28 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      foreign (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ inputCoefficient *
        (GaussPivotInputBytes32.inputBytes s foreign + 1)^2,
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  obtain ⟨t,ht,he,hpacket⟩ :=
    GaussPivotQuadraticClock32.raw_pivot_quadratic_clock
      s hr hc pivot hp hcount foreign hblank htag h22 h25
      h23 h24 h26 h27 h28 hempty
  let I := GaussPivotInputBytes32.inputBytes s foreign
  let B := GaussPivotByteSize32.byteCharge s foreign hr hc
  let K := GaussPivotQuadraticClock32.totalCoefficient
  have hb := GaussPivotInputCharge32.byteCharge_le_input
    s foreign hr hc hcount hblank h22
  have hb' : B+1 ≤ 101*(I+1) := by
    dsimp [B,I] at *
    omega
  have hpow := Nat.pow_le_pow_left hb' 2
  have hmul := Nat.mul_le_mul_left K hpow
  have hpoly : K*(B+1)^2 ≤ inputCoefficient*(I+1)^2 := by
    calc
      _ ≤ K*(101*(I+1))^2 := hmul
      _ = inputCoefficient*(I+1)^2 := by
        dsimp [inputCoefficient,K]
        ring
  exact ⟨t, ht.trans hpoly, he, hpacket⟩

#print axioms raw_pivot_input_quadratic_clock

end
end CurrentAdditive.GaussPivotInputOnlyClock32
