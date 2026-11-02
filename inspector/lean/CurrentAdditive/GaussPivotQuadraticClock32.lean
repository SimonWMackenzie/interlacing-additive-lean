import CurrentAdditive.GaussPivotByteSize32

/-! An explicit fixed quadratic envelope for the actual pivot writer run. -/

namespace CurrentAdditive.GaussPivotQuadraticClock32

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

noncomputable section

def totalCoefficient : Nat :=
  GaussPivotPolynomial32.polynomialCoefficient *
    (GaussPivotByteSize32.quadraticCoefficient+1)

theorem raw_pivot_quadratic_clock {m k : Nat}
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
    ∃ t ≤ totalCoefficient *
        (GaussPivotByteSize32.byteCharge s foreign hr hc + 1)^2,
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  obtain ⟨t,ht,he,hpckt⟩ :=
    GaussPivotFinalPolynomial32.raw_pivot_polynomial_clock
      s hr hc pivot hp hcount foreign hblank htag h22 h25
      h23 h24 h26 h27 h28 hempty
  let N := GaussPivotByteSize32.byteCharge s foreign hr hc
  let Q := GaussPivotByteSize32.quadraticCoefficient
  let K := GaussPivotPolynomial32.polynomialCoefficient
  have hs : GaussPivotPolynomial32.staticCharge s foreign hr hc ≤
      Q*(N+1)^2 :=
    GaussPivotByteSize32.staticCharge_quadratic s foreign hr hc
  have hone : 1 ≤ (N+1)^2 := by
    simpa using (Nat.pow_le_pow_left (show 1 ≤ N+1 by omega) 2)
  have hsize : GaussPivotPolynomial32.staticCharge s foreign hr hc+1 ≤
      (Q+1)*(N+1)^2 := by
    calc
      _ ≤ Q*(N+1)^2+1 := by omega
      _ ≤ (Q+1)*(N+1)^2 := by
        simp only [Nat.add_mul, one_mul]
        omega
  have hmul := Nat.mul_le_mul_left K hsize
  exact ⟨t, ht.trans (by simpa [totalCoefficient,N,Q,K,
    Nat.mul_assoc] using hmul), he, hpckt⟩

#print axioms raw_pivot_quadratic_clock

end
end CurrentAdditive.GaussPivotQuadraticClock32
