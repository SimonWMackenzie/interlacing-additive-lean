import EthInapproximability.CurrentPaper.MatrixWeightedActualPhysicalStep
import EthInapproximability.CurrentPaper.MatrixWeightedEntryEnvelope

/-!
Prepared-bank polynomial normalization for the one-step protected physical
writer/bridge/outer program. Source: frozen replacement v8, Appendix B,
`thm:paper-materialization` and `eq:paper-materialization-runtime`.
-/

namespace EthInapproximability.CurrentPaper.ProtectedBudgetNormalizationScratch

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.CurrentPaper.ProtectedFullBankBridgeScratch

noncomputable section

set_option maxHeartbeats 1000000

private def outerPoly (rank count skip K : ℕ) : ℕ :=
  (K + 1) *
    (2 * count + 2 * skip + 7 +
      (count + 1) * (2 * (rank + K * (count + skip) + count) + 5))

private def prepPoly (v a K : ℕ) : ℕ :=
  4 * K + 4 + (K * (v + a) + 1) + (2 * v + 2) +
    2 * outerPoly 0 v a K + 2 * outerPoly v a v K + 1 +
    v + a + K + (v + K * (a + v)) + 10

private theorem prepCost_eq (v a K : ℕ) :
    MatrixWeightedOrderPreparation.prepCost v a K = prepPoly v a K := rfl

/-- The previously admitted preparation formula is uniformly quartic in
the three physically supplied unary size parameters. -/
theorem prepCost_quartic (v a K E : ℕ)
    (hv : v ≤ E) (ha : a ≤ E) (hK : K ≤ E) (hE : 1 ≤ E) :
    MatrixWeightedOrderPreparation.prepCost v a K ≤ 400 * E^4 := by
  have hmono : MatrixWeightedOrderPreparation.prepCost v a K ≤
      MatrixWeightedOrderPreparation.prepCost E E E := by
    rw [prepCost_eq, prepCost_eq]
    unfold prepPoly outerPoly
    gcongr
  have hdiag : MatrixWeightedOrderPreparation.prepCost E E E ≤
      400 * E^4 := by
    rw [prepCost_eq]
    unfold prepPoly outerPoly
    have h2 : E ≤ E^2 := by
      nlinarith [Nat.mul_le_mul_left E hE]
    have h3 : E^2 ≤ E^3 := by
      nlinarith [Nat.mul_le_mul_left (E^2) hE]
    have h4 : E^3 ≤ E^4 := by
      nlinarith [Nat.mul_le_mul_left (E^3) hE]
    have h1 : 1 ≤ E^4 := by omega
    nlinarith
  exact hmono.trans hdiag

/-- A table-independent size envelope for the outer machine. Its large
terms are exactly the two interlaced output dimensions and their products. -/
def outerSize (R r rows cols b c s lambda : ℕ) : ℕ :=
  let W := 2^r
  let B := 2^R
  let X := W * rows
  let Y := cols^W
  lambda + W +
    (b + c + s + W + B +
      (W + rows + cols + rows*cols + X + Y + X*Y + 1) +
      (B + Y + X + Y*X + B*Y + X^B + (B*Y)*(X^B) + 1) + 1) + 1

theorem outerScale_eq_outerSize (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceOuterJoin.scale R r rows cols b c s lambda f =
      outerSize R r rows cols b c s lambda := by
  simp [MatrixTableInterlaceOuterJoin.scale,
    MatrixTableInterlaceScalarJoin.scale,
    MatrixTableInterlaceDouble.firstScale,
    MatrixTableInterlaceDouble.secondScale,
    MatrixTableInterlaceDouble.firstRowsCount,
    MatrixTableInterlaceDouble.firstColsCount,
    MatrixTableInterlaceFirstFinish.word,
    MatrixMaterialization.rowMajor_length, outerSize]

def coefficient : ℕ :=
  20 * 640003^3 + 400 + 8 +
    (16194 + 4 * UnaryBinaryEncoding.coefficient) + 1

/-- Generic algebraic normalization of the three existing physical clock
bounds. The cell-cost premise is a proved explicit size bound, not a
supplied halting-time or desired-output certificate. -/
theorem prepared_budget_bound
    (v a K rows cols R r b c s lambda E S T : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hE : 1 ≤ E) (hv : v ≤ E) (ha : a ≤ E) (hK : K ≤ E)
    (hr : rows ≤ E) (hc : cols ≤ E) (hS : S ≤ E)
    (hQ : outerSize R r rows cols b c s lambda ≤ E)
    (hT : T ≤ 10000 * (3*S^2+1)^3)
    (hq : MatrixOuterWidthMachine.width lambda = 2^r)
    (hB : MatrixRestorationWidthMachine.width b c s (2^r) = 2^R) :
    MatrixWeightedOrderPreparation.prepCost v a K +
      MatrixTableWriter.writerBound rows cols T + 1 +
      MatrixTableInterlaceProtectedBridge.transferTime rows cols
        (MatrixMaterialization.rowMajor f) +
      MatrixTableInterlaceOuterJoin.totalBound R r rows cols
        b c s lambda f ≤ coefficient * E^18 := by
  have hE2 : E ≤ E^2 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hE (by omega : 1 ≤ 2))
  have hE6 : E ≤ E^6 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hE (by omega : 1 ≤ 6))
  have h1E2 : 1 ≤ E^2 := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ hE (by omega : 0 ≤ 2))
  have h1E6 : 1 ≤ E^6 := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ hE (by omega : 0 ≤ 6))
  have hE2to18 : E^2 ≤ E^18 :=
    pow_le_pow_right₀ hE (by omega)
  have hE4to18 : E^4 ≤ E^18 :=
    pow_le_pow_right₀ hE (by omega)
  have hE6to18 : E^6 ≤ E^18 :=
    pow_le_pow_right₀ hE (by omega)
  have h1E18 : 1 ≤ E^18 := by omega
  have hprep : MatrixWeightedOrderPreparation.prepCost v a K ≤
      400 * E^18 :=
    (prepCost_quartic v a K E hv ha hK hE).trans
      (Nat.mul_le_mul_left 400 hE4to18)
  have hS2 : S^2 ≤ E^2 := Nat.pow_le_pow_left hS 2
  have harg : 3*S^2+1 ≤ 4*E^2 := by omega
  have hT' : T ≤ 640000 * E^6 := by
    calc
      T ≤ 10000 * (3*S^2+1)^3 := hT
      _ ≤ 10000 * (4*E^2)^3 := by gcongr
      _ = 640000 * E^6 := by ring
  have hwriterArg : rows + cols + T + 1 ≤ 640003 * E^6 := by
    have hr' : rows ≤ E^6 := hr.trans hE6
    have hc' : cols ≤ E^6 := hc.trans hE6
    omega
  have hwriter : MatrixTableWriter.writerBound rows cols T ≤
      (20 * 640003^3) * E^18 := by
    calc
      _ ≤ 20 * (rows+cols+T+1)^3 :=
        MatrixTableWriter.writerBound_polynomial rows cols T
      _ ≤ 20 * (640003*E^6)^3 := by gcongr
      _ = (20*640003^3)*E^18 := by ring
  have hword : (MatrixMaterialization.rowMajor f).length =
      rows*cols := MatrixMaterialization.rowMajor_length f
  have hmul : rows*cols ≤ E^2 := by
    nlinarith [Nat.mul_le_mul hr hc]
  have htransfer :
      MatrixTableInterlaceProtectedBridge.transferTime rows cols
        (MatrixMaterialization.rowMajor f) ≤ 8 * E^18 := by
    have hsmall : MatrixTableInterlaceProtectedBridge.transferTime
        rows cols (MatrixMaterialization.rowMajor f) ≤ 8*E^2 := by
      dsimp [MatrixTableInterlaceProtectedBridge.transferTime]
      rw [hword]
      omega
    exact hsmall.trans (Nat.mul_le_mul_left 8 hE2to18)
  have houter : MatrixTableInterlaceOuterJoin.totalBound R r rows cols
      b c s lambda f ≤
      (16194+4*UnaryBinaryEncoding.coefficient)*E^18 := by
    have hpoly := MatrixTableInterlaceOuterJoin.totalBound_polynomial
      R r rows cols b c s lambda f hq hB
    rw [outerScale_eq_outerSize] at hpoly
    exact hpoly.trans ((Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hQ 4)).trans
      (Nat.mul_le_mul_left _ hE4to18))
  calc
    _ ≤ 400*E^18 + (20*640003^3)*E^18 + E^18 +
        8*E^18 +
        (16194+4*UnaryBinaryEncoding.coefficient)*E^18 := by omega
    _ = coefficient * E^18 := by dsimp [coefficient]; ring

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

/-- Explicit prepared-bank and output-dimension envelope. No machine clock,
cost maximum, or value-dependent table word occurs in this definition. -/
def preparedEnvelope : ℕ :=
  let P := actualP G sourceConstant b y level M
  let R := Iteration.rQ G sourceConstant b y level M
  let r := Iteration.rq G sourceConstant b y level M
  let rows := actualRows G sourceConstant b y level M
  let cols := actualCols G sourceConstant b y level M
  let d := actualD G sourceConstant b y level M
  let s := Iteration.s G sourceConstant b y level M
  1 + Fintype.card VG + (s-3) + 4*s + rows + cols +
    MatrixWeightedEntryEnvelope.inputScale d rows cols +
    outerSize R r rows cols P.nextDepth P.sourceConstant
      (Parameters.bins P) (Parameters.scale P)

/-- The actual one-step physical clock has a fixed degree and coefficient
in explicit prepared source/scalar lengths and two-interlace dimensions. -/
theorem actualPhysicalBudget_prepared_polynomial :
    actualPhysicalBudget G sourceConstant b y level M ≤
      coefficient * (preparedEnvelope G sourceConstant b y level M)^18 := by
  let P := actualP G sourceConstant b y level M
  let R := Iteration.rQ G sourceConstant b y level M
  let r := Iteration.rq G sourceConstant b y level M
  let rows := actualRows G sourceConstant b y level M
  let cols := actualCols G sourceConstant b y level M
  let f := actualF G sourceConstant b y level M
  let d := actualD G sourceConstant b y level M
  let order := GraphVectors.itemOrder G
    (Iteration.s G sourceConstant b y level M)
  let s := Iteration.s G sourceConstant b y level M
  let S := MatrixWeightedEntryEnvelope.inputScale d rows cols
  let Q := outerSize R r rows cols P.nextDepth P.sourceConstant
    (Parameters.bins P) (Parameters.scale P)
  let E := preparedEnvelope G sourceConstant b y level M
  have hEnvelope : E =
      1 + Fintype.card VG + (s-3) + 4*s + rows + cols + S + Q := rfl
  have hbin := MatrixWeightedProtectedWriterIteration.actual_binBase_ge_two
    G sourceConstant b y level M
  have hT : MatrixWeightedEntryCost.commonCost d rows cols order ≤
      10000*(3*S^2+1)^3 := by
    simpa only [d,actualD,rows,actualRows,cols,actualCols,
      Iteration.NRow,Iteration.NCol,S,order,s] using
      (MatrixWeightedEntryEnvelope.actual_commonCost_poly M.entry
        (Iteration.a G sourceConstant b y level M)
        (Iteration.s G sourceConstant b y level M)
        (Iteration.q₂ G sourceConstant b y level M)
        (Iteration.labels G sourceConstant b y level M)
        (GraphVectors.vertexCount VG
          (Iteration.s G sourceConstant b y level M))
        (GraphVectors.auxiliaryCount
          (Iteration.s G sourceConstant b y level M))
        (lt_of_lt_of_le (by decide : 0 < 4)
          (Iteration.bins_ge_four G sourceConstant b y level M))
        M.columns_pos hbin
        (Iteration.secondFamily G sourceConstant b y level M)
        (GraphVectors.itemOrder G
          (Iteration.s G sourceConstant b y level M))
        (GraphVectors.vectors G
          (Iteration.s G sourceConstant b y level M))
        (GraphVectors.supportCap G
          (le_trans (by decide : 3 ≤ 4)
            (Iteration.bins_ge_four G sourceConstant b y level M))))
  have hq : MatrixOuterWidthMachine.width (Parameters.scale P) = 2^r := by
    simpa only [Parameters.outerWidth] using
      (MatrixOuterWidthMachine.width_eq_parameters P)
  have hB : MatrixRestorationWidthMachine.width P.nextDepth
      P.sourceConstant (Parameters.bins P) (2^r) = 2^R := by
    simpa only [Parameters.outerWidth,Parameters.restorationWidth] using
      (MatrixRestorationWidthMachine.width_eq_parameters P)
  have hE : 1 ≤ E := by rw [hEnvelope]; omega
  have hv : Fintype.card VG ≤ E := by
    rw [hEnvelope]; omega
  have ha : s-3 ≤ E := by
    rw [hEnvelope]; omega
  have hK : 4*s ≤ E := by
    rw [hEnvelope]; omega
  have hr : rows ≤ E := by
    rw [hEnvelope]; omega
  have hc : cols ≤ E := by
    rw [hEnvelope]; omega
  have hS : S ≤ E := by rw [hEnvelope]; omega
  have hQ : outerSize R r rows cols P.nextDepth P.sourceConstant
      (Parameters.bins P) (Parameters.scale P) ≤ E := by
    change Q ≤ E
    rw [hEnvelope]
    omega
  have h := prepared_budget_bound (Fintype.card VG) (s-3) (4*s)
    rows cols R r P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.scale P) E S
    (MatrixWeightedEntryCost.commonCost d rows cols order) f
    hE hv ha hK hr hc hS hQ hT hq hB
  simpa only [actualPhysicalBudget,actualWriterBound,
    E,P,R,r,rows,cols,f,d,order,s] using h

/-- The normalized clock bounds the actual single-program execution, not
merely its separately defined budget expression. -/
theorem actualPhysicalStep_run_prepared_polynomial :
    ∃ t ≤ coefficient *
        (preparedEnvelope G sourceConstant b y level M)^18,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        MatrixTableInterlaceProtectedBridge.run t
          (actualPhysicalStart G sourceConstant b y level M) = z ∧
        z.l = none ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          actualPhysicalOutput G sourceConstant b y level M := by
  obtain ⟨t,ht,z,hz,hh,ho⟩ :=
    ProtectedFullBankBridgeScratch.actual_physical_step_run
      G sourceConstant b y level M
  exact ⟨t, ht.trans (actualPhysicalBudget_prepared_polynomial
    G sourceConstant b y level M), z, hz, hh, ho⟩


end
end EthInapproximability.CurrentPaper.ProtectedBudgetNormalizationScratch
