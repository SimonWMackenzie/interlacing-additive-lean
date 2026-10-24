import EthInapproximability.CurrentPaper.G5bBoundJNamed
import EthInapproximability.CurrentPaper.W12C1j

/-!
# Named (arbitrary-p) bounds for `outerBoundJ` and the carrier terms of `readyBoundJ`,
# and the reduction of `prepBoundJ` to the installed-bank clear sum
(private lane owner:b-g5-2, segment 1 support; NOT the materialization theorem)

`LevelJPrep.prepBoundJ = readyBoundJ + outerBoundJ + 1`,
`readyBoundJ = cleanBoundJ + (carrier terms in actualRows, actualCols)` (admitted
`W12ReadyJ.ready_splitJ`), `cleanBoundJ = boundJ + Σ_k |C1j (clearCells k)| + nClear·ps3·boundJ
+ nClear + 3` (admitted `W12ReadyJ.cleanJ_split`). This module bounds `outerBoundJ` (through the
admitted generic `ClockP.outer_generic`) and the carrier terms at an ARBITRARY named level, and
states `prepBoundJ` with the ONLY unbounded term the installed-bank clear sum
`Σ_k |C1j (clearCells k)|` (`prep_named`).

NOT claimed: a bound on the clear sum; the level-0 analogues; any total machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5bPrepNamed

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualOrderFromCarrier

set_option maxHeartbeats 3000000

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- The admitted outer preparation clock at an arbitrary named level. -/
theorem outer_named : ∃ K : ℕ, ∀ (i : LI) (p : ℕ), SourceNames i p →
    LevelJPrep.outerBoundJ i.G i.c i.b i.y i.lv i.M ≤
      K * (3 * 2 ^ p + 2 * ell3 i.G + 7) ^ 2 := by
  refine ⟨(1 + OuterLevel0Prep.nS * BitMachineStackGrowth.perStep ETHScaleActualComplete.program) *
      ClockP.Kp + 33554432 + 2 * ClockC.binsConst + 4 * OuterLevel0Prep.nS + 30,
    fun i p h => ?_⟩
  have hsc := from_clog h.sourceDescription
  have hco := from_clog h.costDescription
  have hnd : (PL i).nextDepth ≤ 2 ^ p :=
    h.restrictionDepth.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hrx := from_clog h.inputRows
  have hcy := from_clog h.inputCols
  have hp2 : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self
  have hE := card_le_ell3 i.G
  have hedges : (PL i).edges = Fintype.card i.E := rfl
  have hclogE : Nat.clog 2 ((PL i).edges + 2) ≤ (PL i).edges + 2 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hnl : Parameters.namingLength (PL i) ≤ p := by
    unfold Parameters.namingLength
    exact max_le h.inputRows h.inputCols
  have hSB : Parameters.scaleBound (PL i) ≤ 2 ^ p + ell3 i.G + 2 := by
    unfold Parameters.scaleBound
    simp only [max_le_iff]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hb : i.b ≤ 2 ^ p + ell3 i.G + 2 := by
    have : i.b = (PL i).nextDepth := rfl
    omega
  have hc : i.c ≤ 2 ^ p + ell3 i.G + 2 := by
    have : i.c = (PL i).sourceConstant := rfl
    omega
  have hR : (PL i).rows + (PL i).columns + (PL i).edges ≤ 2 * 2 ^ p + ell3 i.G := by
    have h1 : (PL i).rows = rxI i := rfl
    have h2 : (PL i).columns = cyI i := rfl
    omega
  have hg := ClockP.outer_generic (PL i) i.b i.c (2 ^ p + ell3 i.G + 2) (2 * 2 ^ p + ell3 i.G)
    hSB hb hc hR
  unfold LevelJPrep.outerBoundJ
  refine hg.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
  omega

/-- The carrier terms of `readyBoundJ` at an arbitrary level with output carrier names. -/
theorem ready_carriers_named (i : LI) (p : ℕ)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    ((2 * ProtectedFullBankBridgeScratch.actualRows i.G i.c i.b i.y i.lv i.M + 2) +
      ((2 * ProtectedFullBankBridgeScratch.actualCols i.G i.c i.b i.y i.lv i.M + 2) +
        (ProtectedFullBankBridgeScratch.actualRows i.G i.c i.b i.y i.lv i.M +
         ProtectedFullBankBridgeScratch.actualCols i.G i.c i.b i.y i.lv i.M + 4) + 1) + 1) + 1 ≤
      6 * 2 ^ p + 11 := by
  have hr := (ClockF.actualRows_le i.G i.c i.b i.y i.lv i.M).trans (from_clog hrows)
  have hc := (ClockF.actualCols_le i.G i.c i.b i.y i.lv i.M).trans (from_clog hcols)
  omega

/-- **`prepBoundJ` at an arbitrary named level, up to the installed-bank clear sum.** With
`B := (1+9 ps)((800(|enc G|+1)+2)^C + 2^(C p)) + 13 + Krow (|enc G| + 205·2^(4p) + 1)^9`
(the named bound on `boundJ`), `prepBoundJ ≤ B + Σ_k |C1j (clearCells k)| + nClear·ps3·B
+ nClear + 3 + 6·2^p + 11 + K (3·2^p + 2|enc G| + 7)^2 + 1`, for EVERY master region `mS`. -/
theorem prep_named : ∃ C ps ps3 K : ℕ, ∀ (i : LI) (p : ℕ) (mS : WeightedRawWords.Aux → List Bool),
    SourceNames i p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p →
    LevelJPrep.prepBoundJ i.G i.c i.b i.y i.lv i.M mS ≤
      ((1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
          W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9) +
        ((∑ k : Fin WeightedLevel0Clean.nClear,
            (LevelJRows.C1j i.G i.c i.b i.y i.lv i.M mS (WeightedLevel0Clean.clearCells k)).length) +
          WeightedLevel0Clean.nClear * (ps3 *
            ((1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
              W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9)) +
          WeightedLevel0Clean.nClear + 2) + 1 +
        (6 * 2 ^ p + 11) + K * (3 * 2 ^ p + 2 * ell3 i.G + 7) ^ 2 + 1 := by
  obtain ⟨C, ps, hB⟩ := G5bBoundJNamed.boundJ_named
  obtain ⟨ps3, hsplit⟩ := W12ReadyJ.cleanJ_split
  obtain ⟨K, hK⟩ := outer_named
  refine ⟨C, ps, ps3, K, fun i p mS h hrows hcols => ?_⟩
  have hb := hB i p h hrows hcols
  have ho := hK i p h
  have hcar := ready_carriers_named i p hrows hcols
  unfold LevelJPrep.prepBoundJ
  rw [W12ReadyJ.ready_splitJ, hsplit]
  generalize LevelJClean.boundJ i.G i.c i.b i.y i.lv i.M = x at hb ⊢
  generalize ((1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
      W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9) = B at hb ⊢
  have hm : WeightedLevel0Clean.nClear * (ps3 * x) ≤ WeightedLevel0Clean.nClear * (ps3 * B) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
  omega

/-- The raw parameter word of an arbitrary named level. -/
theorem wordSize_named (i : LI) (p : ℕ) (h : SourceNames i p) :
    ETHParameterScaleMachineInput.wordSize (PL i) ≤ 5 * 2 ^ p + ell3 i.G := by
  have hsc := from_clog h.sourceDescription
  have hco := from_clog h.costDescription
  have hnd : (PL i).nextDepth ≤ 2 ^ p :=
    h.restrictionDepth.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hrx := from_clog h.inputRows
  have hcy := from_clog h.inputCols
  have hE := card_le_ell3 i.G
  have hedges : (PL i).edges = Fintype.card i.E := rfl
  have h1 : (PL i).rows = rxI i := rfl
  have h2 : (PL i).columns = cyI i := rfl
  unfold ETHParameterScaleMachineInput.wordSize
  omega

/-- **`prepBoundJ` at an arbitrary named level, fully bounded** (every master region with a
blank `N` cell, as the physical run's `StepP.mSj (Level0Install.mb1 ..)`; admitted
`W12ReadyJ.mSj_N`). -/
theorem prep_named_full : ∃ C ps ps3 K : ℕ, ∀ (i : LI) (p : ℕ) (mS : WeightedRawWords.Aux → List Bool),
    mS .N = [] → SourceNames i p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p →
    LevelJPrep.prepBoundJ i.G i.c i.b i.y i.lv i.M mS ≤
      (1 + WeightedLevel0Clean.nClear * ps3) *
          ((1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
            W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9) +
        WeightedLevel0Clean.nClear * (5 * 2 ^ p + 2 * ell3 i.G + 1) +
        WeightedLevel0Clean.nClear + 6 * 2 ^ p + 16 + K * (3 * 2 ^ p + 2 * ell3 i.G + 7) ^ 2 := by
  obtain ⟨C, ps, ps3, K, hP⟩ := prep_named
  refine ⟨C, ps, ps3, K, fun i p mS hN h hrows hcols => ?_⟩
  have h1 := hP i p mS h hrows hcols
  have h2 := W12C1j.C1j_sum_le i.G i.c i.b i.y i.lv i.M mS hN
  have h3 := wordSize_named i p h
  have h3' : ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M)
      ≤ 5 * 2 ^ p + ell3 i.G := h3
  have hell : (EncodedGraph.encode (EncodedETHSource.serializeGraph i.G)).length = ell3 i.G := rfl
  rw [hell] at h2
  have h4 : WeightedLevel0Clean.nClear *
      (ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) +
        ell3 i.G + 1) ≤ WeightedLevel0Clean.nClear * (5 * 2 ^ p + 2 * ell3 i.G + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  generalize ((1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
      W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9) = B at h1 ⊢
  have e : (1 + WeightedLevel0Clean.nClear * ps3) * B =
      B + WeightedLevel0Clean.nClear * (ps3 * B) := by ring
  rw [e]
  omega

#print axioms outer_named
#print axioms ready_carriers_named
#print axioms prep_named
#print axioms wordSize_named
#print axioms prep_named_full

end EthInapproximability.CurrentPaper.G5bPrepNamed
