import EthInapproximability.CurrentPaper.ActualWriterClock
import EthInapproximability.CurrentPaper.ClockL

/-!
# Named (arbitrary-p) bounds for the bridge components of one round clock
(private lane owner:b-g5-2, segment 1 support; NOT the materialization theorem)

Source: lock v8 `B-effectivity-details.tex:90-104` (`thm:paper-materialization`), runtime
clause `(n+|enc G|+1)^O(1) + (k+1) 2^O(p)` under the premise that `p` bounds the actual
names, descriptions, widths and restriction depths of every level.

The admitted round clock `StepP.roundBoundP` of one level contains, besides the writer clock
and `prepBoundJ`, the bridge budget `actualPhysicalBudget`, the bridge output length, the
`nB` bridge-start stack sum and the matrix word `mw`. The admitted bounds of these
(`ClockK.level_budget`, `ClockE.level_output`, `ClockL.level_stacks`, `ClockE.level_mw`) are
stated only at the SELECTED levels `j < L(n)` with the multiplicative envelope
`(|packet|+1)^(d+1) T(n)`. Here the same admitted objects are bounded for an ARBITRARY level
record `i : LI` and an ARBITRARY `p` from the named premise `ActualOrderFromCarrier.SourceNames i p`
(the frozen Codex source-name predicate, replayed here) plus the output carrier names
`clog rows(step) ≤ p`, `clog cols(step) ≤ p` (the premises of the frozen
`ActualRoundParts.dims_bound_named`), in the additive form `C (|enc G| + 2)^18 + C 2^(80 p)`.

NOT claimed: any bound on `prepBoundJ` (the only `roundBoundP` component not covered by these
named bounds together with `ActualWriterClock`, `ActualRoundParts`); any total machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5bRoundNamed

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualOrderFromCarrier ProtectedFullBankBridgeScratch

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- The named envelope bound: `preparedEnvelope ≤ |enc G| + 4·2^p + 200·(2^p·2^p)^2`. -/
theorem envelope_named (i : LI) (p : ℕ) (h : SourceNames i p)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    ProtectedBudgetNormalizationScratch.preparedEnvelope i.G i.c i.b i.y i.lv i.M ≤
      ell3 i.G + 4 * 2 ^ p + 200 * ((2 ^ p * 2 ^ p) * (2 ^ p * 2 ^ p)) := by
  have he := ClockJ.envelope_le i.G i.c i.b i.y i.lv i.M
  have hO := ClockE.output_length i.G i.c i.b i.y i.lv i.M
  have hr := from_clog hrows
  have hc := from_clog hcols
  have hscale := from_clog h.scaleDescription
  have hbins := from_clog h.binsDescription
  have hsrc := from_clog h.sourceDescription
  have hd : (PL i).nextDepth ≤ 2 ^ p :=
    h.restrictionDepth.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hV := card_le_ell3 i.G
  have hOle : (actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length ≤ 2 ^ p * 2 ^ p := by
    rw [hO]; exact Nat.mul_le_mul hr hc
  have hOO : (actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length *
      (actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length ≤
        (2 ^ p * 2 ^ p) * (2 ^ p * 2 ^ p) := Nat.mul_le_mul hOle hOle
  have hbins' : Parameters.bins (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) ≤ 2 ^ p := hbins
  have hscale' : Parameters.scale (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) ≤ 2 ^ p :=
    hscale
  have hsrc' : (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M).sourceConstant ≤ 2 ^ p := hsrc
  have hd' : (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M).nextDepth ≤ 2 ^ p := hd
  change _ ≤ Fintype.card i.V + Parameters.scale (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) +
      (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M).nextDepth +
      (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M).sourceConstant +
      Parameters.bins (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) +
      200 * ((actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length *
        (actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length) at he
  omega

/-- `(x + y)^m ≤ 2^m (x^m + y^m)`. -/
theorem pow_add_le (x y m : ℕ) : (x + y) ^ m ≤ 2 ^ m * (x ^ m + y ^ m) := by
  rcases le_total x y with hxy | hxy
  · calc (x + y) ^ m ≤ (2 * y) ^ m := Nat.pow_le_pow_left (by omega) m
      _ = 2 ^ m * y ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (x ^ m + y ^ m) := Nat.mul_le_mul_left _ (by omega)
  · calc (x + y) ^ m ≤ (2 * x) ^ m := Nat.pow_le_pow_left (by omega) m
      _ = 2 ^ m * x ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (x ^ m + y ^ m) := Nat.mul_le_mul_left _ (by omega)

/-- The named envelope in additive form: `≤ ell3 G + 205·2^(4p)`. -/
theorem envelope_named_additive (i : LI) (p : ℕ) (h : SourceNames i p)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    ProtectedBudgetNormalizationScratch.preparedEnvelope i.G i.c i.b i.y i.lv i.M ≤
      ell3 i.G + 205 * 2 ^ (4 * p) := by
  have h1 := envelope_named i p h hrows hcols
  have e : (2 ^ p * 2 ^ p) * (2 ^ p * 2 ^ p) = 2 ^ (4 * p) := by
    rw [← pow_add, ← pow_add]
    ring_nf
  have h2 : 2 ^ p ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [e] at h1
  omega

/-- The admitted bridge budget at an arbitrary named level:
`actualPhysicalBudget ≤ coefficient · 2^18 · ((ell3 G)^18 + 205^18 · 2^(72 p))`. -/
theorem budget_named (i : LI) (p : ℕ) (h : SourceNames i p)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    actualPhysicalBudget i.G i.c i.b i.y i.lv i.M ≤
      ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
        (ell3 i.G ^ 18 + 205 ^ 18 * 2 ^ (72 * p)) := by
  have h1 := ProtectedBudgetNormalizationScratch.actualPhysicalBudget_prepared_polynomial
    i.G i.c i.b i.y i.lv i.M
  have h2 := envelope_named_additive i p h hrows hcols
  have h3 := Nat.pow_le_pow_left h2 18
  have h4 := pow_add_le (ell3 i.G) (205 * 2 ^ (4 * p)) 18
  have e : (205 * 2 ^ (4 * p)) ^ 18 = 205 ^ 18 * 2 ^ (72 * p) := by
    rw [mul_pow, ← pow_mul]; congr 2; ring
  rw [e] at h4
  calc actualPhysicalBudget i.G i.c i.b i.y i.lv i.M
      ≤ ProtectedBudgetNormalizationScratch.coefficient *
          (ProtectedBudgetNormalizationScratch.preparedEnvelope i.G i.c i.b i.y i.lv i.M) ^ 18 := h1
    _ ≤ ProtectedBudgetNormalizationScratch.coefficient *
          (2 ^ 18 * (ell3 i.G ^ 18 + 205 ^ 18 * 2 ^ (72 * p))) :=
        Nat.mul_le_mul_left _ (h3.trans h4)
    _ = _ := by ring

/-- The bridge output word at an arbitrary named level: at most `2^(2p)` bits. -/
theorem output_named (i : LI) (p : ℕ)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    (actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length ≤ 2 ^ (2 * p) := by
  rw [ClockE.output_length, two_mul, pow_add]
  exact Nat.mul_le_mul (from_clog hrows) (from_clog hcols)

/-- The `nB` bridge-start stack summand of `roundBoundP` at an arbitrary named level. -/
theorem stacks_named [Fintype OuterLevel0Bridge.BStack]
    [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (i : LI) (p : ℕ) (h : SourceNames i p)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    (∑ k : Fin Level0CleanRun.nB,
        (((actualPhysicalStart i.G i.c i.b i.y i.lv i.M).stk
              ((Fintype.equivFin OuterLevel0Bridge.BStack).symm k)).length +
          BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
            actualPhysicalBudget i.G i.c i.b i.y i.lv i.M)) ≤
      Level0CleanRun.nB * ((ell3 i.G + 205 * 2 ^ (4 * p)) +
        BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
            (ell3 i.G ^ 18 + 205 ^ 18 * 2 ^ (72 * p)))) := by
  have hE := envelope_named_additive i p h hrows hcols
  have hB := budget_named i p h hrows hcols
  have hterm : ∀ k : Fin Level0CleanRun.nB,
      ((actualPhysicalStart i.G i.c i.b i.y i.lv i.M).stk
            ((Fintype.equivFin OuterLevel0Bridge.BStack).symm k)).length +
          BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
            actualPhysicalBudget i.G i.c i.b i.y i.lv i.M ≤
        (ell3 i.G + 205 * 2 ^ (4 * p)) +
          BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
            (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
              (ell3 i.G ^ 18 + 205 ^ 18 * 2 ^ (72 * p))) := by
    intro k
    have hs := ClockL.start_cell_le i.G i.c i.b i.y i.lv i.M
      ((Fintype.equivFin OuterLevel0Bridge.BStack).symm k)
    exact Nat.add_le_add (hs.trans hE) (Nat.mul_le_mul_left _ hB)
  calc _ ≤ ∑ _k : Fin Level0CleanRun.nB, ((ell3 i.G + 205 * 2 ^ (4 * p)) +
          BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
            (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
              (ell3 i.G ^ 18 + 205 ^ 18 * 2 ^ (72 * p)))) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = _ := by simp

#print axioms envelope_named
#print axioms envelope_named_additive
#print axioms budget_named
#print axioms output_named
#print axioms stacks_named

end EthInapproximability.CurrentPaper.G5bRoundNamed
