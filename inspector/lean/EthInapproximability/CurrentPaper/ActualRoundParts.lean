import EthInapproximability.CurrentPaper.ActualOrderFromCarrier
import EthInapproximability.CurrentPaper.DimsClock1Level

/-! Source-clock bounds for two concrete round components. These do not yet
assemble a complete round or assert a runtime premise. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualRoundParts

open EntryClockPoly3 ActualOrderFromCarrier
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

set_option maxHeartbeats 3000000

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- The actual cost-update machine is polynomial in the level's named
parameters, source graph encoding, and its source numerical depth. -/
theorem cost_bound_named (i : LI) (p : ℕ) (h : SourceNames i p) :
    CostUpdateMachine.costBound (Parameters.scale (PL i))
      (PL i).nextDepth (PL i).sourceConstant (sI i)
      (Fintype.card i.E) (PL i).cost ≤
        (2000000 * ClockD.Kc + 1000000) *
          (5 * 2 ^ p + ell3 i.G + 1) ^ 6 := by
  have hscale := from_clog h.scaleDescription
  have hs := from_clog h.binsDescription
  have hc := from_clog h.sourceDescription
  have hy := from_clog h.costDescription
  have hd : (PL i).nextDepth ≤ 2 ^ p :=
    h.restrictionDepth.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have he := card_le_ell3 i.G
  refine (ClockD.costBound_le _ _ _ _ _ _).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6))
  omega

/-- The actual next-dimension machine is quadratic in the *output* matrix
dimensions, so its source clock follows from the output carrier names. -/
theorem dims_bound_named (i : LI) (p : ℕ) (hc : 1 ≤ i.c)
    (hrows : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p)
    (hcols : Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p) :
    NextDimsMachineTN.dimsBound
      (NextDimsEmbedTN.dimsIn (PL i) (Fintype.card i.V)
        (sI i * EffectiveIteration.familySize (PL i))) ≤
        DimsClock1.Kd * (2 * 2 ^ p + 1) ^ 2 := by
  have h := DimsClock1.dims_step i.G i.c i.b i.y i.lv i.M hc
  have hr := from_clog hrows
  have hcol := from_clog hcols
  have hsum : (Iteration.step i.G i.c i.b i.y i.lv i.M).rows +
      (Iteration.step i.G i.c i.b i.y i.lv i.M).columns + 1 ≤ 2 * 2 ^ p + 1 := by
    omega
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2))

/-- The six-word state-installation clock, charged by the actual name lengths
of its next state and the numeric source restriction depth. In particular no
name for an unconstructed *following* level is required at the final install. -/
theorem install_bound_named {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (c b j p : ℕ)
    (hc : Nat.clog 2 c ≤ p) (hb : b ≤ p)
    (hy : Nat.clog 2
      ((PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).budget +
        (j + 1)) ≤ p)
    (hr : Nat.clog 2
      (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.rows ≤ p)
    (hcol : Nat.clog 2
      (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.columns ≤ p) :
    StepP.installBoundP G c b j ≤ 12 * 2 ^ p + 4 * ell3 G + 30 := by
  have hc' := from_clog hc
  have hb' : b ≤ 2 ^ p := hb.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hy' := from_clog hy
  have hr' := from_clog hr
  have hcol' := from_clog hcol
  rw [ClockB.installBoundP_eq]
  change 2 * c + 2 * b +
      2 * ((PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).budget + (j + 1)) +
      2 * Fintype.card E +
      3 * (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.rows +
      3 * (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.columns +
      2 * ell3 G + 30 ≤ _
  have he := card_le_ell3 G
  omega

#print axioms cost_bound_named
#print axioms dims_bound_named
#print axioms install_bound_named

end EthInapproximability.CurrentPaper.ActualRoundParts
