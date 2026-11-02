import EthInapproximability.CurrentPaper.G5bRoundNamed
import EthInapproximability.CurrentPaper.W12ReadyJ

/-!
# Named (arbitrary-p) bound for the level-row clock `LevelJClean.boundJ`
(private lane owner:b-g5-2, segment 1 support; NOT the materialization theorem)

The admitted `W12BoundJ.boundJ_level` bounds the level-row clock (the core of `cleanBoundJ`,
hence of `readyBoundJ` and `prepBoundJ`) only at the selected levels `j < L(n)` through the
coarse envelope `U`. Here the SAME admitted clock is bounded at an ARBITRARY level record
from the named premise `SourceNames i p` and the output carrier names:

* the `publicBound15` part through the ADMITTED actual-count polynomial
  `ActualCountFamilyClock.hP15 : PolyIn A (...)` and the admitted
  `ActualSourceNames.actual_counts_source_bound : A i ≤ 800·2^p·(|enc G|+1)`;
* the `rowTime` part through the admitted `W12RowTime.rowTime_level` and
  `G5bRoundNamed.envelope_named_additive`.

NOT claimed: bounds on the installed-bank clear sum `Σ C1j` inside `cleanBoundJ`, on
`outerBoundJ`, or on the level-0 analogues; any total machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5bBoundJNamed

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualOrderFromCarrier W12BoundJ

set_option maxHeartbeats 3000000

/-- `pbJ` is polynomial in the ACTUAL level counts `A` (admitted `ActualCountFamilyClock.hP15`). -/
theorem pbJ_poly_actual : PolyIn ActualCountClock.A pbJ := by
  refine PolyIn.mono (fun i => le_of_eq ?_) ActualCountFamilyClock.hP15
  unfold pbJ
  rw [dI_binBase, dI_rawWidth, dI_s, noW_eq']
  rfl

/-- `SourceNames` forces `p ≥ 1` (the scale is at least `2^24`). -/
theorem one_le_p (i : LI) (p : ℕ) (h : SourceNames i p) : 1 ≤ p := by
  have h1 := h.scaleDescription
  have h24 : 2 ^ 24 ≤ Parameters.scale (PL i) := le_max_left _ _
  have h2 : Nat.clog 2 (2 ^ 24) ≤ Nat.clog 2 (Parameters.scale (PL i)) := Nat.clog_mono_right _ h24
  rw [Nat.clog_pow 2 24 (by decide)] at h2
  omega

/-- The `publicBound15` part at an arbitrary named level, additive form. -/
theorem pbJ_named : ∃ C : ℕ, ∀ (i : LI) (p : ℕ), SourceNames i p →
    pbJ i ≤ (800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := pbJ_poly_actual
  refine ⟨K + 2 * 2 * D, fun i p h => ?_⟩
  have hA := ActualSourceNames.actual_counts_source_bound i p h.toNames
  have hp := one_le_p i p h
  set X := 800 * (ell3 i.G + 1) + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hA' : ActualCountClock.A i ≤ 2 ^ (1 * p) * X ^ 1 := by
    rw [one_mul, pow_one]
    calc ActualCountClock.A i ≤ 800 * 2 ^ p * (ell3 i.G + 1) := hA
      _ = 2 ^ p * (800 * (ell3 i.G + 1)) := by ring
      _ ≤ 2 ^ p * X := Nat.mul_le_mul_left _ (by omega)
  have hab := EntryClockPoly.absorb K D 1 1 X p (ActualCountClock.A i) hX2 hp hA'
  have e : (K + 2 * (1 + 1) * D) * p = (K + 2 * 2 * D) * p := by ring
  rw [e] at hab
  have hmono : X ^ (K + 2 * 1 * D) ≤ X ^ (K + 2 * 2 * D) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact (hKD i).trans (hab.trans (Nat.add_le_add_right hmono _))

/-- **The level-row clock `boundJ` at an arbitrary named level**, additive in `2^p`. -/
theorem boundJ_named : ∃ C ps : ℕ, ∀ (i : LI) (p : ℕ), SourceNames i p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).rows ≤ p →
    Nat.clog 2 (Iteration.step i.G i.c i.b i.y i.lv i.M).columns ≤ p →
    LevelJClean.boundJ i.G i.c i.b i.y i.lv i.M ≤
      (1 + 9 * ps) * ((800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell3 i.G + 205 * 2 ^ (4 * p) + 1) ^ 9 := by
  obtain ⟨C, hC⟩ := pbJ_named
  obtain ⟨ps, hps⟩ := boundJ_split
  refine ⟨C, ps, fun i p h hrows hcols => ?_⟩
  rw [hps]
  have hpb := hC i p h
  have hrt := W12RowTime.rowTime_level i.G i.c i.b i.y i.lv i.M
  have hen := G5bRoundNamed.envelope_named_additive i p h hrows hcols
  have hrt' := hrt.trans (Nat.mul_le_mul_left W12RowTime.Krow
    (Nat.pow_le_pow_left (Nat.add_le_add_right hen 1) 9))
  have hpb' : pbJ ⟨i.V, i.E, i.G, i.c, i.b, i.y, i.lv, i.M⟩ ≤
      (800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p) := hpb
  generalize (pbJ ⟨i.V, i.E, i.G, i.c, i.b, i.y, i.lv, i.M⟩) = x at hpb' ⊢
  generalize (800 * (ell3 i.G + 1) + 2) ^ C + 2 ^ (C * p) = B at hpb' ⊢
  have h9 : 9 * (ps * x) ≤ 9 * (ps * B) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left ps hpb')
  have e : (1 + 9 * ps) * B = B + 9 * (ps * B) := by ring
  rw [e]
  omega

#print axioms pbJ_poly_actual
#print axioms one_le_p
#print axioms pbJ_named
#print axioms boundJ_named

end EthInapproximability.CurrentPaper.G5bBoundJNamed
