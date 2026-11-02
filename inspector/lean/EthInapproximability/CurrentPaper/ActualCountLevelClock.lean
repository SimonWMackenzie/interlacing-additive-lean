import EthInapproximability.CurrentPaper.ActualCountFamilyClock

/-! Literal machine-clock polynomials rebased from the coarse scale envelope
to the actual level counts. See `ActualCountFamilyClock` for provenance. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualCountClock

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 EntryClockPoly4 ActualCountFamilyClock
open EntryPrepFamily EntryPrepFamilyJ

set_option maxHeartbeats 3000000

theorem hFamJ : PolyIn A (fun i => famBound_j i.G i.c i.b i.y i.lv i.M) :=
  PolyIn.mono (fun i => le_of_eq (famBound_j_eq i)) ActualCountFamilyClock.famClock_poly

theorem hGrowJ : PolyIn A (fun i => growB_j i.G i.c i.b i.y i.lv i.M) := by
  unfold growB_j
  refine PolyIn.mul (PolyIn.const _) ?_
  exact PolyIn.mono (fun i => le_of_eq (pb15_eqJ i)) ActualCountFamilyClock.hP15

theorem pEncJ : PolyIn A (fun i => (EncodedGraph.encode (gP i.G)).length) :=
  PolyIn.mono (fun i => le_of_eq (show (EncodedGraph.encode (gP i.G)).length = ell3 i.G from rfl)) ActualCountFamilyClock.pEll
theorem pBJ : PolyIn A (fun i => i.b) :=
  PolyIn.mono (fun i => le_of_eq (show i.b = (PL i).nextDepth from rfl)) ActualCountFamilyClock.pND
theorem pYJ : PolyIn A (fun i => i.y + i.lv) :=
  PolyIn.mono (fun i => le_of_eq (show i.y + i.lv = (PL i).cost from rfl)) ActualCountFamilyClock.pCost
theorem pCJ : PolyIn A (fun i => i.c) :=
  PolyIn.mono (fun i => le_of_eq (show i.c = (PL i).sourceConstant from rfl)) ActualCountFamilyClock.pSC
theorem pEJ : PolyIn A (fun i => Fintype.card i.E) :=
  PolyIn.mono (fun i => le_of_eq (show Fintype.card i.E = eI i from rfl)) ActualCountFamilyClock.pE

theorem hSfJ : PolyIn A sfBJ := by
  unfold sfBJ
  have := ActualCountFamilyClock.pCy
  have := ActualCountFamilyClock.pRx
  have := pEncJ
  have := pBJ
  have := pYJ
  have := pEJ
  have := pCJ
  prActual

theorem hExB_actual : PolyIn A (fun i => exB (aI i) (qI i) (tI i) (rxI i)) := by
  unfold exB
  atomsActual
  prActual

theorem hClearJ : PolyIn A (fun i => clearB_j i.G i.c i.b i.y i.lv i.M) := by
  have h1 : PolyIn A exB0J := PolyIn.mono (fun i => le_of_eq (exB0J_eq i)) hExB_actual
  have h2 : PolyIn A (fun i => sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i) :=
    PolyIn.add (PolyIn.add hSfJ hGrowJ) h1
  have h3 : PolyIn A (fun i => nF * (sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i)) :=
    PolyIn.mul (PolyIn.const _) h2
  exact PolyIn.mono (fun i => clearB_leJ i) h3

theorem hAJ : PolyIn A (fun i => costA i.G) := by
  unfold costA
  have := pEncJ
  prActual

theorem hCJ : PolyIn A (fun i => costC_j i.G i.c i.b i.y i.lv i.M) := by
  unfold costC_j
  have hrx' : PolyIn A (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).rx) :=
    PolyIn.mono (fun i => le_of_eq (wJ_fields i).1) ActualCountFamilyClock.pRx
  have hcy' : PolyIn A (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).cy) :=
    PolyIn.mono (fun i => le_of_eq (wJ_fields i).2.1) ActualCountFamilyClock.pCy
  have := pBJ
  have := pYJ
  have := pEJ
  have := pCJ
  prActual

theorem hEJ : PolyIn A (fun i => costE_j i.G i.c i.b i.y i.lv i.M) := by
  refine PolyIn.mono (fun i => le_of_eq (costE_j_eq i)) ?_
  have := ActualCountFamilyClock.pL
  have := ActualCountFamilyClock.pQ
  have := ActualCountFamilyClock.pQOne
  have := ActualCountFamilyClock.pRx
  prActual

theorem hSJ : PolyIn A (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).s) :=
  PolyIn.mono (fun i => le_of_eq (wJ_fields i).2.2.1) ActualCountFamilyClock.pS

/-- The level-j family clock is polynomial in the level size, over ALL levels. -/
theorem TFJ_poly : PolyIn A (fun i => TFJ i.G i.c i.b i.y i.lv i.M) := by
  have := hFamJ
  have := hClearJ
  have := hAJ
  have := hCJ
  have := hEJ
  have := hSJ
  unfold TFJ
  prActual

/-- Pure clock conversion for a bound on *actual counted quantities*. The
premise about `A` is deliberately exposed, not asserted as a consequence of
the manuscript's source classes here. -/
theorem TFJ_le_of_actual_counts : ∃ C : ℕ, ∀ (i : LI) (n p : ℕ),
    1 ≤ p → A i ≤ 2 ^ p * (n + ell3 i.G + 2) →
    TFJ i.G i.c i.b i.y i.lv i.M ≤
      (n + ell3 i.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := TFJ_poly
  let C := max (K + 2 * D) (K + 4 * D)
  refine ⟨C, fun i n p hp hA => ?_⟩
  let X := n + ell3 i.G + 2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have hab := EntryClockPoly.absorb K D 1 1 X p (A i) hX hp (by
    simpa only [one_mul, pow_one] using hA)
  have hC1 : K + 2 * D ≤ C := le_max_left _ _
  have hC2 : K + 4 * D ≤ C := le_max_right _ _
  calc
    TFJ i.G i.c i.b i.y i.lv i.M ≤ K * (A i + 1) ^ D := hKD i
    _ ≤ X ^ (K + 2 * D) + 2 ^ ((K + 4 * D) * p) := by
      simpa only [show 2 * 1 * D = 2 * D by omega,
        show 2 * (1 + 1) * D = 4 * D by omega] using hab
    _ ≤ X ^ C + 2 ^ (C * p) :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) hC1)
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right p hC2))


#print axioms hFamJ
#print axioms hClearJ
#print axioms TFJ_poly
#print axioms TFJ_le_of_actual_counts

end EthInapproximability.CurrentPaper.ActualCountClock
