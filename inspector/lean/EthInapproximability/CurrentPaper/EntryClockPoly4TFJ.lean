import EthInapproximability.CurrentPaper.EntryClockPoly3TF
import EthInapproximability.CurrentPaper.EntryPrepFamilyRunJ

/-!
# Lane owner:b-entry-clock-4, segment 1: the level-j family clock `TFJ` is polynomial

`TFJ G c bJ yb lv Mx` (lane entry-levelj-2's `FJLvl`, restaged import-only as `EC4FJLvl`) is the
clock of the `Family4SpecJ` instance `EntryPrepFamilyJ.family4_j` for owner-8's fixed program
`progF` at an ARBITRARY level state. It is the level-j twin of `TF`: every summand is majorized
over the level-generic index `LI` of `EC3Core` (a level IS an `LI`, no level-0 map is needed):

* `famBound_j` IS `famClock` at the level (`famBound_j_eq`), so `famClock_poly` applies;
* `growB_j` is a fixed multiple of the level's `publicBound15` (`pb15`, `hPb15`);
* the copies are charged by the physical lengths of the copied words (graph bytes, `c`, `|E|`,
  `rx`, `cy`, `yb + lv`, `bJ`, the two family tables, `qOne`, `s`);
* the 321-cell clear is bounded cell by cell: level cells by the admitted start bank (`SF_eqJ`)
  plus `growB_j`, assembly cells by their exact exit words (`EC3TF.exitBank_len`).

Result (`TFJ_le`): ONE absolute `C` with `TFJ G c bJ yb lv Mx ≤ (|enc G| + 1)^C + 2^(C p)` whenever
`oneLevelBound (stepParameters G c bJ yb lv Mx) ≤ p`.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly4

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 EntryPrepFamily EntryPrepFamilyJ

/-! ## The level-j family clock is `famClock` at the level -/

theorem dPj_binBase (i : LI) : (dP_j i.G i.c i.b i.y i.lv i.M).binBase =
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) := rfl
theorem dPj_rawWidth (i : LI) : (dP_j i.G i.c i.b i.y i.lv i.M).rawWidth =
    MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i) := rfl
theorem dPj_s (i : LI) : (dP_j i.G i.c i.b i.y i.lv i.M).s = sI i := rfl

/-- `famBound_j` (the admitted level-wired family clock at the level) IS `famClock` at the level. -/
theorem famBound_j_eq (i : LI) : famBound_j i.G i.c i.b i.y i.lv i.M = famClock i := by
  unfold famBound_j famClock
  rw [dPj_binBase, dPj_rawWidth, dPj_s, noW_eq]

theorem wJ_fields (i : LI) :
    (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).rx = rxI i ∧
    (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).cy = cyI i ∧
    (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).s = sI i ∧
    (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).qOne = Construction.qOne (aI i) := by
  unfold EntryLevelJBank.wJ EntryLevelWords.levelWords
  rw [TemplateEntry.actualWords.eq_def]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Start bank, exit bank and clear -/

/-- The level-j start-bank majorant (admitted start bank, `SF_eqJ`). -/
noncomputable def sfBJ (i : LI) : ℕ :=
  (EncodedGraph.encode (gP i.G)).length + 1 + i.b + (i.y + i.lv) + cyI i + rxI i +
    Fintype.card i.E + i.c

theorem SF_lenJ (i : LI) (x : EntryFamilyLevel.Stack) :
    (SFJ i.G i.c i.b i.y i.lv i.M x).length ≤ sfBJ i := by
  rw [SF_eqJ]
  unfold sfBJ
  have e1 := (wJ_fields i).2.1
  have e2 := (wJ_fields i).1
  simp only [Function.update_apply]
  split_ifs <;> simp only [List.length_cons, List.length_replicate, EntryLayout.rep,
    List.length_nil, e1, e2] <;> omega

theorem initial_lenJ (i : LI) (j : WeightedLevelColumnSave.Stack) :
    (WeightedLevelColumnSave.initialBank (iP_j i.G i.c i.b i.y i.lv i.M) (gP i.G)
      WeightedRawWords.noW j).length ≤ sfBJ i :=
  SF_lenJ i (Sum.inl j)

/-- The assembly exit-cell majorant at the level-j arguments of `exA_j`. -/
noncomputable def exB0J (i : LI) : ℕ :=
  exB (aP_j i.G i.c i.b i.y i.lv i.M) (qP_j i.G i.c i.b i.y i.lv i.M)
    (tP_j i.G i.c i.b i.y i.lv i.M) (iP_j i.G i.c i.b i.y i.lv i.M).rows

theorem exA_lenJ (i : LI) (x : EntryFamilyAssembly.ACell) :
    (exA_j i.G i.c i.b i.y i.lv i.M x).length ≤ exB0J i := by
  unfold exA_j exB0J
  exact exitBank_len _ _ _ _ _ x

theorem exB0J_eq (i : LI) : exB0J i = exB (aI i) (qI i) (tI i) (rxI i) := rfl

/-- Every level-j allowance `bnd_j` is below the common majorant (split through the rewrites
`bnd_inl_j` / `bnd_inr_j`, as at level 0). -/
theorem bnd_leJ (i : LI) (y : EntryFamilyLevel.Stack) :
    bnd_j i.G i.c i.b i.y i.lv i.M y ≤ sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i := by
  rcases y with j | x
  · rw [bnd_inl_j]
    exact Nat.le_add_right_of_le (Nat.add_le_add_right (initial_lenJ i j) _)
  · rw [bnd_inr_j]
    exact le_trans (exA_lenJ i x) (Nat.le_add_left _ _)

theorem lenF_leJ (i : LI) (x : FamIdx) :
    lenF_j i.G i.c i.b i.y i.lv i.M x ≤ sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i := by
  unfold lenF_j
  split
  · exact bnd_leJ i _
  · exact Nat.zero_le _

theorem clearB_leJ (i : LI) :
    clearB_j i.G i.c i.b i.y i.lv i.M ≤
      nF * (sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i) := by
  unfold clearB_j
  calc (∑ k : Fin nF, lenF_j i.G i.c i.b i.y i.lv i.M ((Fintype.equivFin FamIdx).symm k))
      ≤ ∑ _k : Fin nF, (sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i) :=
        Finset.sum_le_sum (fun k _ => lenF_leJ i _)
    _ = nF * (sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The polynomial clock of `progF` at level j -/

theorem costE_j_eq (i : LI) : costE_j i.G i.c i.b i.y i.lv i.M =
    (2 * (LI' i * qI i * Construction.qOne (aI i)) + 2) +
      ((2 * (LI' i * qI i * rxI i) + 2) +
        ((2 * Construction.qOne (aI i) + 2) + ((2 * Construction.qOne (aI i) + 2) + 0))) := by
  unfold costE_j
  rw [wJ_first, wJ_row, MatrixStage4FamilyData.fieldTable_length,
    MatrixStage4FamilyData.fieldTable_length, (wJ_fields i).2.2.2]
  rfl

theorem pb15_eqJ (i : LI) :
    WeightedLevelFields15.publicBound15 (iP_j i.G i.c i.b i.y i.lv i.M) (gP i.G) (Fintype.card i.E)
      WeightedRawWords.noW (aP_j i.G i.c i.b i.y i.lv i.M) (sP_j i.G i.c i.b i.y i.lv i.M)
      (qP_j i.G i.c i.b i.y i.lv i.M) (LPJ i.G i.c i.b i.y i.lv i.M)
      (dP_j i.G i.c i.b i.y i.lv i.M).binBase (dP_j i.G i.c i.b i.y i.lv i.M).rawWidth
      (dP_j i.G i.c i.b i.y i.lv i.M).s = pb15 i := by
  unfold pb15
  rw [dPj_binBase, dPj_rawWidth, dPj_s, noW_eq]

theorem hFamJ : PolyIn U (fun i => famBound_j i.G i.c i.b i.y i.lv i.M) :=
  PolyIn.mono (fun i => le_of_eq (famBound_j_eq i)) famClock_poly

theorem hGrowJ : PolyIn U (fun i => growB_j i.G i.c i.b i.y i.lv i.M) := by
  unfold growB_j
  refine PolyIn.mul (PolyIn.const _) ?_
  exact PolyIn.mono (fun i => le_of_eq (pb15_eqJ i)) hPb15

theorem pEncJ : PolyIn U (fun i => (EncodedGraph.encode (gP i.G)).length) :=
  PolyIn.mono (fun i => le_of_eq (show (EncodedGraph.encode (gP i.G)).length = ell3 i.G from rfl)) pEll
theorem pBJ : PolyIn U (fun i => i.b) :=
  PolyIn.mono (fun i => le_of_eq (show i.b = (PL i).nextDepth from rfl)) pND
theorem pYJ : PolyIn U (fun i => i.y + i.lv) :=
  PolyIn.mono (fun i => le_of_eq (show i.y + i.lv = (PL i).cost from rfl)) pCost
theorem pCJ : PolyIn U (fun i => i.c) :=
  PolyIn.mono (fun i => le_of_eq (show i.c = (PL i).sourceConstant from rfl)) pSC
theorem pEJ : PolyIn U (fun i => Fintype.card i.E) :=
  PolyIn.mono (fun i => le_of_eq (show Fintype.card i.E = eI i from rfl)) pE

theorem hSfJ : PolyIn U sfBJ := by
  unfold sfBJ
  have := pCy
  have := pRx
  have := pEncJ
  have := pBJ
  have := pYJ
  have := pEJ
  have := pCJ
  pr

theorem hClearJ : PolyIn U (fun i => clearB_j i.G i.c i.b i.y i.lv i.M) := by
  have h1 : PolyIn U exB0J := PolyIn.mono (fun i => le_of_eq (exB0J_eq i)) hExB
  have h2 : PolyIn U (fun i => sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i) :=
    PolyIn.add (PolyIn.add hSfJ hGrowJ) h1
  have h3 : PolyIn U (fun i => nF * (sfBJ i + growB_j i.G i.c i.b i.y i.lv i.M + exB0J i)) :=
    PolyIn.mul (PolyIn.const _) h2
  exact PolyIn.mono (fun i => clearB_leJ i) h3

theorem hAJ : PolyIn U (fun i => costA i.G) := by
  unfold costA
  have := pEncJ
  pr

theorem hCJ : PolyIn U (fun i => costC_j i.G i.c i.b i.y i.lv i.M) := by
  unfold costC_j
  have hrx' : PolyIn U (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).rx) :=
    PolyIn.mono (fun i => le_of_eq (wJ_fields i).1) pRx
  have hcy' : PolyIn U (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).cy) :=
    PolyIn.mono (fun i => le_of_eq (wJ_fields i).2.1) pCy
  have := pBJ
  have := pYJ
  have := pEJ
  have := pCJ
  pr

theorem hEJ : PolyIn U (fun i => costE_j i.G i.c i.b i.y i.lv i.M) := by
  refine PolyIn.mono (fun i => le_of_eq (costE_j_eq i)) ?_
  have := pL
  have := pQ
  have := pQOne
  have := pRx
  pr

theorem hSJ : PolyIn U (fun i => (EntryLevelJBank.wJ i.G i.c i.b i.y i.lv i.M).s) :=
  PolyIn.mono (fun i => le_of_eq (wJ_fields i).2.2.1) pS

/-- The level-j family clock is polynomial in the level size, over ALL levels. -/
theorem TFJ_poly : PolyIn U (fun i => TFJ i.G i.c i.b i.y i.lv i.M) := by
  have := hFamJ
  have := hClearJ
  have := hAJ
  have := hCJ
  have := hEJ
  have := hSJ
  unfold TFJ
  pr

/-- The naming premise bounds the level size: `U ≤ 2^p * (|enc G| + 1)`. -/
theorem U_leJ (i : LI) (p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M) ≤ p) :
    U i ≤ 2 ^ (1 * p) * (ell3 i.G + 1) ^ 1 := by
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  unfold U
  rw [one_mul, pow_one]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hname) le_rfl

/-- **Segment 1.** The level-j family clock `TFJ` of owner-8's `progF` is polynomial: ONE absolute
constant `C` for all graphs and all level states under the naming premise. -/
theorem TFJ_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c bJ yb lv : ℕ) (Mx : Iteration.Matrix) (p : ℕ),
    EffectiveIteration.oneLevelBound (Iteration.stepParameters G c bJ yb lv Mx) ≤ p →
    TFJ G c bJ yb lv Mx ≤ (EntryClockPoly.ellG G + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := TFJ_poly
  refine ⟨K + 2 * 2 * D, fun {V E} _ _ _ _ G c bJ yb lv Mx p hname => ?_⟩
  let i : LI := ⟨V, E, G, c, bJ, yb, lv, Mx⟩
  have h1 := hKD i
  have hU := U_leJ i p hname
  have hell := card_le_ell3 G
  have hp : 1 ≤ p := by
    have h128 := (EffectiveIteration.parameter_size_bounds (Iteration.stepParameters G c bJ yb lv Mx)).1
    rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
    have : 1 ≤ Parameters.balanceOrder (Iteration.stepParameters G c bJ yb lv Mx) ^ 4 :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have hab := EntryClockPoly.absorb K D 1 1 (ell3 G + 1) p (U i) (by omega) hp hU
  have e : (K + 2 * (1 + 1) * D) * p = (K + 2 * 2 * D) * p := by ring
  have e' : K + 2 * 1 * D ≤ K + 2 * 2 * D := by omega
  have hX1 : 1 ≤ ell3 G + 1 := by omega
  have hmono : (ell3 G + 1) ^ (K + 2 * 1 * D) ≤ (ell3 G + 1) ^ (K + 2 * 2 * D) :=
    Nat.pow_le_pow_right hX1 e'
  rw [e] at hab
  have hE : EntryClockPoly.ellG G = ell3 G := rfl
  rw [hE]
  exact h1.trans (hab.trans (Nat.add_le_add_right hmono _))

/-- The same bound in the `(n + |enc G| + 1)` form. -/
theorem TFJ_le_n : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c bJ yb lv : ℕ) (Mx : Iteration.Matrix) (p : ℕ),
    EffectiveIteration.oneLevelBound (Iteration.stepParameters G c bJ yb lv Mx) ≤ p →
    TFJ G c bJ yb lv Mx ≤ (n + EntryClockPoly.ellG G + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨C, hC⟩ := TFJ_le
  exact ⟨C, fun {V E} _ _ _ _ G n c bJ yb lv Mx p hname =>
    (hC G c bJ yb lv Mx p hname).trans
      (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) _) _)⟩

#print axioms famBound_j_eq
#print axioms SF_lenJ
#print axioms clearB_leJ
#print axioms costE_j_eq
#print axioms TFJ_poly
#print axioms TFJ_le
#print axioms TFJ_le_n

end EthInapproximability.CurrentPaper.EntryClockPoly4
