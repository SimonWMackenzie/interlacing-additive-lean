import EthInapproximability.CurrentPaper.EntryClockPoly3Clock
import EthInapproximability.CurrentPaper.EntryPrepFamilyFinal
import EthInapproximability.CurrentPaper.EntryClockPolyFinal

/-!
# Lane owner:b-entry-clock-3, segment 1: the clock `TF` of owner-8's `progF` is polynomial

`TF G n c` (owner-8 `F8Lvl`, staged as `EntryPrepFamilyLvl`) is the clock of the `Family4Spec`
instance `EntryPrepFamily.family4`. Every summand is majorized: the admitted level-family clock
`famBound` IS `famClock` at the level-0 level (`EC3Clock.famClock_poly`); the level-bank growth
allowance `growB` is a fixed multiple of the admitted `publicBound15`; the copies are charged by
the physical lengths of the words they copy (the graph bytes, the six raw words, the two family
tables and `qOne`); the 321-cell clear is bounded cell by cell (level cells by the admitted
start bank `SF_eq` plus `growB`, assembly cells by their exact exit words).

Result (`TF_le`): ONE absolute constant `C` with
`TF G n c ≤ (n + |enc G| + 1)^C + 2^(C p)` whenever `oneLevelBound (P0 G n c) ≤ p`.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryPrepFamily EntryTailClear

/-! ## Exit-bank lengths of the admitted family assembly -/

/-- A common majorant of every exit cell of `EntryFamilyAssembly.exitBank`. -/
noncomputable def exB (a q t rx : ℕ) : ℕ :=
  PrimeSampler.prime q t (Construction.qOne a * rx) + t + q + rx + Construction.qOne a +
    Construction.qOne a * rx +
    PrimeSampler.size q t (Construction.qOne a * rx) * q * Construction.qOne a +
    PrimeSampler.size q t (Construction.qOne a * rx) * q * rx + a +
    PrimeSampler.size q t (Construction.qOne a * rx)

theorem exitBank_len (a q t rx : ℕ) (hm : 0 < Construction.qOne a * rx)
    (x : EntryFamilyAssembly.ACell) :
    (EntryFamilyAssembly.exitBank a q t rx hm x).length ≤ exB a q t rx := by
  unfold EntryFamilyAssembly.exitBank EntryFamilyAssembly.full exB
  rcases x with c | k | xx
  · cases c <;> simp only [Sum.elim_inl, FamilyRowBody.rowBank, List.length_replicate,
      MatrixStage4FamilyData.fieldTable_length, List.length_nil] <;> omega
  · simp only [Sum.elim_inr, Sum.elim_inl, List.length_nil]; omega
  · cases xx <;> simp only [Sum.elim_inr, EntryFamilyAssembly.xBank, List.length_replicate,
      List.length_nil] <;> omega

theorem hExB : PolyIn U (fun i => exB (aI i) (qI i) (tI i) (rxI i)) := by
  unfold exB
  atoms
  pr

/-! ## Level-0 levels -/

/-- A graph with the entry parameters `n c`. -/
structure L0 where
  V : Type
  E : Type
  [iV : Fintype V]
  [dV : DecidableEq V]
  [iE : Fintype E]
  [dE : DecidableEq E]
  G : EndpointGraph V E
  n : ℕ
  c : ℕ

attribute [instance] L0.iV L0.dV L0.iE L0.dE

/-- The level-0 level of `(G, n, c)`: exactly the arguments of `EntryTailClear`/`iP`. -/
def φ (k : L0) : LI := ⟨k.V, k.E, k.G, k.c, b0 k.n, y0 k.n, 0, M0 k.n⟩

def U0 (k : L0) : ℕ := U (φ k)

theorem comap0 {f : LI → ℕ} (h : PolyIn U f) : PolyIn U0 (fun k => f (φ k)) :=
  PolyIn.comap φ (fun _ => le_refl _) h

theorem dP_binBase (k : L0) : (dP k.G k.n k.c).binBase =
    MatrixStage4Digits.binBase (aI (φ k)) (sI (φ k)) (qI (φ k)) (cyI (φ k)) := rfl
theorem dP_rawWidth (k : L0) : (dP k.G k.n k.c).rawWidth =
    MatrixStage4Codes.cols (aI (φ k)) (sI (φ k)) (qI (φ k)) (cyI (φ k)) := rfl
theorem dP_s (k : L0) : (dP k.G k.n k.c).s = sI (φ k) := rfl
theorem noW_eq : WeightedRawWords.noW = noW3 := rfl

/-- `famBound` (owner-8) IS the level-generic `famClock` at the level-0 level. -/
theorem famBound_eq (k : L0) : famBound k.G k.n k.c = famClock (φ k) := by
  unfold famBound famClock
  rw [dP_binBase, dP_rawWidth, dP_s, noW_eq]
  dsimp only [φ]

theorem w0_fields (k : L0) :
    (EntryLevelWords.w0 k.G k.n k.c).rx = rxI (φ k) ∧ (EntryLevelWords.w0 k.G k.n k.c).cy = cyI (φ k) ∧
    (EntryLevelWords.w0 k.G k.n k.c).s = sI (φ k) ∧
    (EntryLevelWords.w0 k.G k.n k.c).qOne = Construction.qOne (aI (φ k)) := by
  unfold EntryLevelWords.w0 EntryLevelWords.levelWords
  rw [TemplateEntry.actualWords.eq_def]
  dsimp only [φ]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The start-bank majorant (admitted start bank, `SF_eq`). -/
noncomputable def sfB (k : L0) : ℕ :=
  (EncodedGraph.encode (gP k.G)).length + 1 + b0 k.n + y0 k.n + cyI (φ k) + rxI (φ k) + Fintype.card k.E + k.c

theorem SF_len (k : L0) (x : EntryFamilyLevel.Stack) : (SF k.G k.n k.c x).length ≤ sfB k := by
  rw [SF_eq]
  unfold sfB
  have e1 := (w0_fields k).2.1
  have e2 := (w0_fields k).1
  simp only [Function.update_apply]
  split_ifs <;> simp only [List.length_cons, List.length_replicate, EntryLayout.rep,
    List.length_nil, e1, e2] <;> omega

theorem initial_len (k : L0) (j : WeightedLevelColumnSave.Stack) :
    (WeightedLevelColumnSave.initialBank (iP k.G k.n k.c) (gP k.G) WeightedRawWords.noW j).length ≤
      sfB k :=
  SF_len k (Sum.inl j)

/-- Abbreviation: the assembly exit-cell majorant at the level-0 arguments of `exA`. -/
noncomputable def exB0 (k : L0) : ℕ := exB (aP k.G k.n k.c) (qP k.G k.n k.c) (tP k.G k.n k.c) (iP k.G k.n k.c).rows

theorem exA_len (k : L0) (x : EntryFamilyAssembly.ACell) : (exA k.G k.n k.c x).length ≤ exB0 k := by
  unfold exA exB0
  exact exitBank_len _ _ _ _ _ x

theorem exB0_eq (k : L0) : exB0 k = exB (aI (φ k)) (qI (φ k)) (tI (φ k)) (rxI (φ k)) := by
  unfold exB0
  dsimp only [φ]

/-- The level-generic `publicBound15` at a level. -/
noncomputable def pb15 (i : LI) : ℕ :=
  WeightedLevelFields15.publicBound15 (PL i) (gI i) (eI i) noW3 (aI i) (sI i) (qI i) (LI' i)
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
    (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i)

/-- Every allowance `bnd` (owner-8) is below the common majorant; case split through the
admitted `bnd_inl`/`bnd_inr` rewrites (a direct `exact` after the split is known to explode,
owner-8 CHECKPOINT). -/
theorem bnd_le (k : L0) (y : EntryFamilyLevel.Stack) :
    bnd k.G k.n k.c y ≤ sfB k + growB k.G k.n k.c + exB0 k := by
  rcases y with j | x
  · rw [EntryPrepFamily.bnd_inl]
    exact Nat.le_add_right_of_le (Nat.add_le_add_right (initial_len k j) _)
  · rw [EntryPrepFamily.bnd_inr]
    exact le_trans (exA_len k x) (Nat.le_add_left _ _)

theorem lenF_le (k : L0) (x : FamIdx) :
    lenF k.G k.n k.c x ≤ sfB k + growB k.G k.n k.c + exB0 k := by
  unfold lenF
  split
  · exact bnd_le k _
  · exact Nat.zero_le _

theorem clearB_le (k : L0) :
    clearB k.G k.n k.c ≤
      nF * (sfB k + growB k.G k.n k.c + exB0 k) := by
  unfold clearB
  calc (∑ i : Fin nF, lenF k.G k.n k.c ((Fintype.equivFin FamIdx).symm i))
      ≤ ∑ _i : Fin nF, (sfB k + growB k.G k.n k.c + exB0 k) :=
        Finset.sum_le_sum (fun i _ => lenF_le k _)
    _ = nF * (sfB k + growB k.G k.n k.c + exB0 k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The polynomial clock of `progF` -/

theorem costE_eq (k : L0) : costE k.G k.n k.c =
    (2 * (LI' (φ k) * qI (φ k) * Construction.qOne (aI (φ k))) + 2) +
      ((2 * (LI' (φ k) * qI (φ k) * rxI (φ k)) + 2) +
        ((2 * Construction.qOne (aI (φ k)) + 2) + ((2 * Construction.qOne (aI (φ k)) + 2) + 0))) := by
  unfold costE
  rw [w0_first, w0_row, MatrixStage4FamilyData.fieldTable_length,
    MatrixStage4FamilyData.fieldTable_length, (w0_fields k).2.2.2]
  dsimp only [φ]
  rfl

theorem phi_facts (k : L0) :
    (PL (φ k)).nextDepth = b0 k.n ∧ (PL (φ k)).cost = y0 k.n + 0 ∧
    (PL (φ k)).sourceConstant = k.c ∧ eI (φ k) = Fintype.card k.E ∧
    ell3 (φ k).G = ell3 k.G ∧ ell3 k.G = (EncodedGraph.encode (gP k.G)).length := by
  dsimp only [φ]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hFam0 : PolyIn U0 (fun k => famBound k.G k.n k.c) :=
  PolyIn.mono (fun k => le_of_eq (famBound_eq k)) (comap0 famClock_poly)

theorem pb15_eq (k : L0) :
    WeightedLevelFields15.publicBound15 (iP k.G k.n k.c) (gP k.G) (Fintype.card k.E)
      WeightedRawWords.noW (aP k.G k.n k.c) (sP k.G k.n k.c) (qP k.G k.n k.c) (LP k.G k.n k.c)
      (dP k.G k.n k.c).binBase (dP k.G k.n k.c).rawWidth (dP k.G k.n k.c).s = pb15 (φ k) := by
  unfold pb15
  rw [dP_binBase, dP_rawWidth, dP_s, noW_eq]
  dsimp only [φ]

theorem hPb15 : PolyIn U pb15 := by
  unfold pb15
  exact hP15

theorem hGrow0 : PolyIn U0 (fun k => growB k.G k.n k.c) := by
  unfold growB
  refine PolyIn.mul (PolyIn.const _) ?_
  exact PolyIn.mono (fun k => le_of_eq (pb15_eq k)) (comap0 hPb15)

theorem pEll0 : PolyIn U0 (fun k => ell3 k.G) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.2.1.symm) (comap0 pEll)
theorem pND0 : PolyIn U0 (fun k => b0 k.n) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).1.symm) (comap0 pND)
theorem pY0 : PolyIn U0 (fun k => y0 k.n) :=
  PolyIn.mono (fun k => by rw [(phi_facts k).2.1]; exact Nat.le_add_right _ _) (comap0 pCost)
theorem pC0 : PolyIn U0 (fun k => k.c) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.1.symm) (comap0 pSC)
theorem pE0 : PolyIn U0 (fun k => Fintype.card k.E) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.1.symm) (comap0 pE)
theorem pEnc0 : PolyIn U0 (fun k => (EncodedGraph.encode (gP k.G)).length) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.2.2.symm) pEll0

theorem hSf0 : PolyIn U0 sfB := by
  unfold sfB
  have h4 := comap0 pCy
  have h5 := comap0 pRx
  have := pEnc0
  have := pND0
  have := pY0
  have := pE0
  have := pC0
  pr

theorem hClear0 : PolyIn U0 (fun k => clearB k.G k.n k.c) := by
  have h0 := comap0 hExB
  have h1 : PolyIn U0 exB0 := PolyIn.mono (fun k => le_of_eq (exB0_eq k)) h0
  have h2 : PolyIn U0 (fun k => sfB k + growB k.G k.n k.c + exB0 k) :=
    PolyIn.add (PolyIn.add hSf0 hGrow0) h1
  have h3 : PolyIn U0 (fun k => nF * (sfB k + growB k.G k.n k.c + exB0 k)) :=
    PolyIn.mul (PolyIn.const _) h2
  exact PolyIn.mono (fun k => clearB_le k) h3

theorem hA0 : PolyIn U0 (fun k => costA k.G) := by
  unfold costA
  have := pEnc0
  pr

theorem hC0 : PolyIn U0 (fun k => costC k.G k.n k.c) := by
  unfold costC
  have hrx' : PolyIn U0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).rx) :=
    PolyIn.mono (fun k => le_of_eq (w0_fields k).1) (comap0 pRx)
  have hcy' : PolyIn U0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).cy) :=
    PolyIn.mono (fun k => le_of_eq (w0_fields k).2.1) (comap0 pCy)
  have := pND0
  have := pY0
  have := pE0
  have := pC0
  pr

theorem hE0 : PolyIn U0 (fun k => costE k.G k.n k.c) := by
  refine PolyIn.mono (fun k => le_of_eq (costE_eq k)) ?_
  have := comap0 pL
  have := comap0 pQ
  have := comap0 pQOne
  have := comap0 pRx
  pr

theorem hS0 : PolyIn U0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).s) :=
  PolyIn.mono (fun k => le_of_eq (w0_fields k).2.2.1) (comap0 pS)

theorem TF_poly0 : PolyIn U0 (fun k => TF k.G k.n k.c) := by
  have := hFam0
  have := hClear0
  have := hA0
  have := hC0
  have := hE0
  have := hS0
  unfold TF
  pr

/-- The naming premise bounds the level size: `U ≤ 2^p * (n + |enc G| + 1)`. -/
theorem U0_le (k : L0) (p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (iP k.G k.n k.c) ≤ p) :
    U0 k ≤ 2 ^ (1 * p) * (k.n + ell3 k.G + 1) ^ 1 := by
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  unfold U0 U
  rw [one_mul, pow_one, (phi_facts k).2.2.2.2.1]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hname) (by omega)

/-- **Segment 1.** The clock `TF` of owner-8's family program is polynomial:
ONE absolute constant `C` for all graphs and all `n c p` under the naming premise. -/
theorem TF_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c p : ℕ),
    EffectiveIteration.oneLevelBound (iP G n c) ≤ p →
    TF G n c ≤ (n + ell3 G + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := TF_poly0
  refine ⟨K + 2 * 2 * D, fun {V E} _ _ _ _ G n c p hname => ?_⟩
  let k : L0 := ⟨V, E, G, n, c⟩
  have h1 := hKD k
  have hU := U0_le k p hname
  have hell := card_le_ell3 G
  have hp : 1 ≤ p := by
    have h128 := (EffectiveIteration.parameter_size_bounds (iP G n c)).1
    rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
    have : 1 ≤ Parameters.balanceOrder (iP G n c) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hab := EntryClockPoly.absorb K D 1 1 (n + ell3 G + 1) p (U0 k) (by omega) hp hU
  have e : (K + 2 * (1 + 1) * D) * p = (K + 2 * 2 * D) * p := by ring
  have e' : K + 2 * 1 * D ≤ K + 2 * 2 * D := by omega
  have hX1 : 1 ≤ n + ell3 G + 1 := by omega
  have hmono : (n + ell3 G + 1) ^ (K + 2 * 1 * D) ≤ (n + ell3 G + 1) ^ (K + 2 * 2 * D) :=
    Nat.pow_le_pow_right hX1 e'
  rw [e] at hab
  exact h1.trans (hab.trans (Nat.add_le_add_right hmono _))

#print axioms exitBank_len
#print axioms SF_len
#print axioms clearB_le
#print axioms TF_poly0
#print axioms TF_le

end EthInapproximability.CurrentPaper.EntryClockPoly3
