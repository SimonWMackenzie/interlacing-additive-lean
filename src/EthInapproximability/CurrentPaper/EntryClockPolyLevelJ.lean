import EthInapproximability.CurrentPaper.EntryClockPolyFinal

/-!
# The level-generic instance and the shape of the level-`j` writer-22 clock

Lane owner:b-entry-clock-2 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic; no machine.
Uses production definitions only (no level-`j` lane object is imported).

* `instL G c b yb lv Mx`: owner-1's `Inst` at the ACTUAL level parameters
  `(G, c, b, yb, lv, Mx)` (the same arguments as the admitted `EntryLevelWords.levelWords`,
  `ProtectedFullBankBridgeScratch.actualD`); `instL G c (b0 n) (y0 n) 0 (M0 n) = inst0 G n c`
  definitionally (`instL_zero`).
* `U_instL_le`: segment 1d at every level, under
  `EffectiveIteration.oneLevelBound (Iteration.stepParameters G c b yb lv Mx) ≤ p`.
* `levelj_shape_le`: ONE absolute `C` with
  `(2 * (rowMajor Mx.entry).length + 3) + restI (instL ..) + bvG ⟨V, E, G, s⟩ + T + 7
     ≤ (|enc G| + 1)^C + 2^(C p) + T`
  for every level. This is the shape of lane entry-levelj-1's `writerBound_j … T`
  (`(2 |matWord Mx| + 3) + prepBound_j (labBound_j T) + (tailBoundJ + clearBoundJ + 1) + 1 + 1`)
  once its pieces are identified with `boundAI/labI/wordI/writerI/clearI (instL ..)` and
  `boundV_j ≤ bvG ⟨V, E, G, sv_j⟩` exactly as `boundA_eq … boundV_le` do at level 0.
  That identification is NOT done here (it needs that lane's private definitions).
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level instance at the actual level parameters. -/
noncomputable def instL (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : Inst where
  a := Iteration.a G c b yb lv Mx
  s := Iteration.s G c b yb lv Mx
  q := Iteration.q₂ G c b yb lv Mx
  L := Iteration.labels G c b yb lv Mx
  nv := GraphVectors.vertexCount V (Iteration.s G c b yb lv Mx)
  nb := GraphVectors.auxiliaryCount (Iteration.s G c b yb lv Mx)
  rx := Mx.rows
  cy := Mx.columns
  R := Mx.entry
  hs := lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c b yb lv Mx)
  family := Iteration.secondFamily G c b yb lv Mx
  order := GraphVectors.itemOrder G (Iteration.s G c b yb lv Mx)
  vectors := GraphVectors.vectors G (Iteration.s G c b yb lv Mx)
  cap := GraphVectors.supportCap G (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b yb lv Mx))

theorem instL_zero (G : EndpointGraph V E) (n c : ℕ) :
    instL G c (EntryTailClear.b0 n) (EntryTailClear.y0 n) 0 (EntryTailClear.M0 n) = inst0 G n c := rfl

abbrev PL (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : Parameters.Input :=
  Iteration.stepParameters G c b yb lv Mx

theorem instL_pos (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    0 < cols (instL G c b yb lv Mx).a (instL G c b yb lv Mx).s (instL G c b yb lv Mx).q
      (instL G c b yb lv Mx).cy := by
  have hc : 0 < (instL G c b yb lv Mx).cy := Mx.columns_pos
  have hq : 0 < (instL G c b yb lv Mx).q := q2_pos G _
  unfold cols
  exact Nat.mul_pos (Nat.pow_pos hc) (Nat.pow_pos (Nat.mul_pos hq (Nat.pow_pos hc)))

theorem instL_fl (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    firstLength (instL G c b yb lv Mx).a (instL G c b yb lv Mx).s =
      Parameters.firstLength (PL G c b yb lv Mx) := by
  show qOne (Parameters.firstExponent (PL G c b yb lv Mx)) + (Parameters.bins (PL G c b yb lv Mx) + 1) =
    Parameters.firstWidth (PL G c b yb lv Mx) + Parameters.bins (PL G c b yb lv Mx) + 1
  unfold qOne Parameters.firstWidth
  omega

theorem colsL_le_protected (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    cols (instL G c b yb lv Mx).a (instL G c b yb lv Mx).s (instL G c b yb lv Mx).q
      (instL G c b yb lv Mx).cy ≤ EffectiveIteration.protectedColumnCount (PL G c b yb lv Mx) := by
  have hfl := instL_fl G c b yb lv Mx
  unfold cols
  rw [hfl]
  change (PL G c b yb lv Mx).columns ^ (Parameters.bins (PL G c b yb lv Mx) + 1) *
      (Parameters.secondWidth (PL G c b yb lv Mx) *
        (PL G c b yb lv Mx).columns ^ Parameters.firstLength (PL G c b yb lv Mx)) ^
        Parameters.bins (PL G c b yb lv Mx) ≤ _
  unfold EffectiveIteration.protectedColumnCount
  dsimp only
  generalize hU : Parameters.secondWidth (PL G c b yb lv Mx) * (PL G c b yb lv Mx).columns ^
    Parameters.firstLength (PL G c b yb lv Mx) = U
  have hq : 0 < Parameters.secondWidth (PL G c b yb lv Mx) := Parameters.secondWidth_pos _
  have hc : 0 < (PL G c b yb lv Mx).columns := Mx.columns_pos
  have hU1 : 1 ≤ U := by
    rw [← hU]; exact Nat.mul_pos hq (Nat.pow_pos hc)
  have hUs : 1 ≤ U ^ Parameters.bins (PL G c b yb lv Mx) := Nat.one_le_pow _ _ hU1
  generalize (PL G c b yb lv Mx).columns ^ (Parameters.bins (PL G c b yb lv Mx) + 1) *
    U ^ Parameters.bins (PL G c b yb lv Mx) = X
  calc X ≤ 184 * X := by omega
    _ ≤ 184 * X * U := Nat.le_mul_of_pos_right _ hU1
    _ ≤ 184 * X * U * U ^ Parameters.bins (PL G c b yb lv Mx) := Nat.le_mul_of_pos_right _ hUs

/-- Segment 1d at every level. -/
theorem U_instL_le (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) (p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (PL G c b yb lv Mx) ≤ p) :
    128 ≤ p ∧ (instL G c b yb lv Mx).s ≤ p ∧ (instL G c b yb lv Mx).q ≤ 2 ^ p ∧
      (instL G c b yb lv Mx).U ≤ 3 * 2 ^ p + 2 * p + 4 * p ^ 2 + 4 * p * Fintype.card V := by
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  obtain ⟨h128, _, _, hs, hfl, hq2, _⟩ := EffectiveIteration.parameter_size_bounds (PL G c b yb lv Mx)
  generalize hT : Parameters.balanceOrder (PL G c b yb lv Mx) = T at hname h128 hs hfl hq2
  have hT1 : 1 ≤ T := by omega
  have hT2 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by decide)
  have hT3 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
  have hT14 : T ≤ T ^ 4 := by
    calc T = T ^ 1 := (pow_one T).symm
      _ ≤ T ^ 4 := Nat.pow_le_pow_right hT1 (by decide)
  have hTp : T ≤ p := by omega
  have h3p : 16 * T ^ 3 ≤ p := by omega
  have h2p : 16 * T ^ 2 ≤ p := by omega
  have hsv : (instL G c b yb lv Mx).s ≤ p := by
    change Parameters.bins (PL G c b yb lv Mx) ≤ p; omega
  have hq : (instL G c b yb lv Mx).q ≤ 2 ^ p := by
    change 2 ^ Parameters.secondExponent (PL G c b yb lv Mx) ≤ 2 ^ p
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨by omega, hsv, hq, ?_⟩
  have hcols : cols (instL G c b yb lv Mx).a (instL G c b yb lv Mx).s (instL G c b yb lv Mx).q
      (instL G c b yb lv Mx).cy ≤ 2 ^ p := by
    have h := (colsL_le_protected G c b yb lv Mx).trans
      (EffectiveIteration.protectedColumnCount_bound _)
    rw [hT] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) h3p)
  have hL : (instL G c b yb lv Mx).L ≤ 2 ^ p := by
    have h := EffectiveIteration.familySize_bound (PL G c b yb lv Mx)
    rw [hT] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) h2p)
  have hrx : (instL G c b yb lv Mx).rx ≤ 2 ^ p := by
    have h := (EffectiveIteration.input_cardinality_bounds (PL G c b yb lv Mx)).1
    rw [hT] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) hTp)
  have hflv : firstLength (instL G c b yb lv Mx).a (instL G c b yb lv Mx).s ≤ p := by
    rw [instL_fl]; omega
  have hitems : (instL G c b yb lv Mx).nv + (instL G c b yb lv Mx).nb ≤
      4 * p * Fintype.card V + 4 * p ^ 2 := by
    show 4 * (instL G c b yb lv Mx).s * Fintype.card V +
      4 * (instL G c b yb lv Mx).s * ((instL G c b yb lv Mx).s - 3) ≤ _
    have e1 : 4 * (instL G c b yb lv Mx).s * Fintype.card V ≤ 4 * p * Fintype.card V :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsv)
    have e2 : 4 * (instL G c b yb lv Mx).s * ((instL G c b yb lv Mx).s - 3) ≤ 4 * p * p :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hsv) ((Nat.sub_le _ _).trans hsv)
    have e3 : 4 * p * p = 4 * p ^ 2 := by ring
    omega
  unfold Inst.U
  omega

/-- The level-`j` writer-22 clock shape: ONE absolute `C`, uniform over levels. -/
theorem levelj_shape_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) (p T : ℕ),
    EffectiveIteration.oneLevelBound (PL G c b yb lv Mx) ≤ p →
    (((2 * (rowMajor Mx.entry).length + 2) + 0) + 1) + restI (instL G c b yb lv Mx) +
        bvG ⟨V, E, G, (instL G c b yb lv Mx).s⟩ + T + 7 ≤
      (ellG G + 1) ^ C + 2 ^ (C * p) + T := by
  obtain ⟨K1, D1, h1⟩ := restI_poly
  obtain ⟨K2, D2, h2⟩ := bvG_poly
  let C1 := K1 + 2 * 1 * D1
  let C1' := K1 + 2 * (6 + 1) * D1
  let C2 := K2 + 2 * 2 * D2
  let C2' := K2 + 2 * (4 + 1) * D2
  let M := C1 + C1' + C2 + C2' + 2
  refine ⟨M + 5, ?_⟩
  intro V E _ _ _ _ G c b yb lv Mx p T hname
  obtain ⟨hp, hs, hq, hU⟩ := U_instL_le G c b yb lv Mx p hname
  have hX : 2 ≤ ellG G + 1 := by have := ell_two G; omega
  have hp1 : 1 ≤ p := by omega
  have hV : Fintype.card V ≤ ellG G + 1 := by have := card_le_ell G; omega
  have hpp : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self
  have h1p : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have e2 : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  have hXpos : 1 ≤ ellG G + 1 := by omega
  -- the instance size in product shape
  have hUp : (instL G c b yb lv Mx).U ≤ 2 ^ (6 * p) * (ellG G + 1) := by
    have hp2 : p ^ 2 ≤ 2 ^ (2 * p) := by rw [pow_mul', sq]; nlinarith
    have hpX : p * Fintype.card V ≤ 2 ^ p * (ellG G + 1) := Nat.mul_le_mul hpp hV
    have e6 : 2 ^ (6 * p) = 2 ^ (2 * p) * 2 ^ (4 * p) := by rw [← pow_add]; congr 1; ring
    have h16 : 16 ≤ 2 ^ (4 * p) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
    have a1 : 2 ^ p ≤ 2 ^ (2 * p) * (ellG G + 1) := by rw [e2]; nlinarith
    have a2 : p ^ 2 ≤ 2 ^ (2 * p) * (ellG G + 1) := hp2.trans (Nat.le_mul_of_pos_right _ hXpos)
    have a3 : 2 ^ p * (ellG G + 1) ≤ 2 ^ (2 * p) * (ellG G + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
    have a4 : 4 * p * Fintype.card V = 4 * (p * Fintype.card V) := by ring
    have hsum : (instL G c b yb lv Mx).U ≤ 13 * (2 ^ (2 * p) * (ellG G + 1)) := by omega
    calc _ ≤ 13 * (2 ^ (2 * p) * (ellG G + 1)) := hsum
      _ ≤ 2 ^ (4 * p) * (2 ^ (2 * p) * (ellG G + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (6 * p) * (ellG G + 1) := by rw [e6]; ring
  -- the graph-piece size in product shape
  have hUG : UG ⟨V, E, G, (instL G c b yb lv Mx).s⟩ ≤ 2 ^ (4 * p) * (ellG G + 1) ^ 2 := by
    have hstr := stream_le G
    have e4 : 2 ^ (4 * p) = 2 ^ p * 2 ^ (3 * p) := by rw [← pow_add]; congr 1; ring
    have h16 : 16 ≤ 2 ^ (3 * p) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (3 * p) := Nat.pow_le_pow_right (by decide) (by omega)
    unfold UG
    dsimp only
    have hq' : q2 G (instL G c b yb lv Mx).s ≤ 2 ^ p := hq
    generalize hXd : ellG G + 1 = X at hX ⊢
    have hℓ : ellG G ≤ X := by omega
    have hstr' : strG G ≤ X * (2 * X + 2) := hstr.trans (Nat.mul_le_mul hℓ (by omega))
    have hX2 : X * (2 * X + 2) ≤ 3 * X ^ 2 := by nlinarith
    have hXX : X ≤ X ^ 2 := by nlinarith
    have b1 : 2 ^ p ≤ 2 ^ p * X ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have b2 : X ^ 2 ≤ 2 ^ p * X ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    have hsum : (instL G c b yb lv Mx).s + ellG G + q2 G (instL G c b yb lv Mx).s + strG G ≤
        6 * (2 ^ p * X ^ 2) := by omega
    calc _ ≤ 6 * (2 ^ p * X ^ 2) := hsum
      _ ≤ 2 ^ (3 * p) * (2 ^ p * X ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (4 * p) * X ^ 2 := by rw [e4]; ring
  have hr : restI (instL G c b yb lv Mx) ≤ (ellG G + 1) ^ C1 + 2 ^ (C1' * p) := by
    refine (h1 ⟨instL G c b yb lv Mx, instL_pos G c b yb lv Mx⟩).trans ?_
    have := absorb K1 D1 6 1 (ellG G + 1) p (instL G c b yb lv Mx).U hX hp1 (by simpa using hUp)
    simpa using this
  have hv : bvG ⟨V, E, G, (instL G c b yb lv Mx).s⟩ ≤ (ellG G + 1) ^ C2 + 2 ^ (C2' * p) :=
    (h2 _).trans (absorb K2 D2 4 2 (ellG G + 1) p _ hX hp1 hUG)
  -- the matrix-word copy: |rowMajor Mx.entry| = rows * columns ≤ 2^(2p)
  have hmw : (rowMajor Mx.entry).length ≤ 2 ^ (2 * p) := by
    rw [rowMajor_length]
    have h1 := (EffectiveIteration.input_cardinality_bounds (PL G c b yb lv Mx)).1
    have h2' := (EffectiveIteration.input_cardinality_bounds (PL G c b yb lv Mx)).2.1
    obtain ⟨_, _, _, _, _, _, _⟩ := EffectiveIteration.parameter_size_bounds (PL G c b yb lv Mx)
    have hT : Parameters.balanceOrder (PL G c b yb lv Mx) ≤ p := by
      have := (EffectiveIteration.balanceOrder_le_oneLevelBound (PL G c b yb lv Mx)).trans hname
      exact this
    have hr' : Mx.rows ≤ 2 ^ p := h1.trans (Nat.pow_le_pow_right (by decide) hT)
    have hc' : Mx.columns ≤ 2 ^ p := h2'.trans (Nat.pow_le_pow_right (by decide) hT)
    rw [e2]; exact Nat.mul_le_mul hr' hc'
  generalize ellG G + 1 = X at hX hr hv ⊢
  have hX1 : 1 ≤ X := by omega
  have m1 : X ^ C1 ≤ X ^ M := Nat.pow_le_pow_right hX1 (by omega)
  have m2 : X ^ C2 ≤ X ^ M := Nat.pow_le_pow_right hX1 (by omega)
  have q1 : 2 ^ (C1' * p) ≤ 2 ^ (M * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have q2' : 2 ^ (C2' * p) ≤ 2 ^ (M * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have q3 : 2 ^ (2 * p) ≤ 2 ^ (M * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have x32 : 32 ≤ X ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ X ^ 5 := Nat.pow_le_pow_left hX _
  have t32 : 32 ≤ 2 ^ (5 * p) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (5 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have eX : X ^ (M + 5) = X ^ M * X ^ 5 := pow_add _ _ _
  have e5 : 2 ^ ((M + 5) * p) = 2 ^ (M * p) * 2 ^ (5 * p) := by rw [← pow_add]; congr 1; ring
  have hXM : 1 ≤ X ^ M := Nat.one_le_pow _ _ (by omega)
  have g1 : 32 * X ^ M ≤ X ^ M * X ^ 5 := by rw [mul_comm]; exact Nat.mul_le_mul_left _ x32
  have g2 : 32 * 2 ^ (M * p) ≤ 2 ^ (M * p) * 2 ^ (5 * p) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ t32
  rw [eX, e5]
  omega

#print axioms instL_zero
#print axioms U_instL_le
#print axioms levelj_shape_le

end EthInapproximability.CurrentPaper.EntryClockPoly
