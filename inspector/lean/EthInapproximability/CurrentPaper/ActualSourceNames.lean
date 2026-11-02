import EthInapproximability.CurrentPaper.ActualCarrierBounds
import EthInapproximability.CurrentPaper.ActualCountLevelClock

/-! Source-facing count classes for the arbitrary-p clock. Every field below is
an actual naming-length, parameter-description, auxiliary-width, or numerical
depth clause from the frozen `thm:paper-materialization` (B-effectivity-details
90-95); the raw carrier names are the exact `Iteration` numberings. The task
of identifying these clauses with a future total input checker is separate. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualSourceNames

open EntryClockPoly3 ActualCountClock ActualCarrierBounds

set_option maxHeartbeats 3000000

/-- A level's literal source classes, without an artificial `oneLevelBound`
condition or any already-computed runtime. -/
structure Names (i : LI) (p : ℕ) : Prop where
  rawRows : Nat.clog 2 (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p
  rawCols : Nat.clog 2 (Iteration.rawColumnNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p
  inputRows : Nat.clog 2 (rxI i) ≤ p
  inputCols : Nat.clog 2 (cyI i) ≤ p
  orderWidth : tI i ≤ p
  firstWidth : Construction.qOne (aI i) ≤ p
  binsDescription : Nat.clog 2 (sI i) ≤ p
  scaleDescription : Nat.clog 2 (Parameters.scale (PL i)) ≤ p
  sourceDescription : Nat.clog 2 ((PL i).sourceConstant) ≤ p
  costDescription : Nat.clog 2 ((PL i).cost) ≤ p
  restrictionDepth : (PL i).nextDepth ≤ p

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

private theorem le_two_pow (p : ℕ) : p ≤ 2 ^ p := Nat.le_of_lt Nat.lt_two_pow_self

theorem source_primitives (i : LI) (p : ℕ) (h : Names i p) :
    LI' i ≤ 2 ^ p ∧ pI i ≤ 2 ^ p ∧
    MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i) ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤ 2 ^ p ∧
    cyI i ^ (sI i + 1) ≤ 2 ^ p ∧
    rxI i ≤ 2 ^ p ∧ cyI i ≤ 2 ^ p ∧
    sI i ≤ 2 ^ p ∧ Parameters.scale (PL i) ≤ 2 ^ p ∧
    (PL i).sourceConstant ≤ 2 ^ p ∧ (PL i).cost ≤ 2 ^ p ∧
    tI i ≤ 2 ^ p ∧ 2 ^ tI i ≤ 2 ^ p ∧
    (PL i).nextDepth ≤ 2 ^ p := by
  obtain ⟨hL, hpI, hW, hB, hBs, hCy⟩ :=
    level_large_counts_of_raw_carriers i p h.rawRows h.rawCols
  have hS := from_clog h.binsDescription
  have hT : tI i ≤ 2 ^ p := h.orderWidth.trans (le_two_pow p)
  have h2T : 2 ^ tI i ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) h.orderWidth
  exact ⟨hL, hpI, hW, hB, hBs, hCy, from_clog h.inputRows,
    from_clog h.inputCols, hS, from_clog h.scaleDescription,
    from_clog h.sourceDescription, from_clog h.costDescription,
    hT, h2T, h.restrictionDepth.trans (le_two_pow p)⟩

private theorem sum_le_length_mul (xs : List ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, x ≤ B) : xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      simp only [List.sum_cons, List.length_cons]
      have hx : x ≤ B := h x (List.mem_cons_self ..)
      have hy : ∀ z ∈ ys, z ≤ B := by
        intro z hz
        exact h z (List.mem_cons_of_mem _ hz)
      calc
        x + ys.sum ≤ B + ys.length * B := Nat.add_le_add hx (ih hy)
        _ = (ys.length + 1) * B := by ring

/-- All 25 literal scalar/table counts are bounded by one fixed multiple of
`2^p(|enc G|+1)` from the named source classes. This is an accounting lemma;
none of its fields is a machine clock or a desired output conclusion. -/
theorem actual_counts_source_bound (i : LI) (p : ℕ) (h : Names i p) :
    A i ≤ 800 * 2 ^ p * (ell3 i.G + 1) := by
  let P := 2 ^ p
  let X := ell3 i.G + 1
  let B := 32 * P * X
  have hP : 1 ≤ P := by dsimp [P]; exact Nat.one_le_pow _ _ (by decide)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hbase : P ≤ B := by dsimp [B]; nlinarith
  have h3 : 3 * P ≤ B := by dsimp [B]; nlinarith
  have hqbase : 24 * P * ell3 i.G ≤ B := by
    dsimp [B, X]
    nlinarith
  have hprim := source_primitives i p h
  rcases hprim with ⟨hL, hpI, hW, hBin, hBinS, hCyS, hRx, hCy, hS,
    hScale, hSC, hCost, hT, h2T, hDepth⟩
  have hq : qI i ≤ B := (q2_le_of_actual_bin i p hS).trans hqbase
  have ha1 : 1 ≤ aI i := by
    have hs := Parameters.scale_floor (PL i)
    unfold aI Parameters.firstExponent
    nlinarith
  have h2a : 2 ^ aI i ≤ 3 * P := by
    have heq := Construction.qOne_add_two (aI i) ha1
    have haux := h.firstWidth
    have hpP := le_two_pow p
    dsimp [P]
    omega
  have ha : aI i ≤ B :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (h2a.trans h3)
  have hFL : Construction.firstLength (aI i) (sI i) ≤ B := by
    have hpP := le_two_pow p
    have hAux := h.firstWidth
    have hSp := hS
    have h3P : Construction.firstLength (aI i) (sI i) ≤ 3 * P := by
      unfold Construction.firstLength
      dsimp [P]
      omega
    exact h3P.trans h3
  have hqOne : Construction.qOne (aI i) ≤ B :=
    (h.firstWidth.trans (le_two_pow p)).trans hbase
  have hgraph := card_le_ell3 i.G
  have hEll : ell3 i.G ≤ B := by dsimp [B, X]; nlinarith
  have hEdges : (PL i).edges ≤ B := by
    change Fintype.card i.E ≤ B
    omega
  have hVert : (gI i).vertices ≤ B := by
    change Fintype.card i.V ≤ B
    omega
  have hAll : ∀ x ∈ counts i, x ≤ B := by
    intro x hx
    simp only [counts, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact hT.trans hbase
      | exact h2T.trans hbase
      | exact ha
      | exact h2a.trans h3
      | exact hS.trans hbase
      | exact hqOne
      | exact hFL
      | exact hq
      | exact hRx.trans hbase
      | exact hCy.trans hbase
      | exact hL.trans hbase
      | exact hpI.trans hbase
      | exact hW.trans hbase
      | exact hBin.trans hbase
      | exact hBinS.trans hbase
      | exact hCyS.trans hbase
      | exact hScale.trans hbase
      | exact hSC.trans hbase
      | exact hDepth.trans hbase
      | exact hCost.trans hbase
      | exact hEdges
      | exact hEll
      | exact hVert
  have hsum := sum_le_length_mul (counts i) B hAll
  have hlen : (counts i).length = 25 := by simp [counts]
  unfold A
  rw [hlen] at hsum
  have heq : 25 * B = 800 * 2 ^ p * (ell3 i.G + 1) := by
    dsimp [B, P, X]
    ring
  exact hsum.trans_eq heq

/-- The fixed level-j family program has the literal source clock shape for
*arbitrary* admissible `p`, using only named raw/input carriers, parameter
descriptions, auxiliary widths, numerical depth and `p ≥ clog₂(n+2)`.
No `oneLevelBound ≤ p`, selected cutoff, machine clock, or already-materialized
table is assumed. -/
theorem TFJ_clock_from_source_names : ∃ C : ℕ, ∀ (i : LI) (n p : ℕ),
    Nat.clog 2 (n + 2) ≤ p → Names i p →
    EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M ≤
      (n + ell3 i.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := ActualCountClock.TFJ_poly
  let C := K + 24 * D
  refine ⟨C, fun i n p hfloor hnames => ?_⟩
  have hp : 1 ≤ p := by
    have hclog := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  let X := n + ell3 i.G + 2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have h800 : 800 ≤ 2 ^ (10 * p) := by
    calc
      800 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (10 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have hA : A i ≤ 2 ^ (11 * p) * X := by
    calc
      A i ≤ 800 * 2 ^ p * (ell3 i.G + 1) := actual_counts_source_bound i p hnames
      _ ≤ 2 ^ (10 * p) * 2 ^ p * (ell3 i.G + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h800)
      _ = 2 ^ (11 * p) * (ell3 i.G + 1) := by
        rw [← pow_add]
        rw [show 10 * p + p = 11 * p by omega]
      _ ≤ 2 ^ (11 * p) * X := Nat.mul_le_mul_left _ (by dsimp [X]; omega)
  have hab := EntryClockPoly.absorb K D 11 1 X p (A i) hX hp (by
    simpa only [pow_one] using hA)
  calc
    EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M ≤ K * (A i + 1) ^ D := hKD i
    _ ≤ X ^ (K + 2 * D) + 2 ^ ((K + 24 * D) * p) := by
      simpa only [show 2 * 1 * D = 2 * D by omega,
        show 2 * (11 + 1) * D = 24 * D by omega] using hab
    _ ≤ X ^ C + 2 ^ (C * p) :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) (by dsimp [C]; omega))
        (by dsimp [C]; exact le_refl _)

#print axioms source_primitives
#print axioms actual_counts_source_bound
#print axioms TFJ_clock_from_source_names

end EthInapproximability.CurrentPaper.ActualSourceNames
