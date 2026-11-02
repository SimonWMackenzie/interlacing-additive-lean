import EthInapproximability.CurrentPaper.ActualCountLevel0Clock

/-! A source-identification refinement: the balanced-family order is bounded
by the raw row *binary naming length*. It need not be independently included
among the source's numerical auxiliary-width hypotheses. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualOrderFromCarrier

open EntryClockPoly3 ActualCarrierBounds

theorem order_le_of_raw_row_name (i : LI) (p : ℕ)
    (hrow : Nat.clog 2
      (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p) :
    tI i ≤ p := by
  have hsize : (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size ≤ 2 ^ p :=
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
      (Nat.pow_le_pow_right (by decide) hrow)
  have hL : LI' i ≤ 2 ^ p := by
    have hs : 1 ≤ sI i := Parameters.bins_pos (PL i)
    have hrows := (iteration_raw_carrier_sizes i).1
    have hL0 : LI' i ≤ MatrixStage4Codes.rows (sI i) (LI' i)
        (GraphVectors.vertexCount i.V (sI i))
        (GraphVectors.auxiliaryCount (sI i)) (rxI i) := by
      unfold MatrixStage4Codes.rows
      nlinarith
    exact hL0.trans (by rw [← hrows]; exact hsize)
  have hp2 : 2 ≤ pI i :=
    EthInapproximability.ParameterizedNP.BalancedFamilyBuilder.two_le_balPrime _ _ _
  have hpow : 2 ^ tI i ≤ 2 ^ p := by
    calc
      2 ^ tI i ≤ pI i ^ tI i := Nat.pow_le_pow_left hp2 _
      _ = LI' i := rfl
      _ ≤ 2 ^ p := hL
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow

/-- The source-facing classes after eliminating the redundant balanced-family
order clause. Binary lengths are kept distinct from *numerical* width/depth
clauses. -/
structure SourceNames (i : LI) (p : ℕ) : Prop where
  rawRows : Nat.clog 2 (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p
  rawCols : Nat.clog 2 (Iteration.rawColumnNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p
  inputRows : Nat.clog 2 (rxI i) ≤ p
  inputCols : Nat.clog 2 (cyI i) ≤ p
  firstWidth : Construction.qOne (aI i) ≤ p
  binsDescription : Nat.clog 2 (sI i) ≤ p
  scaleDescription : Nat.clog 2 (Parameters.scale (PL i)) ≤ p
  sourceDescription : Nat.clog 2 ((PL i).sourceConstant) ≤ p
  costDescription : Nat.clog 2 ((PL i).cost) ≤ p
  restrictionDepth : (PL i).nextDepth ≤ p

theorem SourceNames.toNames {i : LI} {p : ℕ} (h : SourceNames i p) :
    ActualSourceNames.Names i p :=
  ⟨h.rawRows, h.rawCols, h.inputRows, h.inputCols,
    order_le_of_raw_row_name i p h.rawRows, h.firstWidth,
    h.binsDescription, h.scaleDescription, h.sourceDescription,
    h.costDescription, h.restrictionDepth⟩

theorem TFJ_clock_from_source_names : ∃ C : ℕ, ∀ (i : LI) (n p : ℕ),
    Nat.clog 2 (n + 2) ≤ p → SourceNames i p →
    EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M ≤
      (n + ell3 i.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨C, hC⟩ := ActualSourceNames.TFJ_clock_from_source_names
  exact ⟨C, fun i n p hfloor hnames => hC i n p hfloor hnames.toNames⟩

theorem TF0_clock_from_source_names : ∃ C : ℕ, ∀ (k : L0) (p : ℕ),
    Nat.clog 2 (k.n + 2) ≤ p → SourceNames (EntryClockPoly3.φ k) p →
    EntryPrepFamily.TF k.G k.n k.c ≤
      (k.n + ell3 k.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨C, hC⟩ := ActualCountLevel0Clock.TF0_clock_from_source_names
  exact ⟨C, fun k p hfloor hnames => hC k p hfloor hnames.toNames⟩

#print axioms order_le_of_raw_row_name
#print axioms TFJ_clock_from_source_names
#print axioms TF0_clock_from_source_names

end EthInapproximability.CurrentPaper.ActualOrderFromCarrier
