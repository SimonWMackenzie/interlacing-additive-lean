import EthInapproximability.CurrentPaper.EntryClockPolyFrame

/-!
# Level instances, their size, and the atomic size facts

Lane owner:b-entry-clock-1 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic.

An `Inst` bundles exactly the arguments of the admitted per-entry clock
`EntryRunsRaw.tableT` (unary scalars `a s q L nv nb rx cy` and the data
`R family order vectors cap`). Its size is

  `Inst.U = cols a s q cy + s + L + rx + (nv + nb) + firstLength a s`.

Every other unary scalar the clocks read (`q`, `cy`, `binBase`, `wordBase`,
`binBase^s`, `cy^(s+1)`, `qOne a`, and the partial powers) is bounded by `U`
as soon as the column count is positive (i.e. as soon as an address exists).
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

structure Inst where
  a : ℕ
  s : ℕ
  q : ℕ
  L : ℕ
  nv : ℕ
  nb : ℕ
  rx : ℕ
  cy : ℕ
  R : Fin rx → Fin cy → Bool
  hs : 0 < s
  family : SecondFamily a q L (Fin rx)
  order : ItemOrder nv nb
  vectors : Fin (nv + nb) → Fin q → Bool
  cap : ∀ α, (activeItems vectors α).card ≤ s

/-- The size of a level instance. -/
def Inst.U (I : Inst) : ℕ :=
  cols I.a I.s I.q I.cy + I.s + I.L + I.rx + (I.nv + I.nb) + firstLength I.a I.s

/-! ## Scalar facts from a positive column count -/

section facts

variable {a s q cy : ℕ}

theorem cols_eq : cols a s q cy = cy ^ (s + 1) * binBase a s q cy ^ s := by
  unfold cols binBase wordBase; rfl

theorem cy_pos (h : 0 < cols a s q cy) : 0 < cy := by
  rcases Nat.eq_zero_or_pos cy with h0 | h0
  · subst h0; rw [cols_eq] at h; simp at h
  · exact h0

theorem binBase_pos (hs : 0 < s) (h : 0 < cols a s q cy) : 0 < binBase a s q cy := by
  rcases Nat.eq_zero_or_pos (binBase a s q cy) with h0 | h0
  · rw [cols_eq, h0, Nat.zero_pow hs] at h; simp at h
  · exact h0

theorem binPowS_le (hs : 0 < s) (h : 0 < cols a s q cy) : binBase a s q cy ^ s ≤ cols a s q cy := by
  rw [cols_eq]
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (cy_pos h))

theorem cyPow1_le (hs : 0 < s) (h : 0 < cols a s q cy) : cy ^ (s + 1) ≤ cols a s q cy := by
  rw [cols_eq]
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (binBase_pos hs h))

theorem binBase_le (hs : 0 < s) (h : 0 < cols a s q cy) : binBase a s q cy ≤ cols a s q cy :=
  (Nat.le_self_pow hs.ne' _).trans (binPowS_le hs h)

theorem binPowSub_le (hs : 0 < s) (h : 0 < cols a s q cy) (e : ℕ) :
    binBase a s q cy ^ (s - 1 - e) ≤ cols a s q cy :=
  (Nat.pow_le_pow_right (binBase_pos hs h) (by omega)).trans (binPowS_le hs h)

theorem cyPowSub_le (hs : 0 < s) (h : 0 < cols a s q cy) (e : ℕ) :
    cy ^ (s - e) ≤ cols a s q cy :=
  (Nat.pow_le_pow_right (cy_pos h) (by omega)).trans (cyPow1_le hs h)

theorem cy_le (hs : 0 < s) (h : 0 < cols a s q cy) : cy ≤ cols a s q cy :=
  (Nat.le_self_pow (Nat.succ_ne_zero s) _).trans (cyPow1_le hs h)

theorem wordBase_pos (hs : 0 < s) (h : 0 < cols a s q cy) : 0 < wordBase a s cy := by
  have := binBase_pos hs h
  unfold binBase at this
  exact Nat.pos_of_mul_pos_left this

theorem q_le (hs : 0 < s) (h : 0 < cols a s q cy) : q ≤ cols a s q cy := by
  have h1 : q ≤ binBase a s q cy := by
    unfold binBase; exact Nat.le_mul_of_pos_right _ (wordBase_pos hs h)
  exact h1.trans (binBase_le hs h)

theorem wordBase_le (hs : 0 < s) (h : 0 < cols a s q cy) : wordBase a s cy ≤ cols a s q cy := by
  have h1 : wordBase a s cy ≤ binBase a s q cy := by
    unfold binBase
    have hq : 0 < q := by
      have := binBase_pos hs h
      unfold binBase at this
      exact Nat.pos_of_mul_pos_right this
    exact Nat.le_mul_of_pos_left _ hq
  exact h1.trans (binBase_le hs h)

theorem cyPowFL_le (hs : 0 < s) (h : 0 < cols a s q cy) :
    cy ^ firstLength a s ≤ cols a s q cy := wordBase_le hs h

theorem cyPowFLSub_le (hs : 0 < s) (h : 0 < cols a s q cy) (e : ℕ) :
    cy ^ (firstLength a s - 1 - e) ≤ cols a s q cy :=
  (Nat.pow_le_pow_right (cy_pos h) (by omega)).trans (cyPowFL_le hs h)

theorem qOne_le_firstLength (a s : ℕ) : qOne a ≤ firstLength a s := by
  unfold firstLength; omega

end facts

/-! ## Atoms over any index type mapping to instances with a positive column count -/

section atoms

variable {ι : Type*} (φ : ι → Inst) (hc : ∀ i, 0 < cols (φ i).a (φ i).s (φ i).q (φ i).cy)
include hc

private theorem cols_le_U (i : ι) : cols (φ i).a (φ i).s (φ i).q (φ i).cy ≤ (φ i).U := by
  unfold Inst.U; omega

theorem at_cols : PolyIn (fun i => (φ i).U) (fun i => cols (φ i).a (φ i).s (φ i).q (φ i).cy) :=
  PolyIn.of_le fun i => cols_le_U φ hc i
theorem at_s : PolyIn (fun i => (φ i).U) (fun i => (φ i).s) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_L : PolyIn (fun i => (φ i).U) (fun i => (φ i).L) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_rx : PolyIn (fun i => (φ i).U) (fun i => (φ i).rx) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_nv : PolyIn (fun i => (φ i).U) (fun i => (φ i).nv) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_nb : PolyIn (fun i => (φ i).U) (fun i => (φ i).nb) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_fl : PolyIn (fun i => (φ i).U) (fun i => firstLength (φ i).a (φ i).s) :=
  PolyIn.of_le fun i => by unfold Inst.U; omega
theorem at_qOne : PolyIn (fun i => (φ i).U) (fun i => qOne (φ i).a) :=
  PolyIn.of_le fun i => by
    have := qOne_le_firstLength (φ i).a (φ i).s
    unfold Inst.U; omega
theorem at_q : PolyIn (fun i => (φ i).U) (fun i => (φ i).q) :=
  PolyIn.of_le fun i => (q_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_cy : PolyIn (fun i => (φ i).U) (fun i => (φ i).cy) :=
  PolyIn.of_le fun i => (cy_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_binBase : PolyIn (fun i => (φ i).U) (fun i => binBase (φ i).a (φ i).s (φ i).q (φ i).cy) :=
  PolyIn.of_le fun i => (binBase_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_wordBase : PolyIn (fun i => (φ i).U) (fun i => wordBase (φ i).a (φ i).s (φ i).cy) :=
  PolyIn.of_le fun i => (wordBase_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_cyPowFL : PolyIn (fun i => (φ i).U) (fun i => (φ i).cy ^ firstLength (φ i).a (φ i).s) :=
  PolyIn.of_le fun i => (cyPowFL_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_binPowS : PolyIn (fun i => (φ i).U) (fun i => binBase (φ i).a (φ i).s (φ i).q (φ i).cy ^ (φ i).s) :=
  PolyIn.of_le fun i => (binPowS_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_cyPow1 : PolyIn (fun i => (φ i).U) (fun i => (φ i).cy ^ ((φ i).s + 1)) :=
  PolyIn.of_le fun i => (cyPow1_le (φ i).hs (hc i)).trans (cols_le_U φ hc i)
theorem at_binPowSub (e : ι → ℕ) :
    PolyIn (fun i => (φ i).U) (fun i => binBase (φ i).a (φ i).s (φ i).q (φ i).cy ^ ((φ i).s - 1 - e i)) :=
  PolyIn.of_le fun i => (binPowSub_le (φ i).hs (hc i) (e i)).trans (cols_le_U φ hc i)
theorem at_cyPowSub (e : ι → ℕ) :
    PolyIn (fun i => (φ i).U) (fun i => (φ i).cy ^ ((φ i).s - e i)) :=
  PolyIn.of_le fun i => (cyPowSub_le (φ i).hs (hc i) (e i)).trans (cols_le_U φ hc i)
theorem at_cyPowFLSub (e : ι → ℕ) :
    PolyIn (fun i => (φ i).U) (fun i => (φ i).cy ^ (firstLength (φ i).a (φ i).s - 1 - e i)) :=
  PolyIn.of_le fun i => (cyPowFLSub_le (φ i).hs (hc i) (e i)).trans (cols_le_U φ hc i)
theorem at_rows : PolyIn (fun i => (φ i).U) (fun i => rows (φ i).s (φ i).L (φ i).nv (φ i).nb (φ i).rx) := by
  unfold rows
  exact PolyIn.add (PolyIn.mul (at_s φ hc) (at_L φ hc)) (PolyIn.mul (PolyIn.add (at_nv φ hc) (at_nb φ hc)) (at_rx φ hc))

end atoms

/-! ## Seed-length leaves -/

theorem itemSeed_len (binB wordB sM1 binPowS codeV cyPow1 cyV : ℕ) (Rtable out : List Bool)
    (sV qV : ℕ) (vtable : List Bool) (rowV sL LV rxV : ℕ) :
    ∀ k, (ItemSeed.seed binB wordB sM1 binPowS codeV cyPow1 cyV Rtable out sV qV vtable rowV sL LV
      rxV k).length ≤ binB + wordB + sM1 + binPowS + codeV + cyPow1 + cyV + Rtable.length +
        out.length + sV + qV + vtable.length + rowV + sL + LV + rxV + 1 := by
  unfold ItemSeed.seed
  repeat' (first
    | refine update_len _ _ _ _ ?_ ?_
    | (intro _; simp)
    | (simp only [List.length_replicate, List.length_cons, List.length_nil]; omega)
    | omega)

theorem templateSeed_len (codeV strideV ellV binPowS binB wordB qV qOneV : ℕ)
    (firstTable : List Bool) (cyV firstExp cyPow rxV : ℕ) (rowTable Rtable : List Bool) :
    ∀ k, (TemplateSeed.seed codeV strideV ellV binPowS binB wordB qV qOneV firstTable cyV firstExp
      cyPow rxV rowTable Rtable k).length ≤ codeV + strideV + ellV + binPowS + binB + wordB + qV +
        qOneV + firstTable.length + cyV + firstExp + cyPow + rxV + rowTable.length +
        Rtable.length + 1 := by
  unfold TemplateSeed.seed
  repeat' (first
    | refine update_len _ _ _ _ ?_ ?_
    | (intro _; simp)
    | (simp only [List.length_replicate, List.length_cons, List.length_nil]; omega)
    | omega)

theorem itemSeedLen_le {a s q L cy rx : ℕ} (R : Fin rx → Fin cy → Bool) (vtable : List Bool)
    (code X : ℕ) :
    EntryFull.itemSeedLen (a := a) (s := s) (q := q) (L := L) R vtable code X ≤
      89 * (binBase a s q cy + wordBase a s cy + (s - 1) + binBase a s q cy ^ s + code +
        cy ^ (s + 1) + cy + rx * cy + 0 + s + q + vtable.length + X + s * L + L + rx + 1) := by
  unfold EntryFull.itemSeedLen
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin 89))
    (fun k => (ItemSeed.seed (binBase a s q cy) (wordBase a s cy) (s - 1)
      (binBase a s q cy ^ s) code (cy ^ (s + 1)) cy (rowMajor R) [] s q vtable X (s * L) L rx
        k).length) _ (fun k _ => itemSeed_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k)
  simpa [rowMajor_length] using h

theorem templateSeedLen_le (w : EntryLayout.Words) (y st ell : ℕ) :
    EntryFull.templateSeedLen w y st ell ≤
      Fintype.card EntryLayout.TS * (y + st + ell + w.binPowS + w.binB + w.wordB + w.q + w.qOne +
        w.firstTable.length + w.cy + w.firstExp + w.cyPowF + w.rx + w.rowTable.length +
        w.Rtable.length + 1) := by
  unfold EntryFull.templateSeedLen TemplateSeeding.seedT
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset EntryLayout.TS)
    (fun k => (TemplateSeed.seed y st ell w.binPowS w.binB w.wordB w.q w.qOne w.firstTable
      w.cy w.firstExp w.cyPowF w.rx w.rowTable w.Rtable k).length) _
      (fun k _ => templateSeed_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k)
  simpa using h

#print axioms at_rows
#print axioms itemSeedLen_le
#print axioms templateSeedLen_le

end EthInapproximability.CurrentPaper.EntryClockPoly
