import Paper2.YaoAllScalarBanks
import Paper2.ClearAll
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 5 segment Y6, part 1 (lane a-yao-owner-2): the count stage of the
Yao prelude.

Consumer: the prelude `YaoPrelude.prelude` (Y6), whose outputs feed the index
decoder Y4 (divisors `sel`, `pay`, `pow`) and the position machine Y3 (`K`).
One fixed program per `(t, lambda)`, placed by an arbitrary embedding
`κ : CStack t lambda ⊕ Fin 5 ↪ J`.  Named cells: `inr 0` unary `e` (preserved),
`inr 1`, `inr 2`, `inr 3` outputs, `inr 4` copy scratch; the `inl` region holds
the admitted composed edge-to-selector-count machine
(`YaoParameterBank.edge_to_count_four_banks`, machine
`program logPowerMachine (selectorCountMachine t lambda)`).
Six stages, five charged handoffs (`BitMachineRawSequence.runs`):
copy `e` into the machine input; the admitted machine run (embedded by
`BitMachineStackEmbedding.outputs`); three charged copies out
(`b = paddedEdgeBits e`, `pow = paddedEdgeCount e`,
`sel = selectorCount t b lambda`); the production `ClearAll.all_run` clearing
every machine cell, with `Lmax` from the admitted
`BitMachineStackGrowth.run_growth`.
Exit bank exact: the three output cells written; every other cell (including
the whole machine region and the scratch) as at entry. -/

noncomputable section

namespace Paper2.YaoPrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoParameterLoader
open Paper2.YaoParameterBank
open Paper2.YaoLowerBound
open Paper2.YaoLookup

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Stack type of the admitted composed count machine. -/
abbrev CStack (t lambda : ℕ) :=
  BitMachineComposition.Stack logPowerMachine (selectorCountMachine t lambda)
abbrev CLabel (t lambda : ℕ) :=
  BitMachineComposition.Label logPowerMachine (selectorCountMachine t lambda)
abbrev CControl (t lambda : ℕ) :=
  BitMachineComposition.Control logPowerMachine (selectorCountMachine t lambda)

/-- The admitted composed program. -/
noncomputable def countLocal (t lambda : ℕ) :=
  BitMachineComposition.program logPowerMachine (selectorCountMachine t lambda)

/-- The admitted start configuration: unary `e` in the machine input only. -/
noncomputable def countInit (t lambda e : ℕ) :
    TM2.Cfg (fun _ : CStack t lambda => Bool) (CLabel t lambda) (CControl t lambda) :=
  rawInit (.inl logPowerMachine.input) (.inl logPowerMachine.start)
    (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none)
    (List.replicate e true)

/-- Explicit bound on the admitted count-machine clock. -/
def countBound (t lambda e : ℕ) : ℕ :=
  (2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
    2*paddedEdgeBits e+2 + 16*paddedEdgeCount e) + 2*paddedEdgeCount e + 2 +
  (1 + MatrixAddressMachine.exactTime (paddedEdgeCount e) (fixedWidth t) (fixedTail t lambda))

/-- The admitted run, restated: one halting local run with the three
output cells named, within `countBound`. -/
theorem count_local (t lambda e : ℕ) :
    ∃ n ≤ countBound t lambda e,
      (((advance (countLocal t lambda))^[n]) (countInit t lambda e)).l = none ∧
      (((advance (countLocal t lambda))^[n]) (countInit t lambda e)).stk (.inl bitsCell) =
        List.replicate (paddedEdgeBits e) true ∧
      (((advance (countLocal t lambda))^[n]) (countInit t lambda e)).stk
          (.inr (.inl (selectorCountMachine t lambda).input)) =
        List.replicate (paddedEdgeCount e) true ∧
      (((advance (countLocal t lambda))^[n]) (countInit t lambda e)).stk
          (.inr (.inl (selectorCountMachine t lambda).output)) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true := by
  obtain ⟨a, b, ha, hb, hrest⟩ := edge_to_count_four_banks t e lambda
  dsimp only at hrest
  obtain ⟨_, hl, _, hbits, hpow, hsel⟩ := hrest
  refine ⟨a + 2*paddedEdgeCount e+2+b, ?_, hl, hbits, hpow, hsel⟩
  unfold countBound
  omega

/-! ## Placement -/

variable {J : Type*} [DecidableEq J]

section Placement

variable {t lambda : ℕ}

/-- The embedded machine region. -/
def region (κ : CStack t lambda ⊕ Fin 5 ↪ J) : CStack t lambda ↪ J :=
  (Function.Embedding.inl).trans κ

def c3 (p q r : CStack t lambda ⊕ Fin 5)
    (h : Function.Injective ![p, q, r]) : Fin 3 ↪ CStack t lambda ⊕ Fin 5 :=
  ⟨![p, q, r], h⟩

/-- Copy `e` into the machine input. -/
def copyIn : Fin 3 ↪ CStack t lambda ⊕ Fin 5 :=
  c3 (.inr 0) (.inl (.inl logPowerMachine.input)) (.inr 4) (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
def copyB : Fin 3 ↪ CStack t lambda ⊕ Fin 5 :=
  c3 (.inl (.inl bitsCell)) (.inr 1) (.inr 4) (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
def copyP : Fin 3 ↪ CStack t lambda ⊕ Fin 5 :=
  c3 (.inl (.inr (.inl (selectorCountMachine t lambda).input))) (.inr 2) (.inr 4) (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
def copyS : Fin 3 ↪ CStack t lambda ⊕ Fin 5 :=
  c3 (.inl (.inr (.inl (selectorCountMachine t lambda).output))) (.inr 3) (.inr 4) (by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all)

/-- The machine cells in an explicit (choice-free up to the admitted
`Fintype` instance) order, as the cell list of `ClearAll`. -/
noncomputable def clearCells (κ : CStack t lambda ⊕ Fin 5 ↪ J) :
    Fin (Fintype.card (CStack t lambda)) → J :=
  fun i => region κ ((Fintype.equivFin (CStack t lambda)).symm i)

omit [DecidableEq J] in
theorem clearCells_injective (κ : CStack t lambda ⊕ Fin 5 ↪ J) :
    Function.Injective (clearCells κ) := by
  intro i j h
  exact (Fintype.equivFin (CStack t lambda)).symm.injective ((region κ).injective h)

end Placement

/-- The embedded admitted count machine. -/
noncomputable def countEmb {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J)
    (l : CLabel t lambda) : TM2.Stmt (fun _ : J => Bool) (CLabel t lambda) (CControl t lambda) :=
  BitMachineStackEmbedding.stmt (region κ) id id id none (countLocal t lambda l)

/-- The embedded count run: from a bank whose machine region holds exactly the
admitted start stacks, to the bank with the region replaced by the admitted
final stacks. -/
theorem count_emb_run {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) (e : ℕ)
    (W : J → List Bool) (hW : ∀ k, W (region κ k) = (countInit t lambda e).stk k) :
    ∃ n ≤ countBound t lambda e, ∃ m ≤ countBound t lambda e, ∃ v,
      ((advance (countEmb κ))^[n])
          (⟨some (.inl logPowerMachine.start),
            (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none), W⟩ :
            TM2.Cfg (fun _ : J => Bool) (CLabel t lambda) (CControl t lambda)) =
        ⟨none, v, BitMachineStackEmbedding.bank (region κ) W
          (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk⟩ ∧
      (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk (.inl bitsCell) =
        List.replicate (paddedEdgeBits e) true ∧
      (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk
          (.inr (.inl (selectorCountMachine t lambda).input)) =
        List.replicate (paddedEdgeCount e) true ∧
      (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk
          (.inr (.inl (selectorCountMachine t lambda).output)) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true := by
  classical
  obtain ⟨m, hm, hl, hb, hp, hs⟩ := count_local t lambda e
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs (region κ) W id id id
    (fun _ => rfl) none (countLocal t lambda) (countEmb κ) (by intro l; rfl)
    (countInit t lambda e) m hl
  have hbank : BitMachineStackEmbedding.bank (region κ) W (countInit t lambda e).stk = W :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun k => (hW k).symm)
  refine ⟨n, hn.trans hm, m, hm,
    (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).var, ?_, hb, hp, hs⟩
  have hc : BitMachineStackEmbedding.cfg (region κ) W id id none (countInit t lambda e) =
      (⟨some (.inl logPowerMachine.start),
        (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none), W⟩ :
        TM2.Cfg (fun _ : J => Bool) (CLabel t lambda) (CControl t lambda)) := by
    change (⟨some (.inl logPowerMachine.start),
      (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none),
      BitMachineStackEmbedding.bank (region κ) W (countInit t lambda e).stk⟩ :
        TM2.Cfg (fun _ : J => Bool) (CLabel t lambda) (CControl t lambda)) = _
    rw [hbank]
  rw [hc] at he
  rw [he]
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  simp only [hl]
  rfl

/-- Length bound on every machine cell at any time of the local run. -/
theorem count_cell_length_le (t lambda e m : ℕ) (hm : m ≤ countBound t lambda e)
    (k : CStack t lambda) :
    ((((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk k).length ≤
      e + BitMachineStackGrowth.perStep (countLocal t lambda) * countBound t lambda e := by
  have hg := BitMachineStackGrowth.run_growth (countLocal t lambda) (countInit t lambda e) m k
  have h0 : ((countInit t lambda e).stk k).length ≤ e := by
    unfold countInit rawInit
    dsimp only
    split <;> simp
  have hmul := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep (countLocal t lambda)) hm
  omega

/-- The uniform clearing clock bound. -/
noncomputable def clearMax (t lambda e : ℕ) : ℕ :=
  e + BitMachineStackGrowth.perStep (countLocal t lambda) * countBound t lambda e

/-! ## The fixed six-stage count program -/

noncomputable def st6 {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  Paper2.ClearAll.prog (clearCells κ)

noncomputable def st56 {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyS.trans κ))
    (st6 κ) (⟨0, by omega⟩ : Fin (Fintype.card (CStack t lambda) + 1)) none none

noncomputable def st456 {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyP.trans κ))
    (st56 κ) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, none)

noncomputable def st3456 {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyB.trans κ))
    (st456 κ) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (none, none))

noncomputable def st23456 {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  BitMachineRawSequence.program (countEmb κ) (st3456 κ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none)
    (none, (none, (none, none)))

/-- The fixed count-stage program (depends only on `t, lambda` and `κ`). -/
noncomputable def countProgram {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (copyIn.trans κ))
    (st23456 κ) (BitMachineRawSequence.leftLabel (.inl logPowerMachine.start)) none
    ((logPowerMachine.initial, (selectorCountMachine t lambda).initial, none),
      (none, (none, (none, none))))

/-- Start control of `countProgram`. -/
def countStartControl (t lambda : ℕ) :
    Option Bool × (CControl t lambda × (Option Bool × (Option Bool × (Option Bool ×
      Option Bool)))) :=
  (none, ((logPowerMachine.initial, (selectorCountMachine t lambda).initial, none),
    (none, (none, (none, none)))))

/-- The exact exit bank: only the three output cells change. -/
def countOut {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J) (W : J → List Bool) (e : ℕ) :
    J → List Bool :=
  Function.update (Function.update (Function.update W (κ (.inr 1))
    (List.replicate (paddedEdgeBits e) true)) (κ (.inr 2))
    (List.replicate (paddedEdgeCount e) true)) (κ (.inr 3))
    (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)

/-- The explicit count-stage clock. -/
noncomputable def countClock (t lambda e : ℕ) : ℕ :=
  (2 * e + 2) + countBound t lambda e + (2 * paddedEdgeBits e + 2) +
    (2 * paddedEdgeCount e + 2) + (2 * selectorCount t (paddedEdgeBits e) lambda + 2) +
    (Fintype.card (CStack t lambda) * (clearMax t lambda e + 1) + 1) + 5

/-- Y6 part 1 main theorem: one physical run of the fixed count program from
charged unary `e` to the exact exit bank. -/
theorem physical_count {t lambda : ℕ} (κ : CStack t lambda ⊕ Fin 5 ↪ J)
    (W : J → List Bool) (e : ℕ)
    (he : W (κ (.inr 0)) = List.replicate e true)
    (h1 : W (κ (.inr 1)) = []) (h2 : W (κ (.inr 2)) = []) (h3 : W (κ (.inr 3)) = [])
    (h4 : W (κ (.inr 4)) = []) (hreg : ∀ k, W (κ (.inl k)) = []) :
    ∃ total ≤ countClock t lambda e, ∃ c',
      ((advance (countProgram κ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          countStartControl t lambda, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', countOut κ W e⟩ := by
  classical
  have hinj := κ.injective
  -- stage 1: copy e into the machine input
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (copyIn.trans κ) W
    (List.replicate e true) (by simp [copyIn, c3, he]) (by simp [copyIn, c3, hreg])
    (by simp [copyIn, c3, h4])
  set W1 := Function.update W ((copyIn.trans κ) 1) (List.replicate e true) with hW1
  -- stage 2: the embedded admitted count machine
  have hW1reg : ∀ k, W1 (region κ k) = (countInit t lambda e).stk k := by
    intro k
    simp only [hW1, region, copyIn, c3, Function.Embedding.trans_apply,
      Function.Embedding.inl_apply, Function.Embedding.coeFn_mk, Matrix.cons_val_one,
      Matrix.cons_val_zero, countInit, rawInit]
    by_cases hk : k = .inl logPowerMachine.input
    · subst hk; simp
    · rw [Function.update_of_ne (fun h => hk (Sum.inl_injective (hinj h))), hreg, if_neg hk]
  obtain ⟨n2, hn2, m, hm, v2, hr2, hb, hp, hs⟩ := count_emb_run κ e W1 hW1reg
  set F := (((advance (countLocal t lambda))^[m]) (countInit t lambda e)).stk with hF
  set W2 := BitMachineStackEmbedding.bank (region κ) W1 F with hW2
  have hW2reg : ∀ k, W2 (κ (.inl k)) = F k := fun k =>
    BitMachineStackEmbedding.bank_at (region κ) W1 F k
  have hW2out : ∀ i : Fin 5, W2 (κ (.inr i)) = W1 (κ (.inr i)) := by
    intro i
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    exact Sum.inl_ne_inr (hinj hk)
  have hW1out : ∀ i : Fin 5, W1 (κ (.inr i)) = W (κ (.inr i)) := by
    intro i
    rw [hW1, Function.update_of_ne]
    intro h
    simp only [copyIn, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      Matrix.cons_val_one, Matrix.cons_val_zero] at h
    exact Sum.inl_ne_inr (hinj h).symm
  -- stage 3-5: three copies out
  obtain ⟨t3, ht3, hr3⟩ := ExactParameterBranchInstall.copy_run (copyB.trans κ) W2
    (List.replicate (paddedEdgeBits e) true)
    (by simp only [copyB, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_zero]; rw [hW2reg]; exact hb)
    (by simp only [copyB, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_one, Matrix.cons_val_zero]; rw [hW2out, hW1out, h1])
    (by simp only [copyB, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk];
        rw [show (![Sum.inl (Sum.inl bitsCell), Sum.inr 1, Sum.inr 4] :
          Fin 3 → CStack t lambda ⊕ Fin 5) 2 = Sum.inr 4 from rfl, hW2out, hW1out, h4])
  set W3 := Function.update W2 ((copyB.trans κ) 1) (List.replicate (paddedEdgeBits e) true)
    with hW3
  have hW3' : W3 = Function.update W2 (κ (.inr 1)) (List.replicate (paddedEdgeBits e) true) :=
    rfl
  obtain ⟨t4, ht4, hr4⟩ := ExactParameterBranchInstall.copy_run (copyP.trans κ) W3
    (List.replicate (paddedEdgeCount e) true)
    (by simp only [copyP, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_zero]
        rw [hW3', Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW2reg]; exact hp)
    (by simp only [copyP, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hW3', Function.update_of_ne (fun h => by simpa using hinj h), hW2out, hW1out, h2])
    (by simp only [copyP, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
        rw [show (![Sum.inl (Sum.inr (Sum.inl (selectorCountMachine t lambda).input)),
          Sum.inr 2, Sum.inr 4] : Fin 3 → CStack t lambda ⊕ Fin 5) 2 = Sum.inr 4 from rfl,
          hW3', Function.update_of_ne (fun h => by simpa using hinj h), hW2out, hW1out, h4])
  set W4 := Function.update W3 ((copyP.trans κ) 1) (List.replicate (paddedEdgeCount e) true)
    with hW4
  have hW4' : W4 = Function.update W3 (κ (.inr 2)) (List.replicate (paddedEdgeCount e) true) :=
    rfl
  obtain ⟨t5, ht5, hr5⟩ := ExactParameterBranchInstall.copy_run (copyS.trans κ) W4
    (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)
    (by simp only [copyS, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_zero]
        rw [hW4', Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW3',
          Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW2reg]; exact hs)
    (by simp only [copyS, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hW4', Function.update_of_ne (fun h => by simpa using hinj h), hW3',
          Function.update_of_ne (fun h => by simpa using hinj h), hW2out, hW1out, h3])
    (by simp only [copyS, c3, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
        rw [show (![Sum.inl (Sum.inr (Sum.inl (selectorCountMachine t lambda).output)),
          Sum.inr 3, Sum.inr 4] : Fin 3 → CStack t lambda ⊕ Fin 5) 2 = Sum.inr 4 from rfl,
          hW4', Function.update_of_ne (fun h => by simpa using hinj h), hW3',
          Function.update_of_ne (fun h => by simpa using hinj h), hW2out, hW1out, h4])
  set W5 := Function.update W4 ((copyS.trans κ) 1)
    (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true) with hW5
  have hW5' : W5 = Function.update W4 (κ (.inr 3))
      (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true) := rfl
  -- stage 6: clear the machine region
  have hW5reg : ∀ k, W5 (κ (.inl k)) = F k := by
    intro k
    rw [hW5', Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW4',
      Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW3',
      Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hW2reg]
  have hL : ∀ j, (W5 (clearCells κ j)).length ≤ clearMax t lambda e := by
    intro j
    simp only [clearCells, region, Function.Embedding.trans_apply, Function.Embedding.inl_apply]
    rw [hW5reg]
    exact count_cell_length_le t lambda e m hm _
  obtain ⟨t6, ht6, v6, hr6⟩ := Paper2.ClearAll.all_run (clearCells κ) (clearCells_injective κ)
    (clearMax t lambda e) W5 hL none
  have hfinal : Paper2.ClearAll.clearFrom (clearCells κ) 0 W5 = countOut κ W e := by
    funext j
    simp only [Paper2.ClearAll.clearFrom]
    by_cases hj : ∃ k, κ (.inl k) = j
    · obtain ⟨k, rfl⟩ := hj
      rw [if_pos ⟨(Fintype.equivFin (CStack t lambda)) k, Nat.zero_le _, by
        simp [clearCells, region]⟩]
      simp only [countOut]
      rw [Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)),
        Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)),
        Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hreg]
    · rw [if_neg (by
        rintro ⟨i, -, hi⟩
        exact hj ⟨_, hi⟩)]
      have hW2j : W2 j = W1 j := BitMachineStackEmbedding.bank_outside (region κ) W1 F j
        (by rintro ⟨k, hk⟩; exact hj ⟨k, hk⟩)
      have hW1j : W1 j = W j := by
        rw [hW1, Function.update_of_ne]
        intro h
        exact hj ⟨_, h.symm⟩
      simp only [countOut, hW5', hW4', hW3', Function.update_apply]
      split_ifs <;> simp [hW2j, hW1j]
  rw [hfinal] at hr6
  -- sequencing with five charged handoffs
  obtain ⟨u5, hu5, hrun5⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyS.trans κ)) (st6 κ)
    BitMachineCopy.Label.scan (⟨0, by omega⟩ : Fin (Fintype.card (CStack t lambda) + 1))
    none none none v6 W4 W5 _ t5 t6 hr5 hr6
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyP.trans κ)) (st56 κ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, none) (none, v6) W3 W4 _ t4 u5 hr4 hrun5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyB.trans κ)) (st456 κ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, none)) (none, (none, v6)) W2 W3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (countEmb κ) (st3456 κ)
    (.inl logPowerMachine.start) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (logPowerMachine.initial, (selectorCountMachine t lambda).initial, none) v2
    (none, (none, (none, none))) (none, (none, (none, v6))) W1 W2 _ n2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copyIn.trans κ)) (st23456 κ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel (.inl logPowerMachine.start))
    none none
    ((logPowerMachine.initial, (selectorCountMachine t lambda).initial, none),
      (none, (none, (none, none))))
    ((logPowerMachine.initial, (selectorCountMachine t lambda).initial, none),
      (none, (none, (none, v6))))
    W W1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht1 ht3 ht4 ht5
  unfold countClock
  omega

#print axioms count_local
#print axioms count_emb_run
#print axioms count_cell_length_le
#print axioms physical_count

end Paper2.YaoPrelude

end
