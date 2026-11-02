import EthInapproximability.CurrentPaper.WeightedRawWordsCore
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy

/-! Lane owner:b-weighted-level-6, unit 2, segment 2b, piece 1: the stages of the
cost-word update machine on ONE fixed local stack `CS = Fin 22 ⊕ LogStack`.

Every stage boundary bank is `U vals` (cell `k : Fin 22` holds unary `vals k`,
the log region is blank). Stages (all admitted production programs, embedded):
* `seedP`: one fixed statement pushing the constants `1, 2256, 10000, 12, 1280`
  onto cells 5, 6, 7, 8, 9;
* `mulP v`: `MatrixStage4ScalarPreparationOps.multiplyProgram` on the six cells
  `v`, adding `vals (v 0) * vals (v 1)` to cell `v 5` (inputs restored, the three
  scratch cells blank before and after);
* `logP src dst`: the admitted `ETHParameterScaleMachineLogCopy.program` reading
  cell `src` in place, a charged copy of its output onto cell `dst`, and a
  charged clear of the whole log region (clock by `run_growth` of the SAME log
  run), adding `clog₂ (vals src)` to cell `dst`;
* `clearP`: the charged clear of the twelve temporaries 6..17.
No value is inserted: every word is computed by these runs. -/

namespace EthInapproximability.CurrentPaper.CostUpdateStages

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

abbrev LogStack := ETHParameterScaleMachineLogCopy.Stack
abbrev CS := Fin 22 ⊕ LogStack

abbrev cell (k : Fin 22) : CS := .inl k

theorem cell_inj {a b : Fin 22} (h : cell a = cell b) : a = b := Sum.inl.inj h

/-- The bank with unary `vals k` in cell `k` and a blank log region. -/
def U (vals : Fin 22 → ℕ) : CS → List Bool :=
  Sum.elim (fun k => List.replicate (vals k) true) (fun _ => [])

theorem U_cell (vals : Fin 22 → ℕ) (k : Fin 22) : U vals (cell k) = List.replicate (vals k) true := rfl
theorem U_log (vals : Fin 22 → ℕ) (k : LogStack) : U vals (.inr k) = [] := rfl

theorem U_set (vals : Fin 22 → ℕ) (k : Fin 22) (m : ℕ) :
    Function.update (U vals) (cell k) (List.replicate m true) = U (Function.update vals k m) := by
  funext x
  rcases x with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show _ = List.replicate (Function.update vals j m j) true
      rw [Function.update_self]
    · rw [Function.update_of_ne (fun e => h (cell_inj e))]
      show List.replicate (vals j) true = List.replicate (Function.update vals k m j) true
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl

theorem U_push (vals : Fin 22 → ℕ) (k : Fin 22) (m : ℕ) :
    Function.update (U vals) (cell k) (List.replicate m true ++ U vals (cell k)) =
      U (Function.update vals k (m + vals k)) := by
  rw [U_cell, ← List.replicate_add, U_set]

/-- A run from `⟨some l, v, S⟩` to `⟨none, v, T⟩` within `B` steps (same control
at both ends). -/
def Runs {L V : Type} (P : L → TM2.Stmt (fun _ : CS => Bool) L V) (l : L) (v : V)
    (S T : CS → List Bool) (B : ℕ) : Prop :=
  ∃ t ≤ B, ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : CS => Bool) L V) = ⟨none, v, T⟩

theorem Runs.seq {LA LB VA VB : Type} {A : LA → TM2.Stmt (fun _ : CS => Bool) LA VA}
    {B : LB → TM2.Stmt (fun _ : CS => Bool) LB VB} {a₀ : LA} {b₀ : LB} {v₀ : VA} {w₀ : VB}
    {S T X : CS → List Bool} {Ta Tb : ℕ}
    (ha : Runs A a₀ v₀ S T Ta) (hb : Runs B b₀ w₀ T X Tb) :
    Runs (BitMachineRawSequence.program A B b₀ v₀ w₀) (BitMachineRawSequence.leftLabel a₀)
      (v₀, w₀) S X (Ta + Tb + 1) := by
  obtain ⟨ta, hta, ra⟩ := ha
  obtain ⟨tb, htb, rb⟩ := hb
  obtain ⟨t, ht, r⟩ := BitMachineRawSequence.runs A B a₀ b₀ v₀ v₀ w₀ w₀ S T X ta tb ra rb
  exact ⟨t, by omega, r⟩

/-! ## Seed: fixed unary constants -/

def pushN (k : CS) : ℕ → TM2.Stmt (fun _ : CS => Bool) Unit Unit →
    TM2.Stmt (fun _ : CS => Bool) Unit Unit
  | 0, q => q
  | n + 1, q => .push k (fun _ => true) (pushN k n q)

theorem pushN_stepAux (k : CS) (n : ℕ) (q : TM2.Stmt (fun _ : CS => Bool) Unit Unit)
    (S : CS → List Bool) :
    TM2.stepAux (pushN k n q) () S =
      TM2.stepAux q () (Function.update S k (List.replicate n true ++ S k)) := by
  induction n generalizing S with
  | zero =>
    show TM2.stepAux q () S = _
    rw [List.replicate_zero, List.nil_append, Function.update_eq_self]
  | succ n ih =>
    show TM2.stepAux (pushN k n q) () (Function.update S k (true :: S k)) = _
    rw [ih, Function.update_self, Function.update_idem, List.replicate_succ',
      List.append_assoc]
    rfl

theorem advance_some {L V : Type} (P : L → TM2.Stmt (fun _ : CS => Bool) L V) (l : L) (v : V)
    (S : CS → List Bool) :
    advance P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : CS => Bool) L V) = TM2.stepAux (P l) v S := rfl

def seedProgram : Unit → TM2.Stmt (fun _ : CS => Bool) Unit Unit := fun _ =>
  pushN (cell 5) 1 (pushN (cell 6) 2256 (pushN (cell 7) 10000 (pushN (cell 8) 12
    (pushN (cell 9) 1280 .halt))))

def seedVals (vals : Fin 22 → ℕ) : Fin 22 → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update vals 5 (1 + vals 5)) 6 (2256 + vals 6)) 7 (10000 + vals 7))
      8 (12 + vals 8)) 9 (1280 + vals 9)

theorem seed_stage (vals : Fin 22 → ℕ) :
    Runs seedProgram () () (U vals) (U (seedVals vals)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  rw [Function.iterate_one, advance_some]
  dsimp only [seedProgram]
  rw [pushN_stepAux, U_push, pushN_stepAux, U_push, pushN_stepAux, U_push,
    pushN_stepAux, U_push, pushN_stepAux, U_push]
  have e6 : Function.update vals 5 (1 + vals 5) 6 = vals 6 :=
    Function.update_of_ne (by decide) _ _
  have e7 : Function.update (Function.update vals 5 (1 + vals 5)) 6 (2256 + vals 6) 7 = vals 7 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  have e8 : Function.update (Function.update (Function.update vals 5 (1 + vals 5)) 6
      (2256 + vals 6)) 7 (10000 + vals 7) 8 = vals 8 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
  have e9 : Function.update (Function.update (Function.update (Function.update vals 5
      (1 + vals 5)) 6 (2256 + vals 6)) 7 (10000 + vals 7)) 8 (12 + vals 8) 9 = vals 9 := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  rw [e6, e7, e8, e9]
  rfl

/-! ## Multiplication (admitted `multiplyProgram`) -/

def emb6 (v : Fin 6 → Fin 22) (hv : Function.Injective v) : Fin 6 ↪ CS :=
  ⟨fun i => cell (v i), fun _ _ h => hv (cell_inj h)⟩

def mulP (v : Fin 6 → Fin 22) (hv : Function.Injective v) :=
  MatrixStage4ScalarPreparationOps.multiplyProgram (emb6 v hv)

theorem mul_stage (v : Fin 6 → Fin 22) (hv : Function.Injective v) (vals : Fin 22 → ℕ)
    (h2 : vals (v 2) = 0) (h3 : vals (v 3) = 0) (h4 : vals (v 4) = 0) :
    Runs (mulP v hv) .outer false (U vals)
      (U (Function.update vals (v 5) (vals (v 0) * vals (v 1) + vals (v 5))))
      (MatrixAddressMachine.exactTime (vals (v 0)) (vals (v 1)) 0) := by
  refine ⟨_, le_rfl, ?_⟩
  have h := MatrixStage4ScalarPreparationOps.multiply_run (emb6 v hv) (U vals)
    (vals (v 0)) (vals (v 1)) rfl rfl
    (by show List.replicate (vals (v 2)) true = []; rw [h2]; rfl)
    (by show List.replicate (vals (v 3)) true = []; rw [h3]; rfl)
    (by show List.replicate (vals (v 4)) true = []; rw [h4]; rfl)
  rw [show emb6 v hv 5 = cell (v 5) from rfl, U_push] at h
  exact h

/-! ## Clear of the temporaries 6..17 -/

def tmpCells (i : Fin 12) : CS := cell ⟨i.val + 6, by omega⟩

theorem tmpCells_inj : Function.Injective tmpCells := by
  intro a b h
  have h' := congrArg Fin.val (cell_inj h)
  exact Fin.ext (by simpa using h')

def clearP := WeightedRawWords.clearProgram tmpCells

def clearVals (vals : Fin 22 → ℕ) : Fin 22 → ℕ :=
  fun k => if 6 ≤ k.val ∧ k.val ≤ 17 then 0 else vals k

theorem cleared_U (vals : Fin 22 → ℕ) :
    BitMachineClearBank.cleared tmpCells (U vals) = U (clearVals vals) := by
  funext x
  unfold BitMachineClearBank.cleared
  rcases x with j | j
  · by_cases hj : 6 ≤ j.val ∧ j.val ≤ 17
    · have hex : ∃ i, tmpCells i = cell j :=
        ⟨⟨j.val - 6, by omega⟩, by
          show cell _ = cell j
          congr 1
          exact Fin.ext (by simp; omega)⟩
      rw [if_pos hex]
      show [] = List.replicate (clearVals vals j) true
      simp [clearVals, hj]
    · have hex : ¬ ∃ i, tmpCells i = cell j := by
        rintro ⟨i, hi⟩
        have := congrArg Fin.val (cell_inj hi)
        simp at this
        omega
      rw [if_neg hex]
      show List.replicate (vals j) true = List.replicate (clearVals vals j) true
      simp [clearVals, hj]
  · have hex : ¬ ∃ i, tmpCells i = (Sum.inr j : CS) := by
      rintro ⟨i, hi⟩
      cases hi
    rw [if_neg hex]
    rfl

theorem clear_stage (vals : Fin 22 → ℕ) :
    Runs clearP 0 ((), none) (U vals) (U (clearVals vals))
      ((∑ i : Fin 12, vals ⟨i.val + 6, by omega⟩) + 12 + 2) := by
  have h := WeightedRawWords.clear_run tmpCells tmpCells_inj (U vals)
  rw [cleared_U] at h
  have hs : (∑ i, (U vals (tmpCells i)).length) = ∑ i : Fin 12, vals ⟨i.val + 6, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [tmpCells, U_cell]
  refine ⟨_, ?_, h⟩
  rw [hs]

/-! ## Clog (admitted `ETHParameterScaleMachineLogCopy.program`), output copied, log region cleared -/

def logSource : LogStack := .inl 0

def logOut : LogStack :=
  ETHParameterScaleMachineLogCopy.logStack ETHParameterScaleMachineLogCopy.logMachine.output

theorem logOut_ne : logOut ≠ logSource := by
  simp [logOut, logSource, ETHParameterScaleMachineLogCopy.logStack]

def logSlots (src : Fin 22) : LogStack ↪ CS where
  toFun k := if k = logSource then cell src else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = logSource <;> by_cases hb : b = logSource <;>
      simp only [ha, hb, if_true, if_false] at h
    · exact ha.trans hb.symm
    · cases h
    · cases h
    · exact Sum.inr.inj h

def logProgram (src : Fin 22) :=
  fun l => stackStmt (logSlots src) (ETHParameterScaleMachineLogCopy.program l)

def logBound (m : ℕ) : ℕ :=
  2*m+2 + (UnaryBinaryEncoding.coefficient+6)*(m+1)^2

def logPer : ℕ := BitMachineStackGrowth.perStep ETHParameterScaleMachineLogCopy.program

theorem log_start_stk (q : List Bool) (k : LogStack) :
    (ETHParameterScaleMachineLogCopy.start q).stk k = if k = logSource then q else [] := by
  unfold ETHParameterScaleMachineLogCopy.start
  unfold BitMachineStackEmbedding.cfg
  unfold stackCfg
  dsimp only
  by_cases hr : ∃ i, ETHParameterScaleMachineLogCopy.copyStack i = k
  · obtain ⟨i, rfl⟩ := hr
    rw [bank_at]
    fin_cases i <;>
      simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg,
        BitMachineCopy.stackContents, BitMachineInline.cfg, logSource]
  · rw [bank_outside _ _ _ _ hr]
    have hk : k ≠ logSource := by
      rintro rfl
      exact hr ⟨0, rfl⟩
    simp [hk]

theorem log_embedded (src : Fin 22) (m : ℕ) (G : CS → List Bool)
    (hS : G (cell src) = List.replicate m true)
    (hL : ∀ k, G (.inr k) = []) :
    ∃ t ≤ logBound m, ∃ (v : ETHParameterScaleMachineLogCopy.Control) (F : LogStack → List Bool),
      ((advance (logProgram src))^[t])
        (⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none, G⟩ :
          TM2.Cfg (fun _ : CS => Bool) ETHParameterScaleMachineLogCopy.Label
            ETHParameterScaleMachineLogCopy.Control) =
        ⟨none, v, bank (logSlots src) G F⟩ ∧
      F logSource = List.replicate m true ∧
      F logOut = List.replicate (Nat.clog 2 m) true ∧
      ∀ k, (F k).length ≤ m + logPer * logBound m := by
  obtain ⟨t, c, ht, hr, hl, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run m
  have hr' : ((advance ETHParameterScaleMachineLogCopy.program)^[t])
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) =
      ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c := hr
  have hlabel : (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg,
      stackCfg, BitMachineInline.cfg, hl]
  refine ⟨t, ht, (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).var,
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk, ?_, ?_, ?_, ?_⟩
  · have h := WeightedRawWords.region_run (logSlots src) ETHParameterScaleMachineLogCopy.program
      _ _ t hr' G
      (by
        intro k
        rw [log_start_stk]
        by_cases hk : k = logSource
        · subst hk; simp [logSlots, hS]
        · simp [logSlots, hk, hL])
    rw [hlabel] at h
    exact h
  · exact ETHParameterScaleMachineLogCopy.afterLog_source m c
  · rw [logOut, ETHParameterScaleMachineLogCopy.afterLog_output]
    exact ho
  · intro k
    have hg := BitMachineStackGrowth.run_growth ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) t k
    rw [hr'] at hg
    have hi : ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length ≤ m := by
      rw [log_start_stk]; split <;> simp
    have hm : logPer * t ≤ logPer * logBound m := Nat.mul_le_mul_left _ ht
    have hg' : ((ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk k).length ≤
        ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length +
          logPer * t := hg
    omega

theorem cleared_update_comm' {K : Type} [DecidableEq K] {n : ℕ} (cells : Fin n → K)
    (S : K → List Bool) (a : K) (u : List Bool) (ha : ∀ i, cells i ≠ a) :
    BitMachineClearBank.cleared cells (Function.update S a u) =
      Function.update (BitMachineClearBank.cleared cells S) a u := by
  funext j
  by_cases hj : j = a
  · subst hj
    have : ¬ ∃ i, cells i = j := fun ⟨i, hi⟩ => ha i hi
    simp [BitMachineClearBank.cleared, this]
  · simp [BitMachineClearBank.cleared, Function.update_of_ne hj]

def logCells : Fin (Fintype.card LogStack) → CS :=
  fun i => .inr ((Fintype.equivFin LogStack).symm i)

theorem logCells_injective : Function.Injective logCells := by
  intro i j h
  exact (Fintype.equivFin LogStack).symm.injective (Sum.inr.inj h)

def logCard : ℕ := Fintype.card LogStack

/-- The copy of the log output onto cell `dst` (temporary: cell 21). -/
def copySlots (dst : Fin 22) (hd : dst ≠ 21) : Fin 3 ↪ CS :=
  ⟨![.inr logOut, cell dst, cell 21], by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | exact absurd (cell_inj h) hd
      | exact absurd (cell_inj h).symm hd
      | (exfalso; cases h; done)
      | (cases h; exact absurd rfl hd)⟩

def copyP (dst : Fin 22) (hd : dst ≠ 21) :=
  MatrixStage4ScalarPreparationOps.copyProgram (copySlots dst hd)

def logP (src dst : Fin 22) (hd : dst ≠ 21) :=
  BitMachineRawSequence.program (logProgram src)
    (BitMachineRawSequence.program (copyP dst hd) (WeightedRawWords.clearProgram logCells)
      0 none ((), none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) (none, ((), none))

def logStart : BitMachineRawSequence.Label ETHParameterScaleMachineLogCopy.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label (Fin (Fintype.card LogStack + 2))) :=
  BitMachineRawSequence.leftLabel (.inl .scan)

def logCtrl : ETHParameterScaleMachineLogCopy.Control × (Option Bool × (Unit × Option Bool)) :=
  (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none)))

def logStageBound (m : ℕ) : ℕ :=
  logBound m + ((2 * Nat.clog 2 m + 2) + (logCard * (m + logPer * logBound m) + logCard + 2) + 1) + 1

theorem sum_le_mul' {n : ℕ} (f : Fin n → ℕ) (B : ℕ) (h : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ n * B := by
  have := Finset.sum_le_card_nsmul Finset.univ f B (fun i _ => h i)
  simpa using this

theorem log_stage (src dst : Fin 22) (hsd : src ≠ dst) (hd : dst ≠ 21) (hs : src ≠ 21)
    (vals : Fin 22 → ℕ) (h21 : vals 21 = 0) :
    Runs (logP src dst hd) logStart logCtrl (U vals)
      (U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst)))
      (logStageBound (vals src)) := by
  obtain ⟨t1, ht1, v, F, hr1, hsrc, hout, hlen⟩ :=
    log_embedded src (vals src) (U vals) rfl (fun _ => rfl)
  set X := bank (logSlots src) (U vals) F with hX
  have hXo : X (.inr logOut) = List.replicate (Nat.clog 2 (vals src)) true := by
    have : (.inr logOut : CS) = logSlots src logOut := by
      simp [logSlots, logOut_ne]
    rw [this, hX, bank_at, hout]
  have hXcell : ∀ k : Fin 22, k ≠ src → X (cell k) = U vals (cell k) := by
    intro k hk
    apply bank_outside
    rintro ⟨j, hj⟩
    by_cases h : j = logSource
    · simp only [logSlots, Function.Embedding.coeFn_mk, h, if_true] at hj
      exact hk (cell_inj hj).symm
    · simp only [logSlots, Function.Embedding.coeFn_mk, h, if_false] at hj
      cases hj
  have hX21 : X (cell 21) = [] := by
    rw [hXcell 21 (fun e => hs e.symm), U_cell, h21, List.replicate_zero]
  have hc := MatrixStage4ScalarPreparationOps.copy_run (copySlots dst hd) X hX21
  have hc' : ((advance (copyP dst hd))^[2 * (Nat.clog 2 (vals src)) + 2])
      (⟨some .scan, none, X⟩ : TM2.Cfg (fun _ : CS => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update X (cell dst)
        (List.replicate (Nat.clog 2 (vals src)) true ++ U vals (cell dst))⟩ := by
    have e0 : copySlots dst hd 0 = .inr logOut := rfl
    have e1 : copySlots dst hd 1 = cell dst := rfl
    rw [e0, e1, hXo, List.length_replicate, hXcell dst (fun e => hsd e.symm)] at hc
    exact hc
  set X1 := Function.update X (cell dst)
    (List.replicate (Nat.clog 2 (vals src)) true ++ U vals (cell dst)) with hX1
  have hcl := WeightedRawWords.clear_run logCells logCells_injective X1
  have hsum : (∑ i, (X1 (logCells i)).length) ≤ logCard * (vals src + logPer * logBound (vals src)) := by
    apply sum_le_mul'
    intro i
    have hne : logCells i ≠ cell dst := by intro e; cases e
    rw [hX1, Function.update_of_ne hne, hX]
    by_cases hr : ∃ k, logSlots src k = logCells i
    · obtain ⟨k, hk⟩ := hr
      rw [← hk, bank_at]
      exact hlen k
    · rw [bank_outside (logSlots src) (U vals) F _ hr]
      simp [logCells, U_log]
  have hclearX : BitMachineClearBank.cleared logCells X = U vals := by
    funext j
    unfold BitMachineClearBank.cleared
    by_cases hc : ∃ i, logCells i = j
    · rw [if_pos hc]
      obtain ⟨i, rfl⟩ := hc
      rfl
    · rw [if_neg hc, hX]
      by_cases hr : ∃ k, logSlots src k = j
      · obtain ⟨k, rfl⟩ := hr
        rw [bank_at]
        by_cases hk : k = logSource
        · subst hk
          rw [hsrc]
          simp [logSlots, U_cell]
        · exfalso
          apply hc
          refine ⟨(Fintype.equivFin LogStack) k, ?_⟩
          simp [logCells, logSlots, hk]
      · exact bank_outside _ _ _ _ hr
  have hfinal : BitMachineClearBank.cleared logCells X1 =
      U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst)) := by
    have hn : ∀ i, logCells i ≠ cell dst := fun i e => by cases e
    rw [hX1, cleared_update_comm' logCells X (cell dst) _ hn, hclearX, U_push]
  rw [hfinal] at hcl
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs (copyP dst hd)
    (WeightedRawWords.clearProgram logCells)
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X X1
    (U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst))) _ _ hc' hcl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs (logProgram src) _
    (.inl .scan) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) v
    (none, ((), none)) (none, ((), none)) (U vals) X _ t1 t2 hr1 h2
  refine ⟨t, ?_, h⟩
  unfold logStageBound
  unfold logCard at hsum ⊢
  omega

#print axioms seed_stage
#print axioms mul_stage
#print axioms clear_stage
#print axioms log_embedded
#print axioms log_stage

end
end EthInapproximability.CurrentPaper.CostUpdateStages
