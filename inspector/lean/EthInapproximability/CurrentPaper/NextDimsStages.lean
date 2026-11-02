import EthInapproximability.CurrentPaper.CostUpdateStages
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Lane owner:b-weighted-level-7, unit 2, segment 2c, piece 1: the stages of the
level-`j+1` rows/columns recompute machine, on the local stack
`DS N = Fin N ⊕ LogStack`, GENERIC in the number `N` of unary cells.

This generalises owner-6's `CostUpdateStages` (fixed `Fin 22`) and adds three
stage kinds. Every stage boundary bank is `U vals` (cell `k : Fin N` holds unary
`vals k`, the log region is blank). Stages (all admitted production programs,
embedded; no value is inserted):
* `pushP k n`: one statement pushing the fixed constant `n` onto cell `k`;
* `popP k n`: one statement popping `n` symbols from cell `k` (truncated `-`);
* `copyP w`: admitted `copyProgram`, `w 1 += w 0` (temporary `w 2` blank);
* `mulP v`: admitted `multiplyProgram`, `v 5 += v 0 * v 1` (scratch `v 2..4` blank);
* `pow2P w`: admitted `unaryPowerProgram`, `w 0 := 2 ^ (w 3)` (`w 0..2` blank before);
* `wpowP w`: admitted `weightedPowerProgram`, `w 0 := (w 1) ^ (w 6)` (`w 0` unary one
  before, scratch `w 2..5` blank), the fuel `w 6` consumed;
* `logP src dst tmp`: admitted `ETHParameterScaleMachineLogCopy.program` reading `src`
  in place, charged copy of its output onto `dst`, charged clear of the log region;
* `clearP nKeep`: the charged clear of every cell of index `≥ nKeep`. -/

namespace EthInapproximability.CurrentPaper.NextDimsStages

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

abbrev LogStack := ETHParameterScaleMachineLogCopy.Stack
abbrev DS (N : ℕ) := Fin N ⊕ LogStack

variable {N : ℕ}

abbrev cell (k : Fin N) : DS N := .inl k

theorem cell_inj {a b : Fin N} (h : (cell a : DS N) = cell b) : a = b := Sum.inl.inj h

/-- The bank with unary `vals k` in cell `k` and a blank log region. -/
def U (vals : Fin N → ℕ) : DS N → List Bool :=
  Sum.elim (fun k => List.replicate (vals k) true) (fun _ => [])

theorem U_cell (vals : Fin N → ℕ) (k : Fin N) :
    U vals (cell k) = List.replicate (vals k) true := rfl
theorem U_log (vals : Fin N → ℕ) (k : LogStack) : U vals (.inr k) = [] := rfl

theorem U_set (vals : Fin N → ℕ) (k : Fin N) (m : ℕ) :
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

theorem U_push (vals : Fin N → ℕ) (k : Fin N) (m : ℕ) :
    Function.update (U vals) (cell k) (List.replicate m true ++ U vals (cell k)) =
      U (Function.update vals k (m + vals k)) := by
  rw [U_cell, ← List.replicate_add, U_set]

/-- A run from `⟨some l, v, S⟩` to `⟨none, v, T⟩` within `B` steps. -/
def Runs {L V : Type} (P : L → TM2.Stmt (fun _ : DS N => Bool) L V) (l : L) (v : V)
    (S T : DS N → List Bool) (B : ℕ) : Prop :=
  ∃ t ≤ B, ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : DS N => Bool) L V) = ⟨none, v, T⟩

theorem Runs.seq {LA LB VA VB : Type} {A : LA → TM2.Stmt (fun _ : DS N => Bool) LA VA}
    {B : LB → TM2.Stmt (fun _ : DS N => Bool) LB VB} {a₀ : LA} {b₀ : LB} {v₀ : VA} {w₀ : VB}
    {S T X : DS N → List Bool} {Ta Tb : ℕ}
    (ha : Runs A a₀ v₀ S T Ta) (hb : Runs B b₀ w₀ T X Tb) :
    Runs (BitMachineRawSequence.program A B b₀ v₀ w₀) (BitMachineRawSequence.leftLabel a₀)
      (v₀, w₀) S X (Ta + Tb + 1) := by
  obtain ⟨ta, hta, ra⟩ := ha
  obtain ⟨tb, htb, rb⟩ := hb
  obtain ⟨t, ht, r⟩ := BitMachineRawSequence.runs A B a₀ b₀ v₀ v₀ w₀ w₀ S T X ta tb ra rb
  exact ⟨t, by omega, r⟩

theorem Runs.mono {L V : Type} {P : L → TM2.Stmt (fun _ : DS N => Bool) L V} {l : L} {v : V}
    {S T : DS N → List Bool} {B B' : ℕ} (h : Runs P l v S T B) (hB : B ≤ B') :
    Runs P l v S T B' := by
  obtain ⟨t, ht, r⟩ := h
  exact ⟨t, le_trans ht hB, r⟩

theorem advance_some {L V : Type} (P : L → TM2.Stmt (fun _ : DS N => Bool) L V) (l : L) (v : V)
    (S : DS N → List Bool) :
    advance P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : DS N => Bool) L V) = TM2.stepAux (P l) v S := rfl

/-! ## Push / pop of a fixed number of symbols -/

def pushN (k : DS N) : ℕ → TM2.Stmt (fun _ : DS N => Bool) Unit Unit →
    TM2.Stmt (fun _ : DS N => Bool) Unit Unit
  | 0, q => q
  | n + 1, q => .push k (fun _ => true) (pushN k n q)

theorem pushN_stepAux (k : DS N) (n : ℕ) (q : TM2.Stmt (fun _ : DS N => Bool) Unit Unit)
    (S : DS N → List Bool) :
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

def popN (k : DS N) : ℕ → TM2.Stmt (fun _ : DS N => Bool) Unit Unit →
    TM2.Stmt (fun _ : DS N => Bool) Unit Unit
  | 0, q => q
  | n + 1, q => .pop k (fun _ _ => ()) (popN k n q)

theorem popN_stepAux (k : DS N) (n : ℕ) (q : TM2.Stmt (fun _ : DS N => Bool) Unit Unit)
    (S : DS N → List Bool) :
    TM2.stepAux (popN k n q) () S =
      TM2.stepAux q () (Function.update S k ((S k).drop n)) := by
  induction n generalizing S with
  | zero =>
    show TM2.stepAux q () S = _
    rw [List.drop_zero, Function.update_eq_self]
  | succ n ih =>
    show TM2.stepAux (popN k n q) () (Function.update S k (S k).tail) = _
    rw [ih, Function.update_self, Function.update_idem]
    have e : List.drop n (S k).tail = List.drop (n + 1) (S k) := by
      rcases S k with _ | ⟨a, t⟩ <;> simp
    rw [e]

def pushP (k : Fin N) (n : ℕ) : Unit → TM2.Stmt (fun _ : DS N => Bool) Unit Unit :=
  fun _ => pushN (cell k) n .halt

theorem push_stage (k : Fin N) (n : ℕ) (vals : Fin N → ℕ) :
    Runs (pushP k n) () () (U vals) (U (Function.update vals k (n + vals k))) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  rw [Function.iterate_one, advance_some]
  dsimp only [pushP]
  rw [pushN_stepAux, U_push]
  rfl

def popP (k : Fin N) (n : ℕ) : Unit → TM2.Stmt (fun _ : DS N => Bool) Unit Unit :=
  fun _ => popN (cell k) n .halt

theorem pop_stage (k : Fin N) (n : ℕ) (vals : Fin N → ℕ) :
    Runs (popP k n) () () (U vals) (U (Function.update vals k (vals k - n))) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  rw [Function.iterate_one, advance_some]
  dsimp only [popP]
  rw [popN_stepAux, U_cell, List.drop_replicate, U_set]
  rfl

/-! ## Copy (admitted `copyProgram`) -/

def emb3 (w : Fin 3 → Fin N) (hw : Function.Injective w) : Fin 3 ↪ DS N :=
  ⟨fun i => cell (w i), fun _ _ h => hw (cell_inj h)⟩

def copyP (w : Fin 3 → Fin N) (hw : Function.Injective w) :=
  MatrixStage4ScalarPreparationOps.copyProgram (emb3 w hw)

theorem copy_stage (w : Fin 3 → Fin N) (hw : Function.Injective w) (vals : Fin N → ℕ)
    (h2 : vals (w 2) = 0) :
    Runs (copyP w hw) BitMachineCopy.Label.scan none (U vals)
      (U (Function.update vals (w 1) (vals (w 0) + vals (w 1)))) (2 * vals (w 0) + 2) := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (emb3 w hw) (U vals)
    (by show List.replicate (vals (w 2)) true = []; rw [h2]; rfl)
  have e0 : emb3 w hw 0 = cell (w 0) := rfl
  have e1 : emb3 w hw 1 = cell (w 1) := rfl
  rw [e0, e1, U_cell, U_cell, List.length_replicate, ← List.replicate_add, U_set] at h
  exact ⟨_, le_rfl, h⟩

/-! ## Multiplication (admitted `multiplyProgram`) -/

def emb6 (v : Fin 6 → Fin N) (hv : Function.Injective v) : Fin 6 ↪ DS N :=
  ⟨fun i => cell (v i), fun _ _ h => hv (cell_inj h)⟩

def mulP (v : Fin 6 → Fin N) (hv : Function.Injective v) :=
  MatrixStage4ScalarPreparationOps.multiplyProgram (emb6 v hv)

theorem mul_stage (v : Fin 6 → Fin N) (hv : Function.Injective v) (vals : Fin N → ℕ)
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

/-! ## Power of two (admitted `unaryPowerProgram`) -/

def idx4 : MatrixUnaryPower.Stack → Fin 4 := Sum.elim (fun i => i.castSucc) (fun _ => 3)

theorem idx4_inj : Function.Injective idx4 := by decide

def emb4 (w : Fin 4 → Fin N) (hw : Function.Injective w) : MatrixUnaryPower.Stack ↪ DS N :=
  ⟨fun x => cell (w (idx4 x)), fun _ _ h => idx4_inj (hw (cell_inj h))⟩

def pow2P (w : Fin 4 → Fin N) (hw : Function.Injective w) :=
  MatrixStage4ScalarPreparationOps.unaryPowerProgram (emb4 w hw)

theorem pow2_stage (w : Fin 4 → Fin N) (hw : Function.Injective w) (vals : Fin N → ℕ)
    (h0 : vals (w 0) = 0) (h1 : vals (w 1) = 0) (h2 : vals (w 2) = 0) :
    Runs (pow2P w hw) (.inr false) ((false, false), none) (U vals)
      (U (Function.update vals (w 0) (2 ^ vals (w 3))))
      (4 * 2 ^ vals (w 3) + 5 * vals (w 3) + 7) := by
  obtain ⟨t, ht, h⟩ := MatrixStage4ScalarPreparationOps.unary_power_run (emb4 w hw) (U vals)
    (vals (w 3)) rfl
    (by show List.replicate (vals (w 0)) true = []; rw [h0]; rfl)
    (by show List.replicate (vals (w 1)) true = []; rw [h1]; rfl)
    (by show List.replicate (vals (w 2)) true = []; rw [h2]; rfl)
  rw [show emb4 w hw (.inl 0) = cell (w 0) from rfl, U_set] at h
  exact ⟨t, ht, h⟩

/-! ## Weighted power (admitted `weightedPowerProgram`) -/

def idx7 : MatrixWeightedPower.Stack → Fin 7 := Sum.elim (fun i => i.castSucc) (fun _ => 6)

theorem idx7_inj : Function.Injective idx7 := by decide

def emb7 (w : Fin 7 → Fin N) (hw : Function.Injective w) : MatrixWeightedPower.Stack ↪ DS N :=
  ⟨fun x => cell (w (idx7 x)), fun _ _ h => idx7_inj (hw (cell_inj h))⟩

def wpowP (w : Fin 7 → Fin N) (hw : Function.Injective w) :=
  MatrixStage4ScalarPreparationOps.weightedPowerProgram (emb7 w hw)

theorem wpow_stage (w : Fin 7 → Fin N) (hw : Function.Injective w) (vals : Fin N → ℕ)
    (h0 : vals (w 0) = 1) (h2 : vals (w 2) = 0) (h3 : vals (w 3) = 0)
    (h4 : vals (w 4) = 0) (h5 : vals (w 5) = 0) :
    Runs (wpowP w hw) (.inr .test) (false, false) (U vals)
      (U (Function.update (Function.update vals (w 0) (vals (w 1) ^ vals (w 6))) (w 6) 0))
      (MatrixWeightedPower.powerBound (vals (w 1)) (vals (w 6))) := by
  obtain ⟨t, ht, h⟩ := MatrixStage4ScalarPreparationOps.weighted_power_run (emb7 w hw) (U vals)
    (vals (w 1)) (vals (w 6))
    (by show List.replicate (vals (w 0)) true = [true]; rw [h0]; rfl) rfl
    (by show List.replicate (vals (w 2)) true = []; rw [h2]; rfl)
    (by show List.replicate (vals (w 3)) true = []; rw [h3]; rfl)
    (by show List.replicate (vals (w 4)) true = []; rw [h4]; rfl)
    (by show List.replicate (vals (w 5)) true = []; rw [h5]; rfl) rfl
  rw [show emb7 w hw (.inl 0) = cell (w 0) from rfl, U_set,
    show emb7 w hw (.inr 0) = cell (w 6) from rfl,
    show ([] : List Bool) = List.replicate 0 true from rfl, U_set] at h
  exact ⟨t, ht, h⟩

/-! ## Clear of every cell of index `≥ nKeep` -/

def clearCells (nKeep : ℕ) (hk : nKeep ≤ N) : Fin (N - nKeep) → DS N :=
  fun i => cell ⟨nKeep + i.val, by omega⟩

theorem clearCells_inj (nKeep : ℕ) (hk : nKeep ≤ N) : Function.Injective (clearCells nKeep hk) := by
  intro a b h
  have h' := congrArg Fin.val (cell_inj h)
  exact Fin.ext (by simpa using h')

def clearP (nKeep : ℕ) (hk : nKeep ≤ N) := WeightedRawWords.clearProgram (clearCells nKeep hk)

def clearVals (nKeep : ℕ) (vals : Fin N → ℕ) : Fin N → ℕ :=
  fun k => if nKeep ≤ k.val then 0 else vals k

theorem cleared_U (nKeep : ℕ) (hk : nKeep ≤ N) (vals : Fin N → ℕ) :
    BitMachineClearBank.cleared (clearCells nKeep hk) (U vals) = U (clearVals nKeep vals) := by
  funext x
  unfold BitMachineClearBank.cleared
  rcases x with j | j
  · by_cases hj : nKeep ≤ j.val
    · have hex : ∃ i, clearCells nKeep hk i = cell j :=
        ⟨⟨j.val - nKeep, by omega⟩, by
          show cell _ = cell j
          congr 1
          exact Fin.ext (by simp; omega)⟩
      rw [if_pos hex]
      show [] = List.replicate (clearVals nKeep vals j) true
      simp [clearVals, hj]
    · have hex : ¬ ∃ i, clearCells nKeep hk i = cell j := by
        rintro ⟨i, hi⟩
        have := congrArg Fin.val (cell_inj hi)
        simp at this
        omega
      rw [if_neg hex]
      show List.replicate (vals j) true = List.replicate (clearVals nKeep vals j) true
      simp [clearVals, hj]
  · have hex : ¬ ∃ i, clearCells nKeep hk i = (Sum.inr j : DS N) := by
      rintro ⟨i, hi⟩
      cases hi
    rw [if_neg hex]
    rfl

theorem clear_stage (nKeep : ℕ) (hk : nKeep ≤ N) (vals : Fin N → ℕ) :
    Runs (clearP nKeep hk) 0 ((), none) (U vals) (U (clearVals nKeep vals))
      ((∑ i : Fin (N - nKeep), vals ⟨nKeep + i.val, by omega⟩) + (N - nKeep) + 2) := by
  have h := WeightedRawWords.clear_run (clearCells nKeep hk) (clearCells_inj nKeep hk) (U vals)
  rw [cleared_U] at h
  have hs : (∑ i, (U vals (clearCells nKeep hk i)).length) =
      ∑ i : Fin (N - nKeep), vals ⟨nKeep + i.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [clearCells, U_cell]
  refine ⟨_, ?_, h⟩
  rw [hs]

/-! ## Clog (admitted `ETHParameterScaleMachineLogCopy.program`), output copied onto `dst`
(temporary `tmp`), log region cleared -/

def logSlots (src : Fin N) : LogStack ↪ DS N where
  toFun k := if k = CostUpdateStages.logSource then cell src else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = CostUpdateStages.logSource <;> by_cases hb : b = CostUpdateStages.logSource <;>
      simp only [ha, hb, if_true, if_false] at h
    · exact ha.trans hb.symm
    · cases h
    · cases h
    · exact Sum.inr.inj h

def logProgram (src : Fin N) :=
  fun l => stackStmt (logSlots src) (ETHParameterScaleMachineLogCopy.program l)

theorem log_embedded (src : Fin N) (m : ℕ) (G : DS N → List Bool)
    (hS : G (cell src) = List.replicate m true)
    (hL : ∀ k, G (.inr k) = []) :
    ∃ t ≤ CostUpdateStages.logBound m, ∃ (v : ETHParameterScaleMachineLogCopy.Control)
      (F : LogStack → List Bool),
      ((advance (logProgram src))^[t])
        (⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none, G⟩ :
          TM2.Cfg (fun _ : DS N => Bool) ETHParameterScaleMachineLogCopy.Label
            ETHParameterScaleMachineLogCopy.Control) =
        ⟨none, v, bank (logSlots src) G F⟩ ∧
      F CostUpdateStages.logSource = List.replicate m true ∧
      F CostUpdateStages.logOut = List.replicate (Nat.clog 2 m) true ∧
      ∀ k, (F k).length ≤ m + CostUpdateStages.logPer * CostUpdateStages.logBound m := by
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
        rw [CostUpdateStages.log_start_stk]
        by_cases hk : k = CostUpdateStages.logSource
        · subst hk; simp [logSlots, hS]
        · simp [logSlots, hk, hL])
    rw [hlabel] at h
    exact h
  · exact ETHParameterScaleMachineLogCopy.afterLog_source m c
  · rw [CostUpdateStages.logOut, ETHParameterScaleMachineLogCopy.afterLog_output]
    exact ho
  · intro k
    have hg := BitMachineStackGrowth.run_growth ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) t k
    rw [hr'] at hg
    have hi : ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length ≤ m := by
      rw [CostUpdateStages.log_start_stk]; split <;> simp
    have hm : CostUpdateStages.logPer * t ≤ CostUpdateStages.logPer * CostUpdateStages.logBound m :=
      Nat.mul_le_mul_left _ ht
    have hg' : ((ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk k).length ≤
        ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length +
          CostUpdateStages.logPer * t := hg
    unfold CostUpdateStages.logPer at hm ⊢
    omega

def logCells : Fin (Fintype.card LogStack) → DS N :=
  fun i => .inr ((Fintype.equivFin LogStack).symm i)

theorem logCells_injective : Function.Injective (logCells (N := N)) := by
  intro i j h
  exact (Fintype.equivFin LogStack).symm.injective (Sum.inr.inj h)

def copySlotsL (dst tmp : Fin N) (hd : dst ≠ tmp) : Fin 3 ↪ DS N :=
  ⟨![.inr CostUpdateStages.logOut, cell dst, cell tmp], by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | exact absurd (cell_inj h) hd
      | exact absurd (cell_inj h).symm hd
      | (exfalso; cases h)⟩

def copyLP (dst tmp : Fin N) (hd : dst ≠ tmp) :=
  MatrixStage4ScalarPreparationOps.copyProgram (copySlotsL dst tmp hd)

def logP (src dst tmp : Fin N) (hd : dst ≠ tmp) :=
  BitMachineRawSequence.program (logProgram src)
    (BitMachineRawSequence.program (copyLP dst tmp hd) (WeightedRawWords.clearProgram (logCells (N := N)))
      0 none ((), none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) (none, ((), none))

theorem log_stage (src dst tmp : Fin N) (hsd : src ≠ dst) (hd : dst ≠ tmp) (hs : src ≠ tmp)
    (vals : Fin N → ℕ) (htmp : vals tmp = 0) :
    Runs (logP src dst tmp hd) CostUpdateStages.logStart CostUpdateStages.logCtrl (U vals)
      (U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst)))
      (CostUpdateStages.logStageBound (vals src)) := by
  obtain ⟨t1, ht1, v, F, hr1, hsrc, hout, hlen⟩ :=
    log_embedded src (vals src) (U vals) rfl (fun _ => rfl)
  set X := bank (logSlots src) (U vals) F with hX
  have hXo : X (.inr CostUpdateStages.logOut) = List.replicate (Nat.clog 2 (vals src)) true := by
    have : (.inr CostUpdateStages.logOut : DS N) = logSlots src CostUpdateStages.logOut := by
      simp [logSlots, CostUpdateStages.logOut_ne]
    rw [this, hX, bank_at, hout]
  have hXcell : ∀ k : Fin N, k ≠ src → X (cell k) = U vals (cell k) := by
    intro k hk
    apply bank_outside
    rintro ⟨j, hj⟩
    by_cases h : j = CostUpdateStages.logSource
    · simp only [logSlots, Function.Embedding.coeFn_mk, h, if_true] at hj
      exact hk (cell_inj hj).symm
    · simp only [logSlots, Function.Embedding.coeFn_mk, h, if_false] at hj
      cases hj
  have hXt : X (cell tmp) = [] := by
    rw [hXcell tmp (fun e => hs e.symm), U_cell, htmp, List.replicate_zero]
  have hc := MatrixStage4ScalarPreparationOps.copy_run (copySlotsL dst tmp hd) X hXt
  have hc' : ((advance (copyLP dst tmp hd))^[2 * (Nat.clog 2 (vals src)) + 2])
      (⟨some .scan, none, X⟩ : TM2.Cfg (fun _ : DS N => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update X (cell dst)
        (List.replicate (Nat.clog 2 (vals src)) true ++ U vals (cell dst))⟩ := by
    have e0 : copySlotsL dst tmp hd 0 = .inr CostUpdateStages.logOut := rfl
    have e1 : copySlotsL dst tmp hd 1 = cell dst := rfl
    rw [e0, e1, hXo, List.length_replicate, hXcell dst (fun e => hsd e.symm)] at hc
    exact hc
  set X1 := Function.update X (cell dst)
    (List.replicate (Nat.clog 2 (vals src)) true ++ U vals (cell dst)) with hX1
  have hcl := WeightedRawWords.clear_run (logCells (N := N)) logCells_injective X1
  have hsum : (∑ i, (X1 (logCells i)).length) ≤
      CostUpdateStages.logCard * (vals src + CostUpdateStages.logPer * CostUpdateStages.logBound (vals src)) := by
    apply CostUpdateStages.sum_le_mul'
    intro i
    have hne : (logCells i : DS N) ≠ cell dst := by intro e; cases e
    rw [hX1, Function.update_of_ne hne, hX]
    by_cases hr : ∃ k, logSlots src k = logCells i
    · obtain ⟨k, hk⟩ := hr
      rw [← hk, bank_at]
      exact hlen k
    · rw [bank_outside (logSlots src) (U vals) F _ hr]
      simp [logCells, U_log]
  have hclearX : BitMachineClearBank.cleared (logCells (N := N)) X = U vals := by
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
        by_cases hk : k = CostUpdateStages.logSource
        · subst hk
          rw [hsrc]
          simp [logSlots, U_cell]
        · exfalso
          apply hc
          refine ⟨(Fintype.equivFin LogStack) k, ?_⟩
          simp [logCells, logSlots, hk]
      · exact bank_outside _ _ _ _ hr
  have hfinal : BitMachineClearBank.cleared (logCells (N := N)) X1 =
      U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst)) := by
    have hn : ∀ i, (logCells i : DS N) ≠ cell dst := fun i e => by cases e
    rw [hX1, CostUpdateStages.cleared_update_comm' logCells X (cell dst) _ hn, hclearX, U_push]
  rw [hfinal] at hcl
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs (copyLP dst tmp hd)
    (WeightedRawWords.clearProgram (logCells (N := N)))
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X X1
    (U (Function.update vals dst (Nat.clog 2 (vals src) + vals dst))) _ _ hc' hcl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs (logProgram src) _
    (.inl .scan) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) v
    (none, ((), none)) (none, ((), none)) (U vals) X _ t1 t2 hr1 h2
  refine ⟨t, ?_, h⟩
  unfold CostUpdateStages.logStageBound
  unfold CostUpdateStages.logCard at hsum ⊢
  have hcard : Fintype.card LogStack = Fintype.card CostUpdateStages.LogStack := rfl
  omega

#print axioms push_stage
#print axioms pop_stage
#print axioms copy_stage
#print axioms mul_stage
#print axioms pow2_stage
#print axioms wpow_stage
#print axioms clear_stage
#print axioms log_embedded
#print axioms log_stage

end
end EthInapproximability.CurrentPaper.NextDimsStages
