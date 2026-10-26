import EthInapproximability.CurrentPaper.SourceCSPEntryBound

namespace EthInapproximability.CurrentPaper.SourceCSPEntryWrapper

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.SourceCSPEntryBound
open scoped Classical

abbrev Ambient (q : Nat) := SourceCSPFirstSlotBridge.Stack q ⊕ Fin 4

def firstEmbedding {q : Nat} :
    SourceCSPFirstRowController.Stack q ↪ Ambient q where
  toFun
    | .inl g => .inl (.inl g)
    | .inr k => .inl (.inr (.inl k))
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

def laterEmbedding {q : Nat} : SourceCSPFirstSlotBridge.Stack q ↪ Ambient q :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl.inj h⟩

def stash {q : Nat} (i : Fin 4) : Ambient q := .inr i

def prefixTarget {q : Nat} : Fin 3 → Ambient q
  | 0 => firstEmbedding (.inr SourceClauseRowWriterCleanup.savedCell)
  | 1 => firstEmbedding (.inr SourceClauseRowWriterCleanup.outputCell)
  | 2 => firstEmbedding (.inr SourceClauseRowWriterCleanup.countCell)

def foreign (q : Nat) (saved output count : List Bool) :
    Ambient q → List Bool
  | .inl _ => []
  | .inr 0 => saved
  | .inr 1 => output
  | .inr 2 => count
  | .inr 3 => []

noncomputable def initial (q : Nat) (input saved output count : List Bool) :
    TM2.Cfg (fun _ : Ambient q => Bool)
      (SourceCSPFirstRowController.Label 2 q)
      (SourceCSPFirstRowController.Control 2 q) :=
  stackCfg firstEmbedding (foreign q saved output count)
    (SourceCSPFirstRowController.initial 2 q input)

def firstProgram (q : Nat) :=
  fun l => stackStmt (firstEmbedding (q := q))
    (SourceCSPFirstRowController.program 2 q l)

theorem first_run (q : Nat) (input saved output count : List Bool)
    (t : Nat) (v : SourceCSPFirstRowController.Control 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (hrun : ((advance (SourceCSPFirstRowController.program 2 q))^[t])
      (SourceCSPFirstRowController.initial 2 q input) =
        ⟨none, v, U⟩) :
    ((advance (firstProgram q))^[t])
      (initial q input saved output count) =
        ⟨none, v,
          bank firstEmbedding (foreign q saved output count) U⟩ := by
  have h := BitMachineStackRun.run firstEmbedding
    (foreign q saved output count)
    (SourceCSPFirstRowController.program 2 q)
    (SourceCSPFirstRowController.initial 2 q input) t
  rw [hrun] at h
  exact h

def targetEmbedding {q : Nat} : Fin 3 ↪ Ambient q where
  toFun := prefixTarget
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [prefixTarget, firstEmbedding,
        SourceClauseRowWriterCleanup.savedCell,
        SourceClauseRowWriterCleanup.outputCell,
        SourceClauseRowWriterCleanup.countCell]

def clearProgram (q : Nat) : Fin 5 →
    TM2.Stmt (fun _ : Ambient q => Bool) (Fin 5) (Unit × Option Bool)
  | 0 => BitMachineClearBank.clearStep (prefixTarget 0) 0 1
  | 1 => BitMachineClearBank.clearStep (prefixTarget 1) 1 2
  | 2 => BitMachineClearBank.clearStep (prefixTarget 2) 2 3
  | 3 => BitMachineClearBank.finishStep id 4
  | 4 => halt

def clearTime {q : Nat} (B : Ambient q → List Bool) : Nat :=
  (∑ i : Fin 3, (B (prefixTarget i)).length) + 5

theorem clear_run (q : Nat) (B : Ambient q → List Bool) :
    ((advance (clearProgram q))^[clearTime B])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool)
          (Fin 5) (Unit × Option Bool)) =
      ⟨none, ((), none),
        BitMachineClearBank.cleared prefixTarget B⟩ := by
  have hs := BitMachineClearBank.clear_bank_run
    (clearProgram q) id 4 3 (prefixTarget (q := q))
    targetEmbedding.injective
    (fun i : Fin 4 => i.castSucc)
    (by intro i; fin_cases i <;> rfl)
    (by rfl) () B
  change ((advance (clearProgram q))^[
    (∑ i : Fin 3, (B (prefixTarget i)).length) + 3 + 1])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool)
          (Fin 5) (Unit × Option Bool)) =
      ⟨some 4, ((), none),
        BitMachineClearBank.cleared prefixTarget B⟩ at hs
  change ((advance (clearProgram q))^[
      (∑ i : Fin 3, (B (prefixTarget i)).length) + 5])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool)
          (Fin 5) (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared prefixTarget B⟩
  rw [show (∑ i : Fin 3, (B (prefixTarget i)).length) + 5 =
    ((∑ i : Fin 3, (B (prefixTarget i)).length) + 3 + 1) + 1 by omega,
    Function.iterate_succ_apply', hs]
  rfl

def copySlots {q : Nat} (i : Fin 3) : Fin 3 ↪ Ambient q where
  toFun
    | 0 => stash i.castSucc
    | 1 => prefixTarget i
    | 2 => stash 3
  inj' := by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [stash, prefixTarget, firstEmbedding]

def copyProgram {q : Nat} (i : Fin 3) : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Ambient q => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => stackStmt (copySlots (q := q) i) (BitMachineCopy.program l)

theorem copy_run {q : Nat} (i : Fin 3)
    (B : Ambient q → List Bool)
    (htarget : B (prefixTarget i) = [])
    (hscratch : B (stash 3) = []) :
    ((advance (copyProgram i))^[2 * (B (stash i.castSucc)).length + 2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update B (prefixTarget i) (B (stash i.castSucc))⟩ := by
  let word := B (stash i.castSucc)
  let C := BitMachineCopy.cfg (some .scan) none word [] []
  have hbank : bank (copySlots i) B C.stk = B := by
    apply bank_eq_self
    intro k
    fin_cases k
    · rfl
    · exact htarget.symm
    · exact hscratch.symm
  have hc : ((advance BitMachineCopy.program)^[2 * word.length + 2]) C =
      BitMachineCopy.cfg none none word word [] := by
    simpa [C, BitMachineCopy.run] using
      BitMachineCopy.run_correct none word []
  have he := BitMachineStackRun.run (copySlots i) B
    BitMachineCopy.program C (2 * word.length + 2)
  rw [hc] at he
  have hf : (BitMachineCopy.cfg none none word word []).stk =
      Function.update C.stk 1 word := by
    funext k
    fin_cases k <;> rfl
  simp only [stackCfg, hf, bank_update, hbank] at he
  simpa only [copyProgram, word, copySlots] using he

theorem cleared_target {q : Nat} (B : Ambient q → List Bool)
    (i : Fin 3) :
    BitMachineClearBank.cleared prefixTarget B (prefixTarget i) = [] := by
  have h : ∃ k : Fin 3, prefixTarget (q := q) k = prefixTarget i :=
    ⟨i, rfl⟩
  simp [BitMachineClearBank.cleared, h]

theorem target_ne_stash {q : Nat} (i : Fin 3) (j : Fin 4) :
    prefixTarget (q := q) i ≠ stash j := by
  cases i using Fin.cases with
  | zero => simp [prefixTarget, stash, firstEmbedding]
  | succ i =>
      cases i using Fin.cases with
      | zero => simp [prefixTarget, stash, firstEmbedding]
      | succ i => fin_cases i; simp [prefixTarget, stash, firstEmbedding]

theorem cleared_stash {q : Nat} (B : Ambient q → List Bool)
    (j : Fin 4) :
    BitMachineClearBank.cleared prefixTarget B (stash j) = B (stash j) := by
  have hne : ¬ ∃ i : Fin 3, prefixTarget (q := q) i = stash j := by
    rintro ⟨i, hi⟩
    exact target_ne_stash i j hi
  simp [BitMachineClearBank.cleared, hne]

def copy01Program (q : Nat) :=
  BitMachineRawSequence.program (copyProgram (q := q) 0)
    (copyProgram (q := q) 1) .scan none none

def copy012Program (q : Nat) :=
  BitMachineRawSequence.program (copy01Program q)
    (copyProgram (q := q) 2) .scan (none, none) none

def prefixProgram (q : Nat) :=
  BitMachineRawSequence.program (clearProgram q)
    (copy012Program q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((), none) ((none, none), none)

noncomputable def prefixResult {q : Nat} (B : Ambient q → List Bool) :
    Ambient q → List Bool :=
  let B0 := BitMachineClearBank.cleared prefixTarget B
  let B1 := Function.update B0 (prefixTarget 0) (B0 (stash 0))
  let B2 := Function.update B1 (prefixTarget 1) (B1 (stash 1))
  Function.update B2 (prefixTarget 2) (B2 (stash 2))

def prefixTime {q : Nat} (B : Ambient q → List Bool) : Nat :=
  clearTime B +
    (2 * (B (stash 0)).length + 2) +
    (2 * (B (stash 1)).length + 2) +
    (2 * (B (stash 2)).length + 2) + 3

theorem target_ne_target {q : Nat} {i j : Fin 3} (h : i ≠ j) :
    prefixTarget (q := q) i ≠ prefixTarget j := by
  exact fun he => h (targetEmbedding.injective he)

theorem prefix_run {q : Nat} (B : Ambient q → List Bool)
    (hscratch : B (stash 3) = []) :
    ∃ t ≤ prefixTime B,
      ((advance (prefixProgram q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel 0),
          (((), none), ((none, none), none)), B⟩ :
          TM2.Cfg (fun _ : Ambient q => Bool)
            _ _) =
        ⟨none, (((), none), ((none, none), none)), prefixResult B⟩ := by
  let B0 := BitMachineClearBank.cleared prefixTarget B
  let B1 := Function.update B0 (prefixTarget 0) (B0 (stash 0))
  let B2 := Function.update B1 (prefixTarget 1) (B1 (stash 1))
  let B3 := Function.update B2 (prefixTarget 2) (B2 (stash 2))
  have hc := clear_run q B
  have hs0 : B0 (stash 3) = [] :=
    (cleared_stash B 3).trans hscratch
  have ht0 : B0 (prefixTarget 0) = [] := cleared_target B 0
  have h0 := copy_run (0 : Fin 3) B0 ht0 hs0
  have ht1 : B1 (prefixTarget 1) = [] := by
    simpa only [B1, Function.update_of_ne
      (target_ne_target (q := q) (by decide : (1 : Fin 3) ≠ 0))]
      using cleared_target B 1
  have hs1 : B1 (stash 3) = [] := by
    simpa only [B1, Function.update_of_ne
      (target_ne_stash (q := q) 0 3).symm] using hs0
  have h1 := copy_run (1 : Fin 3) B1 ht1 hs1
  have ht2 : B2 (prefixTarget 2) = [] := by
    have hne12 : prefixTarget (q := q) 2 ≠ prefixTarget 1 :=
      target_ne_target (q := q) (by decide : (2 : Fin 3) ≠ 1)
    have hne02 : prefixTarget (q := q) 2 ≠ prefixTarget 0 :=
      target_ne_target (q := q) (by decide : (2 : Fin 3) ≠ 0)
    simp only [B2, B1, Function.update_of_ne hne12,
      Function.update_of_ne hne02]
    exact cleared_target B 2
  have hs2 : B2 (stash 3) = [] := by
    simp only [B2, B1,
      Function.update_of_ne (target_ne_stash (q := q) 1 3).symm,
      Function.update_of_ne (target_ne_stash (q := q) 0 3).symm]
    exact hs0
  have h2 := copy_run (2 : Fin 3) B2 ht2 hs2
  obtain ⟨t01, ht01, h01⟩ := BitMachineRawSequence.runs
    (copyProgram (q := q) 0) (copyProgram (q := q) 1)
    .scan .scan none none none none B0 B1 B2
    (2 * (B0 (stash 0)).length + 2)
    (2 * (B1 (stash 1)).length + 2) h0 h1
  obtain ⟨t012, ht012, h012⟩ := BitMachineRawSequence.runs
    (copy01Program q) (copyProgram (q := q) 2)
    (BitMachineRawSequence.leftLabel .scan) .scan
    (none, none) (none, none) none none B0 B2 B3
    t01 (2 * (B2 (stash 2)).length + 2) h01 h2
  obtain ⟨tp, htp, hp⟩ := BitMachineRawSequence.runs
    (clearProgram q) (copy012Program q)
    0 (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((), none) ((), none) ((none, none), none)
    ((none, none), none) B B0 B3
    (clearTime B) t012 hc h012
  have hstash0 : B0 (stash 0) = B (stash 0) := cleared_stash B 0
  have hstash1 : B1 (stash 1) = B (stash 1) := by
    simpa only [B1, Function.update_of_ne
      (target_ne_stash (q := q) 0 1).symm] using cleared_stash B 1
  have hstash2 : B2 (stash 2) = B (stash 2) := by
    simp only [B2, B1,
      Function.update_of_ne (target_ne_stash (q := q) 1 2).symm,
      Function.update_of_ne (target_ne_stash (q := q) 0 2).symm]
    exact cleared_stash B 2
  refine ⟨tp, ?_, ?_⟩
  · dsimp [prefixTime]
    rw [← hstash0, ← hstash1, ← hstash2]
    omega
  · exact hp

theorem cleared_other {q : Nat} (B : Ambient q → List Bool)
    (x : Ambient q)
    (h0 : x ≠ prefixTarget 0)
    (h1 : x ≠ prefixTarget 1)
    (h2 : x ≠ prefixTarget 2) :
    BitMachineClearBank.cleared prefixTarget B x = B x := by
  have hne : ¬ ∃ i : Fin 3, prefixTarget (q := q) i = x := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact h0 hi.symm
    · exact h1 hi.symm
    · exact h2 hi.symm
  simp [BitMachineClearBank.cleared, hne]

theorem prefix_result_value {q : Nat} (B : Ambient q → List Bool)
    (x : Ambient q) :
    prefixResult B x =
      if x = prefixTarget 2 then B (stash 2)
      else if x = prefixTarget 1 then B (stash 1)
      else if x = prefixTarget 0 then B (stash 0)
      else B x := by
  by_cases h2 : x = prefixTarget (q := q) 2
  · subst x
    simp [prefixResult, Function.update_self,
      Function.update_of_ne (target_ne_stash (q := q) 0 2).symm,
      Function.update_of_ne (target_ne_stash (q := q) 1 2).symm,
      cleared_stash]
  by_cases h1 : x = prefixTarget (q := q) 1
  · subst x
    simp [prefixResult, h2, Function.update_self,
      Function.update_of_ne (target_ne_stash (q := q) 0 1).symm,
      cleared_stash]
  by_cases h0 : x = prefixTarget (q := q) 0
  · subst x
    simp [prefixResult, h2, h1,
      Function.update_self, cleared_stash]
  · simp [prefixResult, h2, h1, h0,
      cleared_other B x h0 h1 h2]

noncomputable def firstBank {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) : Ambient q → List Bool :=
  bank firstEmbedding (foreign q saved output count) U

noncomputable def laterBank {q : Nat}
    (V : SourceCSPFirstSlotBridge.Stack q → List Bool)
    (saved output count : List Bool) : Ambient q → List Bool :=
  bank laterEmbedding (foreign q saved output count) V

theorem first_bank_global {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    firstBank U saved output count (.inl (.inl g)) = U (.inl g) :=
  bank_at firstEmbedding (foreign q saved output count) U (.inl g)

theorem first_bank_writer {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (k : SourceClauseRowWriterOperands.Stack q) :
    firstBank U saved output count (.inl (.inr (.inl k))) = U (.inr k) :=
  bank_at firstEmbedding (foreign q saved output count) U (.inr k)

theorem first_bank_stash {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) (i : Fin 4) :
    firstBank U saved output count (stash i) =
      foreign q saved output count (stash i) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases k <;> cases hk

theorem first_bank_extra {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (k : Fin 2) :
    firstBank U saved output count (.inl (.inr (.inr k))) = [] := by
  rw [firstBank, bank_outside]
  · rfl
  · rintro ⟨x, hx⟩
    cases x <;> cases hx

theorem later_bank_at {q : Nat}
    (V : SourceCSPFirstSlotBridge.Stack q → List Bool)
    (saved output count : List Bool)
    (x : SourceCSPFirstSlotBridge.Stack q) :
    laterBank V saved output count (.inl x) = V x :=
  bank_at laterEmbedding (foreign q saved output count) V x

theorem later_bank_stash {q : Nat}
    (V : SourceCSPFirstSlotBridge.Stack q → List Bool)
    (saved output count : List Bool) (i : Fin 4) :
    laterBank V saved output count (stash i) =
      foreign q saved output count (stash i) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases hk

theorem prefix_result_first {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    prefixResult (firstBank U saved output count) =
      laterBank
        (SourceCSPFirstSlotBridge.extended
          (prefixBank U saved output count))
        saved output count := by
  funext x
  rw [prefix_result_value]
  cases x with
  | inl y =>
      cases y with
      | inl g =>
          simp [prefixTarget, firstEmbedding, later_bank_at,
            SourceCSPFirstSlotBridge.extended,
            first_bank_global, prefixBank_global]
      | inr z =>
          cases z with
          | inl k =>
              simp [prefixTarget, firstEmbedding, later_bank_at,
                SourceCSPFirstSlotBridge.extended,
                first_bank_writer, prefixBank, Function.update_apply]
              have hs : firstBank U saved output count (Sum.inr (0 : Fin 4)) = saved := by
                simpa [stash, foreign] using
                  first_bank_stash U saved output count 0
              have ho : firstBank U saved output count (Sum.inr (1 : Fin 4)) = output := by
                simpa [stash, foreign] using
                  first_bank_stash U saved output count 1
              have hc : firstBank U saved output count (Sum.inr (2 : Fin 4)) = count := by
                simpa [stash, foreign] using
                  first_bank_stash U saved output count 2
              simp [stash, hs, ho, hc]
          | inr j =>
              simp [prefixTarget, firstEmbedding, later_bank_at,
                SourceCSPFirstSlotBridge.extended, first_bank_extra]
  | inr i =>
      change firstBank U saved output count (stash i) =
        laterBank
          (SourceCSPFirstSlotBridge.extended
            (prefixBank U saved output count))
          saved output count (stash i)
      rw [first_bank_stash, later_bank_stash]

theorem prefix_time_bound {q F : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (hU : ∀ x, (U x).length ≤ F) :
    prefixTime (firstBank U saved output count) ≤
      3 * F + 2 * (saved.length + output.length + count.length) + 14 := by
  let B := firstBank U saved output count
  have h0 := hU (.inr SourceClauseRowWriterCleanup.savedCell)
  have h1 := hU (.inr SourceClauseRowWriterCleanup.outputCell)
  have h2 := hU (.inr SourceClauseRowWriterCleanup.countCell)
  have ht0 : B (prefixTarget 0) = U (.inr SourceClauseRowWriterCleanup.savedCell) :=
    first_bank_writer U saved output count _
  have ht1 : B (prefixTarget 1) = U (.inr SourceClauseRowWriterCleanup.outputCell) :=
    first_bank_writer U saved output count _
  have ht2 : B (prefixTarget 2) = U (.inr SourceClauseRowWriterCleanup.countCell) :=
    first_bank_writer U saved output count _
  have hs0 : B (stash 0) = saved := by
    simpa [stash, foreign] using first_bank_stash U saved output count 0
  have hs1 : B (stash 1) = output := by
    simpa [stash, foreign] using first_bank_stash U saved output count 1
  have hs2 : B (stash 2) = count := by
    simpa [stash, foreign] using first_bank_stash U saved output count 2
  have hsum : (∑ i : Fin 3, (B (prefixTarget i)).length) ≤ 3 * F := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (B (prefixTarget 0)).length +
      ((B (prefixTarget 1)).length + (B (prefixTarget 2)).length) ≤ 3 * F
    rw [ht0, ht1, ht2]
    omega
  dsimp [prefixTime, clearTime]
  change (∑ i : Fin 3, (B (prefixTarget i)).length) + 5 +
      (2 * (B (stash 0)).length + 2) +
      (2 * (B (stash 1)).length + 2) +
      (2 * (B (stash 2)).length + 2) + 3 ≤
    3 * F + 2 * (saved.length + output.length + count.length) + 14
  rw [hs0, hs1, hs2]
  omega

noncomputable def callbackLift (q : Nat) (hq : 0 < q) :=
  fun l => stackStmt (laterEmbedding (q := q)) (callbackProgram q hq l)

def clearLift (q : Nat) :=
  fun l => stackStmt (laterEmbedding (q := q)) (clearLoopProgram q l)

noncomputable def loopLift (q : Nat) (hq : 0 < q) :=
  fun l => stackStmt (laterEmbedding (q := q))
    (SourceCSPAllRowLoop.program hq l)

theorem later_run {q : Nat} {L V : Type*}
    (P : L → TM2.Stmt (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool) L V)
    (saved output count : List Bool)
    (c d : TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool) L V)
    (t : Nat) (hrun : ((advance P)^[t]) c = d) :
    ((advance (fun l => stackStmt (laterEmbedding (q := q)) (P l)))^[t])
      (stackCfg laterEmbedding (foreign q saved output count) c) =
      stackCfg laterEmbedding (foreign q saved output count) d := by
  have h := BitMachineStackRun.run laterEmbedding
    (foreign q saved output count) P c t
  rwa [hrun] at h

def firstStart (q : Nat) : SourceCSPFirstRowController.Label 2 q :=
  .inl (.prefix (.prefix (.inl
    (SourceCSPGuardDispatchSequence.headerStart 2 q))))

def firstControl (q : Nat) : SourceCSPFirstRowController.Control 2 q :=
  (.prefix SourceCSPGuardOutputCombined.initialControl,
    SourceCSPFirstRowController.bodyInitial)

theorem initial_exact (q : Nat) (input saved output count : List Bool) :
    initial q input saved output count =
      ⟨some (firstStart q), firstControl q,
        bank firstEmbedding (foreign q saved output count)
          (SourceCSPFirstRowController.initial 2 q input).stk⟩ := rfl

def prefixStart :
    BitMachineRawSequence.Label (Fin 5)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
        BitMachineCopy.Label) :=
  .inl 0

def prefixControl :
    (Unit × Option Bool) ×
      ((Option Bool × Option Bool) × Option Bool) :=
  (((), none), ((none, none), none))

noncomputable def phase1 (q : Nat) :=
  BitMachineRawSequence.program (firstProgram q) (prefixProgram q)
    prefixStart (firstControl q) prefixControl

noncomputable def phase2 (q : Nat) (hq : 0 < q) :=
  BitMachineRawSequence.program (phase1 q) (callbackLift q hq)
    (BitMachineRawSequence.leftLabel (.clear 0))
    (firstControl q, prefixControl)
    (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)

noncomputable def phase3 (q : Nat) (hq : 0 < q) :=
  BitMachineRawSequence.program (phase2 q hq) (clearLift q)
    0
    ((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial))
    ((), none)

noncomputable def fullProgram (q : Nat) (hq : 0 < q) :=
  BitMachineRawSequence.program (phase3 q hq) (loopLift q hq)
    (.copy .scan)
    (((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
      ((), none))
    (.copy none)

noncomputable def wrapperClock (q : Nat) (hq : 0 < q)
    (L A : Nat) : Nat :=
  let F := firstEnvelope q L
  let B := entryBase q L A
  let H := entryEnvelope q hq L A
  SourceCSPFirstRowController.cubicCoefficient 2 q * (L + 1) ^ 3 +
    (3 * F + 2 * A + 14) + callbackClock q B + (H + 2) +
    SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 + 4

noncomputable def wrapperPerStep (q : Nat) (hq : 0 < q) : Nat := by
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  letI : Finite C.Label := C.labelsFinite
  letI : Fintype C.Label := Fintype.ofFinite _
  letI : Fintype (SourceCSPAllRowLoop.Label hq) := Fintype.ofFinite _
  letI : Fintype (SourceCSPFirstRowController.Label 2 q) := Fintype.ofFinite _
  exact BitMachineStackGrowth.perStep (fullProgram q hq)

noncomputable def wrapperEndpoint (q : Nat) (hq : 0 < q)
    (L A : Nat) : Nat :=
  L + A + wrapperPerStep q hq * wrapperClock q hq L A

theorem initial_bank_le (q : Nat)
    (input saved output count : List Bool) (x : Ambient q) :
    ((initial q input saved output count).stk x).length ≤
      input.length +
        (saved.length + output.length + count.length) := by
  let U := (SourceCSPFirstRowController.initial 2 q input).stk
  change (firstBank U saved output count x).length ≤ _
  cases x with
  | inl y =>
      cases y with
      | inl g =>
          rw [first_bank_global]
          exact (SourceCSPEntryBound.first_initial_length_le q input (.inl g)).trans
            (Nat.le_add_right _ _)
      | inr z =>
          cases z with
          | inl k =>
              rw [first_bank_writer]
              exact (SourceCSPEntryBound.first_initial_length_le q input (.inr k)).trans
                (Nat.le_add_right _ _)
          | inr j =>
              rw [first_bank_extra]
              simp
  | inr i =>
      change (firstBank U saved output count (stash i)).length ≤ _
      rw [first_bank_stash]
      fin_cases i <;> simp [stash, foreign] <;> omega

theorem wrapper_run_endpoint (q : Nat) (hq : 0 < q)
    (input saved output count : List Bool)
    (t : Nat)
    (c : TM2.Cfg (fun _ : Ambient q => Bool) _ _)
    (ht : t ≤ wrapperClock q hq input.length
      (saved.length + output.length + count.length))
    (hrun : ((advance (fullProgram q hq))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (firstStart q))))),
        ((((firstControl q, prefixControl),
          (((), none),
            (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
          ((), none)), .copy none),
        (initial q input saved output count).stk⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) = c) :
    ∀ x, (c.stk x).length ≤ wrapperEndpoint q hq input.length
      (saved.length + output.length + count.length) := by
  intro x
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  letI : Finite C.Label := C.labelsFinite
  letI : Fintype C.Label := Fintype.ofFinite _
  letI : Fintype (SourceCSPAllRowLoop.Label hq) := Fintype.ofFinite _
  letI : Fintype (SourceCSPFirstRowController.Label 2 q) := Fintype.ofFinite _
  have hg := BitMachineStackGrowth.run_growth (fullProgram q hq)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (firstStart q))))),
      ((((firstControl q, prefixControl),
        (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
        ((), none)), .copy none),
      (initial q input saved output count).stk⟩ :
      TM2.Cfg (fun _ : Ambient q => Bool) _ _) t x
  rw [hrun] at hg
  have hi := initial_bank_le q input saved output count x
  change (c.stk x).length ≤
    ((initial q input saved output count).stk x).length +
      wrapperPerStep q hq * t at hg
  dsimp [wrapperEndpoint]
  exact le_trans hg (by nlinarith)

theorem compose_physical (q : Nat) (hq : 0 < q)
    (input saved output count : List Bool)
    (tf tc tclear tloop : Nat)
    (v : SourceCSPFirstRowController.Control 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (V2 V3 V4 : SourceCSPFirstSlotBridge.Stack q → List Bool)
    (hfirst : ((advance (SourceCSPFirstRowController.program 2 q))^[tf])
      (SourceCSPFirstRowController.initial 2 q input) = ⟨none, v, U⟩)
    (hcallback : ((advance (callbackProgram q hq))^[tc])
      (callbackInitial q hq (prefixBank U saved output count)) =
      ⟨none, (((), none),
        (SourceClauseCallback.AllSlots.allCircuit hq).initial), V2⟩)
    (hclear : ((advance (clearLoopProgram q))^[tclear])
      (⟨some 0, ((), none), V2⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool)
          (Fin 2) (Unit × Option Bool)) = ⟨none, ((), none), V3⟩)
    (hloop : ((advance (SourceCSPAllRowLoop.program hq))^[tloop])
      (⟨some (.copy .scan), .copy none, V3⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool)
          (SourceCSPAllRowLoop.Label hq)
          (SourceCSPAllRowLoop.Control hq)) =
      ⟨none, .done true, V4⟩) :
    ∃ t ≤ tf + prefixTime (firstBank U saved output count) + tc +
        tclear + tloop + 4,
      ((advance (fullProgram q hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (firstStart q))))),
          ((((firstControl q, prefixControl),
            (((), none),
              (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
            ((), none)), .copy none),
          (initial q input saved output count).stk⟩ :
          TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
        ⟨none,
          ((((firstControl q, prefixControl),
            (((), none),
              (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
            ((), none)), .done true),
          laterBank V4 saved output count⟩ := by
  let B1 := firstBank U saved output count
  let B2 := laterBank
    (SourceCSPFirstSlotBridge.extended
      (prefixBank U saved output count)) saved output count
  let B3 := laterBank V2 saved output count
  let B4 := laterBank V3 saved output count
  let B5 := laterBank V4 saved output count
  have hf : ((advance (firstProgram q))^[tf])
      (⟨some (firstStart q), firstControl q,
        (initial q input saved output count).stk⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
      ⟨none, v, B1⟩ := by
    simpa [initial_exact, B1, firstBank] using
      first_run q input saved output count tf v U hfirst
  obtain ⟨tp, htp, hp⟩ := prefix_run B1 (by
    simpa [B1, stash, foreign] using
      first_bank_stash U saved output count 3)
  have hp' : ((advance (prefixProgram q))^[tp])
      (⟨some prefixStart, prefixControl, B1⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
      ⟨none, prefixControl, B2⟩ := by
    simpa [prefixStart, prefixControl, B2, B1,
      prefix_result_first] using hp
  have hcb : ((advance (callbackLift q hq))^[tc])
      (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
        (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial), B2⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
      ⟨none, (((), none),
        (SourceClauseCallback.AllSlots.allCircuit hq).initial), B3⟩ := by
    simpa [callbackLift, callbackInitial, B2, B3, laterBank] using
      later_run (callbackProgram q hq) saved output count
        (callbackInitial q hq (prefixBank U saved output count))
        ⟨none, (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial), V2⟩
        tc hcallback
  have hcl : ((advance (clearLift q))^[tclear])
      (⟨some 0, ((), none), B3⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
      ⟨none, ((), none), B4⟩ := by
    simpa [clearLift, B3, B4, laterBank] using
      later_run (clearLoopProgram q) saved output count
        (⟨some 0, ((), none), V2⟩ :
          TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool)
            (Fin 2) (Unit × Option Bool))
        ⟨none, ((), none), V3⟩ tclear hclear
  have hl : ((advance (loopLift q hq))^[tloop])
      (⟨some (.copy .scan), .copy none, B4⟩ :
        TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
      ⟨none, .done true, B5⟩ := by
    simpa [loopLift, B4, B5, laterBank] using
      later_run (SourceCSPAllRowLoop.program hq) saved output count
        (⟨some (.copy .scan), .copy none, V3⟩ :
          TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool)
            (SourceCSPAllRowLoop.Label hq)
            (SourceCSPAllRowLoop.Control hq))
        ⟨none, .done true, V4⟩ tloop hloop
  obtain ⟨t1, ht1, h1⟩ := BitMachineRawSequence.runs
    (firstProgram q) (prefixProgram q)
    (firstStart q) prefixStart
    (firstControl q) v prefixControl prefixControl
    (initial q input saved output count).stk B1 B2 tf tp hf hp'
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs
    (phase1 q) (callbackLift q hq)
    (BitMachineRawSequence.leftLabel (firstStart q))
    (BitMachineRawSequence.leftLabel (.clear 0))
    (firstControl q, prefixControl)
    (firstControl q, prefixControl)
    (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)
    (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)
    (initial q input saved output count).stk B2 B3 t1 tc h1 hcb
  obtain ⟨t3, ht3, h3⟩ := BitMachineRawSequence.runs
    (phase2 q hq) (clearLift q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (firstStart q))) 0
    ((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial))
    ((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial))
    ((), none) ((), none)
    (initial q input saved output count).stk B3 B4 t2 tclear h2 hcl
  obtain ⟨t4, ht4, h4⟩ := BitMachineRawSequence.runs
    (phase3 q hq) (loopLift q hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (firstStart q))))
    (.copy .scan)
    (((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
      ((), none))
    (((firstControl q, prefixControl),
      (((), none), (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
      ((), none))
    (.copy none) (.done true)
    (initial q input saved output count).stk B4 B5 t3 tloop h3 hl
  refine ⟨t4, ?_, ?_⟩
  · change tp ≤ prefixTime (firstBank U saved output count) at htp
    omega
  · simpa only [fullProgram, B5] using h4

/-- The accepting validator run is a branch premise, while the physical wrapper
itself starts at the raw first-controller input. Its first clock includes the
validator and first-row work. The three prefix words are supplied in distinct
ambient cells, then physically copied into the writer cells. -/
theorem raw_accepted_full_row_wrapper (q : Nat) (hq : 0 < q)
    (input : List Bool) (ta : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (Sa : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[ta])
      (SourceCSPGlobalDecisionProgram.initial 2 q input) =
        ⟨none, .row (vr, some true), Sa⟩)
    (saved output count : List Bool) :
    let A := saved.length + output.length + count.length
    let H := entryEnvelope q hq input.length A
    ∃ (n m : Nat) (hm : 0 < m)
      (rows : Fin m → SourceCSPCodec.Row n 2 q)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool)
      (t : Nat),
      n ≤ H ∧ m ≤ H ∧ t ≤ wrapperClock q hq input.length A ∧
      ((advance (fullProgram q hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (firstStart q))))),
          ((((firstControl q, prefixControl),
            (((), none),
              (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
            ((), none)), .copy none),
          (initial q input saved output count).stk⟩ :
          TM2.Cfg (fun _ : Ambient q => Bool) _ _) =
        ⟨none,
          ((((firstControl q, prefixControl),
            (((), none),
              (SourceClauseCallback.AllSlots.allCircuit hq).initial)),
            ((), none)), .done true),
          laterBank
            (SourceCSPNextRowBridge.callbackBank
              (SourceCSPAllRowLoop.withRemaining
                (Function.update Sa SourceCSPHeaderRowBridge.loopCount []) 0)
              lastRow n (m - 1)
              ((EncodedCNF.clauseFields
                (SourceCSPAllRowLoop.suffixClauses rows hq 0
                  (m - 1) (by omega))).reverse ++
                (EncodedCNF.clauseFields
                  (SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩)).reverse ++ saved)
              output
              (List.replicate
                (SourceCSPAllRowLoop.suffixClauses rows hq 0
                  (m - 1) (by omega)).length true ++
                List.replicate
                  (SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩).length
                  true ++ count))
            saved output count⟩ ∧
      lastRow (.inr 0) = [] := by
  let A := saved.length + output.length + count.length
  let B := entryBase q input.length A
  let H := entryEnvelope q hq input.length A
  obtain ⟨n, m, hm, rows, tf, v, U, tc, tclear, tloop,
    lastRow, hn, hmH, htf, htc, htclear, htloop, _hbudget,
    hfirst, hcallback, hclear, hloop, hlast⟩ :=
      raw_accepted_full_row_continuation q hq input ta vr Sa hacc
        saved output count
  let first := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  let suffix := SourceCSPAllRowLoop.suffixClauses rows hq 0
    (m - 1) (by omega)
  let saved' := (EncodedCNF.clauseFields first).reverse ++ saved
  let count' := List.replicate first.length true ++ count
  let Sc := Function.update Sa SourceCSPHeaderRowBridge.loopCount []
  let Ub := prefixBank U saved output count
  let row := SourceCSPFirstSlotBridge.row Ub
  let V2 := SourceCSPNextRowBridge.callbackBank Sa row n 0
    saved' output count'
  let V3 := SourceCSPNextRowBridge.callbackBank Sc row n 0
    saved' output count'
  let V4 := SourceCSPNextRowBridge.callbackBank
    (SourceCSPAllRowLoop.withRemaining Sc 0)
    lastRow n (m - 1)
    ((EncodedCNF.clauseFields suffix).reverse ++ saved')
    output (List.replicate suffix.length true ++ count')
  obtain ⟨t, ht, hr⟩ := compose_physical q hq input saved output count
    tf tc tclear tloop v U V2 V3 V4 hfirst hcallback hclear hloop
  have hwords := actual_first_bank_le q input tf v U htf hfirst
  have hprefix := prefix_time_bound U saved output count hwords
  refine ⟨n, m, hm, rows, lastRow, t, hn, hmH, ?_, ?_, hlast⟩
  · dsimp [wrapperClock]
    change tc ≤ callbackClock q B at htc
    change tclear ≤ H + 2 at htclear
    change tloop ≤
      SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 at htloop
    omega
  · simpa only [V4, Sc, saved', count', first, suffix,
      List.append_assoc] using hr

end EthInapproximability.CurrentPaper.SourceCSPEntryWrapper
