import Paper2.OutputSkipperLabel
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Physical label skipping and capture on top of the output skipper.

Bank: the skipper cells, then `code` (retained serialized code of one label
kind), `cnt` (unary counter, consumed), `scr` (copy scratch), `lbl` (output
label). `skipN` repeats, `cnt` times: source-preserving copy of `code` into
the skipper's syntax cell, one `true` marker, one full skipper run (consumes
exactly one produced label from `out`), clearing of `used`. `capture` does
one more skipper run and reverses the consumed label into `lbl`. -/

namespace Paper2.FetchLabel

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open OutputSkipper (bk ctl0 ready Shape)

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev SkStack := OutputSkipper.Stack
abbrev Stack := SkStack ⊕ Fin 4

def ext4 (a b c d : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

def fb (S : SkStack → List Bool) (code cnt scr lbl : List Bool) : Stack → List Bool :=
  Sum.elim S (ext4 code cnt scr lbl)

def codeC : Stack := .inr 0
def cntC : Stack := .inr 1
def scrC : Stack := .inr 2
def lblC : Stack := .inr 3
def skC (k : SkStack) : Stack := .inl k

def skSlots : SkStack ↪ Stack := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

def copySlot : Fin 3 → Stack
  | 0 => codeC
  | 1 => skC (OutputSkipper.hc 0)
  | _ => scrC

theorem copySlot_injective : Function.Injective copySlot := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [copySlot, codeC, scrC, skC, OutputSkipper.hc]

def copySlots : Fin 3 ↪ Stack := ⟨copySlot, copySlot_injective⟩

inductive Label where
  | cnt
  | copy (l : BitMachineCopy.Label)
  | mark
  | skip (l : OutputSkipper.Label)
  | clr
  | rev

abbrev Control := Option Bool × (Option Bool × OutputSkipper.Control)

def base : Control := (none, (none, ctl0))

def skProgram := fun l => BitMachineStackEmbedding.stackStmt skSlots (OutputSkipper.program l)

/-- `capture = false`: `skipN` (loop on the counter). `capture = true`: one
run then reverse into `lbl`. The label table is fixed; the flag is a fixed
program parameter. -/
def program (capture : Bool) : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .cnt => pop cntC (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (load (fun _ => base) (goto (fun _ => .copy .scan))) halt)
  | .copy l => BitMachineInline.stmt Label.copy (fun c => (none, (c, ctl0)))
      (fun v => v.2.1) (some .mark)
      (MatrixStage4ScalarPreparationOps.copyProgram copySlots l)
  | .mark => push (skC OutputSkipper.pending) (fun _ => true)
      (load (fun _ => base) (goto (fun _ => .skip (.inr .check))))
  | .skip l => BitMachineInline.stmt Label.skip (fun w => (none, (none, w)))
      (fun v => v.2.2) (some (if capture then .rev else .clr)) (skProgram l)
  | .clr => pop (skC OutputSkipper.used) (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome) (goto (fun _ => .clr)) (goto (fun _ => .cnt)))
  | .rev => pop (skC OutputSkipper.used) (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (push lblC (fun v => v.1.getD false) (goto (fun _ => .rev))) halt)

def run (capture : Bool) (n : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance (program capture))^[n]) c

theorem run_add (capture : Bool) (m n : Nat) (c) :
    run capture (m + n) c = run capture n (run capture m c) := by
  unfold run; rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_one (capture : Bool) (c) : run capture 1 c = advance (program capture) c := rfl

/-! ### Bank lemmas -/

section BankLemmas
variable (S : SkStack → List Bool) (code cnt scr lbl x : List Bool)

@[simp] theorem fb_code : fb S code cnt scr lbl codeC = code := rfl
@[simp] theorem fb_cnt : fb S code cnt scr lbl cntC = cnt := rfl
@[simp] theorem fb_scr : fb S code cnt scr lbl scrC = scr := rfl
@[simp] theorem fb_lbl : fb S code cnt scr lbl lblC = lbl := rfl
@[simp] theorem fb_sk (k : SkStack) : fb S code cnt scr lbl (skC k) = S k := rfl

@[simp] theorem fup_cnt : Function.update (fb S code cnt scr lbl) cntC x =
    fb S code x scr lbl := by
  funext j; rcases j with j | j
  · rfl
  · fin_cases j <;> rfl
@[simp] theorem fup_lbl : Function.update (fb S code cnt scr lbl) lblC x =
    fb S code cnt scr x := by
  funext j; rcases j with j | j
  · rfl
  · fin_cases j <;> rfl
@[simp] theorem fup_sk (k : SkStack) : Function.update (fb S code cnt scr lbl) (skC k) x =
    fb (Function.update S k x) code cnt scr lbl := by
  funext j; rcases j with j | j
  · by_cases h : j = k
    · subst h; simp [fb, skC]
    · simp [fb, skC, Function.update_of_ne h,
        Function.update_of_ne (show (Sum.inl j : Stack) ≠ Sum.inl k from fun e => h (Sum.inl_injective e))]
  · simp [fb, skC]

end BankLemmas

/-! ### Steps -/

theorem cnt_cons (cap : Bool) (S) (code cnt scr lbl) (v : Control) :
    advance (program cap) ⟨some .cnt, v, fb S code (true :: cnt) scr lbl⟩ =
      ⟨some (.copy .scan), base, fb S code cnt scr lbl⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

theorem cnt_nil (cap : Bool) (S) (code scr lbl) (v : Control) :
    advance (program cap) ⟨some .cnt, v, fb S code [] scr lbl⟩ =
      ⟨none, (none, v.2), fb S code [] scr lbl⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

theorem mark_step (cap : Bool) (S) (code cnt scr lbl) (v : Control) :
    advance (program cap) ⟨some .mark, v, fb S code cnt scr lbl⟩ =
      ⟨some (.skip (.inr .check)), base,
        fb (Function.update S OutputSkipper.pending (true :: S OutputSkipper.pending))
          code cnt scr lbl⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

theorem clr_loop (S : SkStack → List Bool) (code cnt scr lbl : List Bool) :
    ∀ (U : List Bool) (v : Control), S OutputSkipper.used = U →
      run false (U.length + 1) ⟨some .clr, v, fb S code cnt scr lbl⟩ =
        ⟨some .cnt, (none, v.2),
          fb (Function.update S OutputSkipper.used []) code cnt scr lbl⟩
  | [], v, hU => by
      show run false 1 _ = _
      rw [run_one]
      have hS : Function.update S OutputSkipper.used [] = S := by
        rw [← hU]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hU, hS]
  | b :: U, v, hU => by
      rw [show (b :: U).length + 1 = 1 + (U.length + 1) by simp; omega, run_add, run_one]
      have e : advance (program false) ⟨some .clr, v, fb S code cnt scr lbl⟩ =
          ⟨some .clr, (some b, v.2),
            fb (Function.update S OutputSkipper.used U) code cnt scr lbl⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hU]
      rw [e, clr_loop (Function.update S OutputSkipper.used U) code cnt scr lbl U
        (some b, v.2) (by simp)]
      simp

theorem rev_loop (S : SkStack → List Bool) (code cnt scr : List Bool) :
    ∀ (U lbl : List Bool) (v : Control), S OutputSkipper.used = U →
      run true (U.length + 1) ⟨some .rev, v, fb S code cnt scr lbl⟩ =
        ⟨none, (none, v.2),
          fb (Function.update S OutputSkipper.used []) code cnt scr (U.reverse ++ lbl)⟩
  | [], lbl, v, hU => by
      show run true 1 _ = _
      rw [run_one]
      have hS : Function.update S OutputSkipper.used [] = S := by
        rw [← hU]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hU, hS]
  | b :: U, lbl, v, hU => by
      rw [show (b :: U).length + 1 = 1 + (U.length + 1) by simp; omega, run_add, run_one]
      have e : advance (program true) ⟨some .rev, v, fb S code cnt scr lbl⟩ =
          ⟨some .rev, (some b, v.2),
            fb (Function.update S OutputSkipper.used U) code cnt scr (b :: lbl)⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hU]
      rw [e, rev_loop (Function.update S OutputSkipper.used U) code cnt scr U (b :: lbl)
        (some b, v.2) (by simp)]
      simp

/-- The copy phase: `code` into the (empty) skipper syntax cell. -/
theorem copy_phase (cap : Bool) (S : SkStack → List Bool) (code cnt lbl : List Bool)
    (h0 : S (OutputSkipper.hc 0) = []) :
    ∃ t ≤ 2 * code.length + 2,
      run cap t ⟨some (.copy .scan), base, fb S code cnt [] lbl⟩ =
        ⟨some .mark, base, fb (Function.update S (OutputSkipper.hc 0) code) code cnt [] lbl⟩ := by
  have hc := MatrixStage4ScalarPreparationOps.copy_run copySlots (fb S code cnt [] lbl) rfl
  have hc' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram copySlots))^[
      2 * code.length + 2])
      (⟨some .scan, none, fb S code cnt [] lbl⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, fb (Function.update S (OutputSkipper.hc 0) code) code cnt [] lbl⟩ := by
    have e0 : fb S code cnt [] lbl (copySlots 0) = code := rfl
    have e1 : fb S code cnt [] lbl (copySlots 1) = [] := h0
    rw [e0, e1, List.append_nil] at hc
    rw [hc]
    congr 1
    exact fup_sk S code cnt [] lbl code (OutputSkipper.hc 0)
  have hh : (((advance (MatrixStage4ScalarPreparationOps.copyProgram copySlots))^[
      2 * code.length + 2]) (⟨some .scan, none, fb S code cnt [] lbl⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool))).l = none := by
    rw [hc']
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs Label.copy (fun c => (none, (c, ctl0)))
    (fun v => v.2.1) (fun _ => rfl) (some .mark)
    (MatrixStage4ScalarPreparationOps.copyProgram copySlots) (program cap) (fun _ => rfl)
    (⟨some .scan, none, fb S code cnt [] lbl⟩ :
      TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool))
    (2 * code.length + 2) hh
  rw [hc'] at hr
  exact ⟨t, ht, by simpa only [BitMachineInline.cfg, base] using hr⟩

/-- The skipper phase, inlined: one produced label consumed. -/
theorem skip_phase (cap : Bool) (c : Code) (hc : Shape c) (w : List Bool)
    (hw : Produces (meaning c) w) (O U code cnt lbl : List Bool) :
    ∃ t ≤ 8 * codeSize c * (w.length + 1) + 1,
      run cap t ⟨some (.skip (.inr .check)), base,
        fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl⟩ =
        ⟨some (if cap then .rev else .clr), (none, (none, (ctl0.1, (none, (none, 0))))),
          fb (bk [] [] [] [] [] [] [] [] O (w.reverse ++ U) []) code cnt [] lbl⟩ := by
  obtain ⟨t, ht, hr⟩ := OutputSkipper.label_run c hc w hw [] O U
  rw [List.append_nil] at hr
  have hs := BitMachineStackRun.run skSlots (fb (bk (encodeCode c) [] [] [] [] [] [] [true]
    (w ++ O) U []) code cnt [] lbl) OutputSkipper.program
    (ready (encodeCode c) [true] (w ++ O) U) t
  change ((advance OutputSkipper.program)^[t]) _ = _ at hr
  rw [hr] at hs
  have hb1 : BitMachineStackEmbedding.bank skSlots
      (fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl)
      (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) =
      fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hb2 : BitMachineStackEmbedding.bank skSlots
      (fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl)
      (bk [] [] [] [] [] [] [] [] O (w.reverse ++ U) []) =
      fb (bk [] [] [] [] [] [] [] [] O (w.reverse ++ U) []) code cnt [] lbl := by
    funext j; rcases j with j | j
    · exact BitMachineStackEmbedding.bank_at skSlots _ _ j
    · exact BitMachineStackEmbedding.bank_outside skSlots _ _ (.inr j)
        (by rintro ⟨k, hk⟩; cases hk)
  simp only [BitMachineStackEmbedding.stackCfg, ready, hb1, hb2] at hs
  have hh : (((advance skProgram)^[t]) (⟨some (.inr .check), ctl0,
      fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl⟩ :
      TM2.Cfg (fun _ : Stack => Bool) OutputSkipper.Label OutputSkipper.Control)).l = none := by
    rw [show skProgram = fun l => BitMachineStackEmbedding.stackStmt skSlots
      (OutputSkipper.program l) from rfl, hs]
  obtain ⟨n, hn, hrun⟩ := BitMachineInline.outputs Label.skip (fun w => (none, (none, w)))
    (fun v => v.2.2) (fun _ => rfl) (some (if cap then .rev else .clr)) skProgram
    (program cap) (fun _ => rfl)
    (⟨some (.inr .check), ctl0,
      fb (bk (encodeCode c) [] [] [] [] [] [] [true] (w ++ O) U []) code cnt [] lbl⟩ :
      TM2.Cfg (fun _ : Stack => Bool) OutputSkipper.Label OutputSkipper.Control) t hh
  rw [show skProgram = fun l => BitMachineStackEmbedding.stackStmt skSlots
    (OutputSkipper.program l) from rfl, hs] at hrun
  exact ⟨n, hn.trans ht, by simpa only [BitMachineInline.cfg, base] using hrun⟩

#print axioms clr_loop
#print axioms rev_loop
#print axioms copy_phase
#print axioms skip_phase

end Paper2.FetchLabel
