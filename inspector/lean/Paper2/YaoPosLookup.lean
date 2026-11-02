import Paper2.YaoSrcCodecB
import Paper2.YaoLookupEvaluation

/-! Unit 5 segment Y3 core (lane a-yao-owner-1): the physical position lookup,
the missing `positionEval` producer.

One fixed 14-label TM2 program on seven Boolean stacks
(0 body `B`, 1 skip counter `AK`, 2 position counter `KC`, 3 vertex `Vx`,
4 restore scratch `T`, 5 flag `F`, 6 output `OUT`).  Charged inputs: the exact
body stream `tokens (List.ofFn (flatten edges))` of a valid Y1 code (R-Y2;
Y2 leaves exactly this stream in its work cell when the code cell holds the
code alone), unary `a*K` (skip count), unary `K`, unary `vertex`.  The program
skips `a*K` fields; a peek detects the out-of-range case `a ≥ e` (body
exhausted; this is the `paddedEdgesEval` `none` branch) and sets the flag;
then `K` iterations compare fields with the vertex by moving unary marks
(the vertex word is restored each time), counting positions until the first
hit; a miss clears the output; finally the body remainder is cleared.
Exit bank exact: all scratch empty, the vertex word preserved, `OUT` =
unary `(positionEval (paddedEdgesEval edges) a vertex).val`.
Value bridge: the admitted `edgePositionEval_eq`, `edgePosition_apply`,
`edgePosition_absent`, `positionEval`, `paddedEdgesEval`. -/

namespace Paper2.YaoPositionLookup

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.RecursiveLabelCodecScratch
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec
open Paper2.YaoLookup

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Label where
  | skipLoop | skipField | check | scanLoop | iter | cmp | onTrue | onEnd
  | skipRest | restore | skipF | finish | clearOut | clearB
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label (Option Bool)
  | .skipLoop => pop 1 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .skipField)) (goto (fun _ => .check)))
  | .skipField => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false) (goto (fun _ => .skipField)) (goto (fun _ => .skipLoop)))
  | .check => peek 0 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .scanLoop))
        (push 5 (fun _ => true) (goto (fun _ => .scanLoop))))
  | .scanLoop => pop 2 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .iter)) (goto (fun _ => .finish)))
  | .iter => pop 5 (fun _ b => b)
      (branch (fun b => b.isSome) (push 5 (fun _ => true) (goto (fun _ => .skipF)))
        (push 6 (fun _ => true) (goto (fun _ => .cmp))))
  | .cmp => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false) (goto (fun _ => .onTrue)) (goto (fun _ => .onEnd)))
  | .onTrue => pop 3 (fun _ b => b)
      (branch (fun b => b.isSome) (push 4 (fun _ => true) (goto (fun _ => .cmp)))
        (goto (fun _ => .skipRest)))
  | .onEnd => pop 3 (fun _ b => b)
      (branch (fun b => b.isSome) (push 3 (fun _ => true) (goto (fun _ => .restore)))
        (push 5 (fun _ => true) (goto (fun _ => .restore))))
  | .skipRest => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false) (goto (fun _ => .skipRest)) (goto (fun _ => .restore)))
  | .restore => pop 4 (fun _ b => b)
      (branch (fun b => b.isSome) (push 3 (fun _ => true) (goto (fun _ => .restore)))
        (goto (fun _ => .scanLoop)))
  | .skipF => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false) (goto (fun _ => .skipF)) (goto (fun _ => .scanLoop)))
  | .finish => pop 5 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .clearB)) (goto (fun _ => .clearOut)))
  | .clearOut => pop 6 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .clearOut)) (goto (fun _ => .clearB)))
  | .clearB => pop 0 (fun _ b => b)
      (branch (fun b => b.isSome) (goto (fun _ => .clearB)) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label (Option Bool)

def cfg (l : Option Label) (c : Option Bool) (b ak kc vx t f out : List Bool) : Config :=
  ⟨l, c, ![b, ak, kc, vx, t, f, out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

/-- Reachability within a charged number of steps. -/
def RIn (c d : Config) (bd : ℕ) : Prop := ∃ n ≤ bd, run n c = d

theorem RIn.step {c d : Config} (h : TM2.step program c = some d) : RIn c d 1 :=
  ⟨1, le_rfl, by simp only [run, Function.iterate_one, advance, h, Option.getD_some]⟩

theorem RIn.refl (c : Config) : RIn c c 0 := ⟨0, le_rfl, rfl⟩

theorem RIn.trans {c d e : Config} {b₁ b₂ : ℕ} (h₁ : RIn c d b₁) (h₂ : RIn d e b₂) :
    RIn c e (b₁ + b₂) := by
  obtain ⟨n₁, hn₁, r₁⟩ := h₁
  obtain ⟨n₂, hn₂, r₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  simp only [run, Function.iterate_add_apply] at r₁ r₂ ⊢
  rw [r₁, r₂]

theorem RIn.mono {c d : Config} {b₁ b₂ : ℕ} (h : RIn c d b₁) (hb : b₁ ≤ b₂) : RIn c d b₂ := by
  obtain ⟨n, hn, r⟩ := h
  exact ⟨n, by omega, r⟩

theorem RIn.cast {c d : Config} {b₁ b₂ : ℕ} (h : RIn c d b₁) (hb : b₁ = b₂) : RIn c d b₂ :=
  hb ▸ h

macro "step_tac " l:term:max c:term:max : tactic =>
  `(tactic| (apply congrArg (fun S => some (⟨$l, $c, S⟩ : Config)); funext k; fin_cases k <;> rfl))

/-! ## Single steps -/

section Steps
variable (c : Option Bool) (b ak kc vx t f out : List Bool)

theorem s_skipLoop_mark : TM2.step program (cfg (some .skipLoop) c b (true :: ak) kc vx t f out) =
    some (cfg (some .skipField) (some true) b ak kc vx t f out) := by
  step_tac (some Label.skipField) (some true)
theorem s_skipLoop_empty : TM2.step program (cfg (some .skipLoop) c b [] kc vx t f out) =
    some (cfg (some .check) none b [] kc vx t f out) := by
  step_tac (some Label.check) none
theorem s_skipField_true : TM2.step program (cfg (some .skipField) c (true :: b) ak kc vx t f out) =
    some (cfg (some .skipField) (some true) b ak kc vx t f out) := by
  step_tac (some Label.skipField) (some true)
theorem s_skipField_false : TM2.step program (cfg (some .skipField) c (false :: b) ak kc vx t f out) =
    some (cfg (some .skipLoop) (some false) b ak kc vx t f out) := by
  step_tac (some Label.skipLoop) (some false)
theorem s_skipField_nil : TM2.step program (cfg (some .skipField) c [] ak kc vx t f out) =
    some (cfg (some .skipLoop) none [] ak kc vx t f out) := by
  step_tac (some Label.skipLoop) none
theorem s_check_some (x : Bool) : TM2.step program (cfg (some .check) c (x :: b) ak kc vx t f out) =
    some (cfg (some .scanLoop) (some x) (x :: b) ak kc vx t f out) := by
  step_tac (some Label.scanLoop) (some x)
theorem s_check_nil : TM2.step program (cfg (some .check) c [] ak kc vx t f out) =
    some (cfg (some .scanLoop) none [] ak kc vx t (true :: f) out) := by
  step_tac (some Label.scanLoop) none
theorem s_scan_mark : TM2.step program (cfg (some .scanLoop) c b ak (true :: kc) vx t f out) =
    some (cfg (some .iter) (some true) b ak kc vx t f out) := by
  step_tac (some Label.iter) (some true)
theorem s_scan_empty : TM2.step program (cfg (some .scanLoop) c b ak [] vx t f out) =
    some (cfg (some .finish) none b ak [] vx t f out) := by
  step_tac (some Label.finish) none
theorem s_iter_set : TM2.step program (cfg (some .iter) c b ak kc vx t (true :: f) out) =
    some (cfg (some .skipF) (some true) b ak kc vx t (true :: f) out) := by
  step_tac (some Label.skipF) (some true)
theorem s_iter_clear : TM2.step program (cfg (some .iter) c b ak kc vx t [] out) =
    some (cfg (some .cmp) none b ak kc vx t [] (true :: out)) := by
  step_tac (some Label.cmp) none
theorem s_cmp_true : TM2.step program (cfg (some .cmp) c (true :: b) ak kc vx t f out) =
    some (cfg (some .onTrue) (some true) b ak kc vx t f out) := by
  step_tac (some Label.onTrue) (some true)
theorem s_cmp_false : TM2.step program (cfg (some .cmp) c (false :: b) ak kc vx t f out) =
    some (cfg (some .onEnd) (some false) b ak kc vx t f out) := by
  step_tac (some Label.onEnd) (some false)
theorem s_onTrue_mark : TM2.step program (cfg (some .onTrue) c b ak kc (true :: vx) t f out) =
    some (cfg (some .cmp) (some true) b ak kc vx (true :: t) f out) := by
  step_tac (some Label.cmp) (some true)
theorem s_onTrue_empty : TM2.step program (cfg (some .onTrue) c b ak kc [] t f out) =
    some (cfg (some .skipRest) none b ak kc [] t f out) := by
  step_tac (some Label.skipRest) none
theorem s_onEnd_mark : TM2.step program (cfg (some .onEnd) c b ak kc (true :: vx) t f out) =
    some (cfg (some .restore) (some true) b ak kc (true :: vx) t f out) := by
  step_tac (some Label.restore) (some true)
theorem s_onEnd_empty : TM2.step program (cfg (some .onEnd) c b ak kc [] t f out) =
    some (cfg (some .restore) none b ak kc [] t (true :: f) out) := by
  step_tac (some Label.restore) none
theorem s_skipRest_true : TM2.step program (cfg (some .skipRest) c (true :: b) ak kc vx t f out) =
    some (cfg (some .skipRest) (some true) b ak kc vx t f out) := by
  step_tac (some Label.skipRest) (some true)
theorem s_skipRest_false : TM2.step program (cfg (some .skipRest) c (false :: b) ak kc vx t f out) =
    some (cfg (some .restore) (some false) b ak kc vx t f out) := by
  step_tac (some Label.restore) (some false)
theorem s_restore_mark : TM2.step program (cfg (some .restore) c b ak kc vx (true :: t) f out) =
    some (cfg (some .restore) (some true) b ak kc (true :: vx) t f out) := by
  step_tac (some Label.restore) (some true)
theorem s_restore_empty : TM2.step program (cfg (some .restore) c b ak kc vx [] f out) =
    some (cfg (some .scanLoop) none b ak kc vx [] f out) := by
  step_tac (some Label.scanLoop) none
theorem s_skipF_true : TM2.step program (cfg (some .skipF) c (true :: b) ak kc vx t f out) =
    some (cfg (some .skipF) (some true) b ak kc vx t f out) := by
  step_tac (some Label.skipF) (some true)
theorem s_skipF_false : TM2.step program (cfg (some .skipF) c (false :: b) ak kc vx t f out) =
    some (cfg (some .scanLoop) (some false) b ak kc vx t f out) := by
  step_tac (some Label.scanLoop) (some false)
theorem s_skipF_nil : TM2.step program (cfg (some .skipF) c [] ak kc vx t f out) =
    some (cfg (some .scanLoop) none [] ak kc vx t f out) := by
  step_tac (some Label.scanLoop) none
theorem s_finish_some : TM2.step program (cfg (some .finish) c b ak kc vx t (true :: f) out) =
    some (cfg (some .clearB) (some true) b ak kc vx t f out) := by
  step_tac (some Label.clearB) (some true)
theorem s_finish_none : TM2.step program (cfg (some .finish) c b ak kc vx t [] out) =
    some (cfg (some .clearOut) none b ak kc vx t [] out) := by
  step_tac (some Label.clearOut) none
theorem s_clearOut_mark (x : Bool) :
    TM2.step program (cfg (some .clearOut) c b ak kc vx t f (x :: out)) =
    some (cfg (some .clearOut) (some x) b ak kc vx t f out) := by
  step_tac (some Label.clearOut) (some x)
theorem s_clearOut_empty : TM2.step program (cfg (some .clearOut) c b ak kc vx t f []) =
    some (cfg (some .clearB) none b ak kc vx t f []) := by
  step_tac (some Label.clearB) none
theorem s_clearB_some (x : Bool) :
    TM2.step program (cfg (some .clearB) c (x :: b) ak kc vx t f out) =
    some (cfg (some .clearB) (some x) b ak kc vx t f out) := by
  step_tac (some Label.clearB) (some x)
theorem s_clearB_nil : TM2.step program (cfg (some .clearB) c [] ak kc vx t f out) =
    some (cfg none none [] ak kc vx t f out) := by
  step_tac none none

end Steps

/-! ## Loops -/

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_cons (n : ℕ) (l : List Bool) : rep n ++ true :: l = true :: (rep n ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep, List.replicate_succ] at ih ⊢; exact ih

theorem rep_succ_append (n : ℕ) (l : List Bool) : rep (n + 1) ++ l = true :: (rep n ++ l) := by
  simp [rep, List.replicate_succ]

theorem field_run (y : ℕ) (c : Option Bool) (X ak kc vx t f out : List Bool) :
    RIn (cfg (some .skipField) c (rep y ++ false :: X) ak kc vx t f out)
      (cfg (some .skipLoop) (some false) X ak kc vx t f out) (y + 1) := by
  induction y generalizing c with
  | zero => exact RIn.step (s_skipField_false c X ak kc vx t f out)
  | succ y ih =>
      rw [rep_succ_append]
      exact (RIn.step (s_skipField_true c _ ak kc vx t f out)).trans (ih _) |>.cast (by omega)

theorem tokens_cons {v : ℕ} (y : Fin v) (ys : List (Fin v)) :
    tokens (y :: ys) = rep y.val ++ false :: tokens ys := by
  simp [tokens, finCodec, rep, List.append_assoc]

theorem tokens_append {v : ℕ} (xs ys : List (Fin v)) :
    tokens (xs ++ ys) = tokens xs ++ tokens ys := by
  simp [tokens, List.flatMap_append]

theorem skip_run {v : ℕ} (n : ℕ) (xs : List (Fin v)) (c : Option Bool)
    (kc vx t f out : List Bool) :
    RIn (cfg (some .skipLoop) c (tokens xs) (rep n) kc vx t f out)
      (cfg (some .check) none (tokens (xs.drop n)) [] kc vx t f out)
      (2 * n + (tokens xs).length + 1) := by
  induction n generalizing xs c with
  | zero => exact (RIn.step (s_skipLoop_empty c _ kc vx t f out)).mono (by omega)
  | succ n ih =>
      rw [show rep (n + 1) = true :: rep n by simp [rep, List.replicate_succ]]
      cases xs with
      | nil =>
          have e0 : tokens ([] : List (Fin v)) = [] := rfl
          have h1 := RIn.step (s_skipLoop_mark c ([] : List Bool) (rep n) kc vx t f out)
          have h2 := RIn.step (s_skipField_nil (some true) (rep n) kc vx t f out)
          have h3 := ih [] none
          rw [e0, List.drop_nil] at h3
          rw [e0, List.drop_nil]
          exact (h1.trans (h2.trans h3)).mono (by simp only [List.length_nil]; omega)
      | cons y ys =>
          have h1 := RIn.step (s_skipLoop_mark c (tokens (y :: ys)) (rep n) kc vx t f out)
          rw [tokens_cons] at h1
          have h2 := field_run y.val (some true) (tokens ys) (rep n) kc vx t f out
          have h3 := ih ys (some false)
          rw [List.drop_succ_cons]
          have hl : (tokens (y :: ys)).length = y.val + 1 + (tokens ys).length := by
            rw [tokens_cons]; simp [rep]; omega
          rw [tokens_cons] at hl ⊢
          exact (h1.trans (h2.trans h3)).mono (by rw [hl]; omega)

theorem pairs_run (k : ℕ) (c : Option Bool) (X ak kc Y t f out : List Bool) :
    ∃ c', RIn (cfg (some .cmp) c (rep k ++ X) ak kc (rep k ++ Y) t f out)
      (cfg (some .cmp) c' X ak kc Y (rep k ++ t) f out) (2 * k) := by
  induction k generalizing c t with
  | zero => exact ⟨c, RIn.refl _⟩
  | succ k ih =>
      obtain ⟨c', h⟩ := ih (some true) (true :: t)
      refine ⟨c', ?_⟩
      rw [rep_succ_append, rep_succ_append, rep_succ_append]
      rw [rep_cons] at h
      exact ((RIn.step (s_cmp_true c (rep k ++ X) ak kc (true :: (rep k ++ Y)) t f out)).trans
        ((RIn.step (s_onTrue_mark (some true) (rep k ++ X) ak kc (rep k ++ Y) t f out)).trans
          h)).cast (by omega)

theorem restore_run (k : ℕ) (c : Option Bool) (b ak kc vx f out : List Bool) :
    RIn (cfg (some .restore) c b ak kc vx (rep k) f out)
      (cfg (some .scanLoop) none b ak kc (rep k ++ vx) [] f out) (k + 1) := by
  induction k generalizing c vx with
  | zero => exact RIn.step (s_restore_empty c b ak kc vx f out)
  | succ k ih =>
      have h := ih (some true) (true :: vx)
      rw [rep_cons] at h
      rw [show rep (k + 1) = true :: rep k by simp [rep, List.replicate_succ],
        List.cons_append]
      exact ((RIn.step (s_restore_mark c b ak kc vx (rep k) f out)).trans h).cast (by omega)

theorem skipRest_run (d : ℕ) (c : Option Bool) (X ak kc vx t f out : List Bool) :
    RIn (cfg (some .skipRest) c (rep d ++ false :: X) ak kc vx t f out)
      (cfg (some .restore) (some false) X ak kc vx t f out) (d + 1) := by
  induction d generalizing c with
  | zero => exact RIn.step (s_skipRest_false c X ak kc vx t f out)
  | succ d ih =>
      rw [rep_succ_append]
      exact ((RIn.step (s_skipRest_true c _ ak kc vx t f out)).trans (ih _)).cast (by omega)

theorem skipF_run (y : ℕ) (c : Option Bool) (X ak kc vx t f out : List Bool) :
    RIn (cfg (some .skipF) c (rep y ++ false :: X) ak kc vx t f out)
      (cfg (some .scanLoop) (some false) X ak kc vx t f out) (y + 1) := by
  induction y generalizing c with
  | zero => exact RIn.step (s_skipF_false c X ak kc vx t f out)
  | succ y ih =>
      rw [rep_succ_append]
      exact ((RIn.step (s_skipF_true c _ ak kc vx t f out)).trans (ih _)).cast (by omega)

def flagWord (b : Bool) : List Bool := if b then [true] else []

/-- One comparison iteration with the flag clear. -/
theorem iter_clear_run {v : ℕ} (y : Fin v) (ys : List (Fin v)) (w : ℕ) (c : Option Bool)
    (ak kc out : List Bool) :
    RIn (cfg (some .iter) c (tokens (y :: ys)) ak kc (rep w) [] [] out)
      (cfg (some .scanLoop) none (tokens ys) ak kc (rep w) []
        (flagWord (decide (y.val = w))) (true :: out)) (3 * y.val + 3 * w + 5) := by
  rw [tokens_cons]
  have h0 := RIn.step (s_iter_clear c (rep y.val ++ false :: tokens ys) ak kc (rep w) [] out)
  rcases lt_trichotomy y.val w with hlt | heq | hgt
  · -- the field is shorter than the vertex word
    obtain ⟨d, hd⟩ : ∃ d, w = y.val + 1 + d := ⟨w - y.val - 1, by omega⟩
    have hvx : rep w = rep y.val ++ true :: rep d := by
      rw [hd, show y.val + 1 + d = y.val + (d + 1) by omega]
      simp [rep, List.replicate_add, List.replicate_succ]
    rw [show flagWord (decide (y.val = w)) = [] by simp [flagWord, show y.val ≠ w by omega]]
    obtain ⟨c', hp⟩ := pairs_run y.val none (false :: tokens ys) ak kc (true :: rep d) []
      [] (true :: out)
    rw [hvx]
    rw [hvx] at h0
    have h3 := RIn.step (s_cmp_false c' (tokens ys) ak kc (true :: rep d) (rep y.val ++ [])
      [] (true :: out))
    have h4 := RIn.step (s_onEnd_mark (some false) (tokens ys) ak kc (rep d)
      (rep y.val ++ []) [] (true :: out))
    have h5 := restore_run y.val (some true) (tokens ys) ak kc (true :: rep d) [] (true :: out)
    simp only [List.append_nil] at h3 h4 hp
    exact (h0.trans (hp.trans (h3.trans (h4.trans h5)))).mono (by omega)
  · -- equal: a hit
    rw [show flagWord (decide (y.val = w)) = [true] by simp [flagWord, heq]]
    obtain ⟨c', hp⟩ := pairs_run y.val none (false :: tokens ys) ak kc [] [] [] (true :: out)
    rw [← heq]
    rw [← heq] at h0
    have hw : rep y.val = rep y.val ++ [] := by simp
    rw [hw] at h0
    have h3 := RIn.step (s_cmp_false c' (tokens ys) ak kc [] (rep y.val ++ []) [] (true :: out))
    have h4 := RIn.step (s_onEnd_empty (some false) (tokens ys) ak kc (rep y.val ++ [])
      [] (true :: out))
    have h5 := restore_run y.val none (tokens ys) ak kc [] [true] (true :: out)
    simp only [List.append_nil] at h0 h3 h4 hp h5
    exact (h0.trans (hp.trans (h3.trans (h4.trans h5)))).mono (by omega)
  · -- the field is longer than the vertex word
    obtain ⟨d, hd⟩ : ∃ d, y.val = w + 1 + d := ⟨y.val - w - 1, by omega⟩
    have hb : rep y.val ++ false :: tokens ys = rep w ++ (true :: (rep d ++ false :: tokens ys)) := by
      rw [hd, show w + 1 + d = w + (d + 1) by omega]
      simp [rep, List.replicate_add, List.replicate_succ, List.append_assoc]
    rw [show flagWord (decide (y.val = w)) = [] by simp [flagWord, show y.val ≠ w by omega]]
    rw [hb] at h0
    rw [hb]
    obtain ⟨c', hp⟩ := pairs_run w none (true :: (rep d ++ false :: tokens ys)) ak kc [] []
      [] (true :: out)
    have hw : rep w = rep w ++ [] := by simp
    rw [hw] at h0
    have h3 := RIn.step (s_cmp_true c' (rep d ++ false :: tokens ys) ak kc [] (rep w ++ [])
      [] (true :: out))
    have h4 := RIn.step (s_onTrue_empty (some true) (rep d ++ false :: tokens ys) ak kc
      (rep w ++ []) [] (true :: out))
    have h5 := skipRest_run d none (tokens ys) ak kc [] (rep w ++ []) [] (true :: out)
    have h6 := restore_run w (some false) (tokens ys) ak kc [] [] (true :: out)
    simp only [List.append_nil] at h0 h3 h4 hp h5 h6
    exact (h0.trans (hp.trans (h3.trans (h4.trans (h5.trans h6))))).mono (by omega)

/-- One iteration with the flag set: the field is skipped. -/
theorem iter_set_run {v : ℕ} (y : Fin v) (ys : List (Fin v)) (c : Option Bool)
    (ak kc vx out : List Bool) :
    RIn (cfg (some .iter) c (tokens (y :: ys)) ak kc vx [] [true] out)
      (cfg (some .scanLoop) (some false) (tokens ys) ak kc vx [] [true] out) (y.val + 2) := by
  rw [tokens_cons]
  exact ((RIn.step (s_iter_set c _ ak kc vx [] [] out)).trans
    (skipF_run y.val (some true) (tokens ys) ak kc vx [] [true] out)).cast (by omega)

/-- Pure state of the scan: (found, count). -/
def scanStep {v : ℕ} (w : ℕ) (s : Bool × ℕ) (y : Fin v) : Bool × ℕ :=
  if s.1 then s else (decide (y.val = w), s.2 + 1)

theorem scan_run {v : ℕ} (w : ℕ) (L R : List (Fin v)) (s : Bool × ℕ) (c : Option Bool)
    (ak : List Bool) :
    RIn (cfg (some .scanLoop) c (tokens (L ++ R)) ak (rep L.length) (rep w) [] (flagWord s.1)
        (rep s.2))
      (cfg (some .finish) none (tokens R) ak [] (rep w) [] (flagWord (L.foldl (scanStep w) s).1)
        (rep (L.foldl (scanStep w) s).2))
      (L.length * (3 * w + 6) + 3 * (tokens L).length + 1) := by
  induction L generalizing s c with
  | nil => exact (RIn.step (s_scan_empty c _ ak _ [] _ _)).mono (by simp)
  | cons y L ih =>
      have hlen : (tokens (y :: L)).length = y.val + 1 + (tokens L).length := by
        rw [tokens_cons]; simp [rep]; omega
      obtain ⟨found, cnt⟩ := s
      have hrepL : rep (L.length + 1) = true :: rep L.length := by
        simp [rep, List.replicate_succ]
      rw [List.length_cons, hrepL, List.foldl_cons, List.cons_append]
      have h1 := RIn.step (s_scan_mark c (tokens (y :: (L ++ R))) ak (rep L.length) (rep w) []
        (flagWord (found, cnt).1) (rep (found, cnt).2))
      cases found with
      | true =>
          have e2 : scanStep w (true, cnt) y = (true, cnt) := rfl
          have e1 : flagWord (true, cnt).1 = [true] := rfl
          have h2 := iter_set_run y (L ++ R) (some true) ak (rep L.length) (rep w) (rep cnt)
          have h3 := ih (true, cnt) (some false)
          rw [e1] at h1 h3
          rw [e2, e1]
          exact (h1.trans (h2.trans h3)).mono (by rw [hlen]; nlinarith)
      | false =>
          have e2 : scanStep w (false, cnt) y = (decide (y.val = w), cnt + 1) := rfl
          have e1 : flagWord (false, cnt).1 = [] := rfl
          have hr : rep (decide (y.val = w), cnt + 1).2 = true :: rep cnt := by
            simp [rep, List.replicate_succ]
          have hf : flagWord (decide (y.val = w), cnt + 1).1 = flagWord (decide (y.val = w)) := rfl
          have h2 := iter_clear_run y (L ++ R) w (some true) ak (rep L.length) (rep cnt)
          have h3 := ih (decide (y.val = w), cnt + 1) none
          rw [hr, hf] at h3
          rw [e1] at h1
          rw [e2, e1]
          exact (h1.trans (h2.trans h3)).mono (by rw [hlen]; nlinarith)

theorem scan_empty_run (n : ℕ) (w : ℕ) (c : Option Bool) (ak out : List Bool) :
    RIn (cfg (some .scanLoop) c [] ak (rep n) (rep w) [] [true] out)
      (cfg (some .finish) none [] ak [] (rep w) [] [true] out) (3 * n + 1) := by
  induction n generalizing c with
  | zero => exact RIn.step (s_scan_empty c [] ak (rep w) [] [true] out)
  | succ n ih =>
      rw [show rep (n + 1) = true :: rep n by simp [rep, List.replicate_succ]]
      have h1 := RIn.step (s_scan_mark c [] ak (rep n) (rep w) [] [true] out)
      have h2 := RIn.step (s_iter_set (some true) [] ak (rep n) (rep w) [] [] out)
      have h3 := RIn.step (s_skipF_nil (some true) ak (rep n) (rep w) [] [true] out)
      exact (h1.trans (h2.trans (h3.trans (ih none)))).cast (by omega)

theorem clearOut_run (k : ℕ) (c : Option Bool) (b ak kc vx t f : List Bool) :
    RIn (cfg (some .clearOut) c b ak kc vx t f (rep k))
      (cfg (some .clearB) none b ak kc vx t f []) (k + 1) := by
  induction k generalizing c with
  | zero => exact RIn.step (s_clearOut_empty c b ak kc vx t f)
  | succ k ih =>
      rw [show rep (k + 1) = true :: rep k by simp [rep, List.replicate_succ]]
      exact ((RIn.step (s_clearOut_mark c b ak kc vx t f (rep k) true)).trans (ih _)).cast
        (by omega)

theorem clearB_run (b : List Bool) (c : Option Bool) (ak kc vx t f out : List Bool) :
    RIn (cfg (some .clearB) c b ak kc vx t f out)
      (cfg none none [] ak kc vx t f out) (b.length + 1) := by
  induction b generalizing c with
  | nil => exact RIn.step (s_clearB_nil c ak kc vx t f out)
  | cons x b ih =>
      exact ((RIn.step (s_clearB_some c b ak kc vx t f out x)).trans (ih _)).cast
        (by simp; omega)

/-! ## Pure value of the scan -/

theorem fold_true {v : ℕ} (w : ℕ) (L : List (Fin v)) (cnt : ℕ) :
    L.foldl (scanStep w) (true, cnt) = (true, cnt) := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [List.foldl_cons, scanStep, ih]

theorem fold_miss {v : ℕ} (w : ℕ) (L : List (Fin v)) (cnt : ℕ) (h : ∀ y ∈ L, y.val ≠ w) :
    L.foldl (scanStep w) (false, cnt) = (false, cnt + L.length) := by
  induction L generalizing cnt with
  | nil => rfl
  | cons y L ih =>
      rw [List.foldl_cons]
      have hy : y.val ≠ w := h y (by simp)
      simp only [scanStep, Bool.false_eq_true, if_false, decide_eq_false hy]
      rw [ih (cnt + 1) (fun z hz => h z (by simp [hz]))]
      simp; omega

theorem fold_hit {v : ℕ} (w : ℕ) (L₁ L₂ : List (Fin v)) (y : Fin v) (hy : y.val = w)
    (h : ∀ z ∈ L₁, z.val ≠ w) (cnt : ℕ) :
    (L₁ ++ y :: L₂).foldl (scanStep w) (false, cnt) = (true, cnt + L₁.length + 1) := by
  rw [List.foldl_append, fold_miss w L₁ cnt h, List.foldl_cons]
  simp only [scanStep, Bool.false_eq_true, if_false, decide_eq_true hy]
  exact fold_true w L₂ _

/-- The scan result over one ordered edge is its `edgePositionEval`. -/
theorem fold_edge {v K : ℕ} (edge : Fin K ↪ Fin v) (vertex : Fin v) :
    (if ((List.ofFn (fun j => edge j)).foldl (scanStep vertex.val) (false, 0)).1 then
      ((List.ofFn (fun j => edge j)).foldl (scanStep vertex.val) (false, 0)).2 else 0) =
      (edgePositionEval edge vertex).val := by
  rw [edgePositionEval_eq]
  by_cases hex : ∃ j, edge j = vertex
  · obtain ⟨j, hj⟩ := hex
    have hsplit : List.ofFn (fun j => edge j) =
        (List.ofFn (fun j => edge j)).take j.val ++ edge j ::
          (List.ofFn (fun j => edge j)).drop (j.val + 1) := by
      conv_lhs => rw [← List.take_append_drop j.val (List.ofFn (fun j => edge j))]
      congr 1
      rw [List.drop_eq_getElem_cons (by simp)]
      simp
    have hnot : ∀ z ∈ (List.ofFn (fun j => edge j)).take j.val, z.val ≠ vertex.val := by
      intro z hz hzv
      rw [List.mem_iff_getElem] at hz
      obtain ⟨i, hi, hzi⟩ := hz
      simp only [List.length_take, List.length_ofFn] at hi
      rw [List.getElem_take, List.getElem_ofFn] at hzi
      have : edge ⟨i, by omega⟩ = edge j := by
        rw [hzi, hj]; exact Fin.ext hzv
      have := congrArg Fin.val (edge.injective this)
      simp at this
      omega
    rw [hsplit, fold_hit vertex.val _ _ (edge j) (by rw [hj]) hnot 0]
    simp only [if_true, List.length_take, List.length_ofFn]
    rw [← hj, edgePosition_apply]
    simp
  · push Not at hex
    rw [fold_miss vertex.val _ 0 (by
      intro z hz hzv
      rw [List.mem_ofFn] at hz
      obtain ⟨j, rfl⟩ := hz
      exact hex j (Fin.ext hzv))]
    simp [edgePosition_absent edge vertex hex]

/-! ## The body stream: skipping `a*K` fields exposes edge `a` -/

theorem take_drop_flatten {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : ℕ) (ha : a < e) :
    ((List.ofFn (flatten edges)).drop (a * arity t)).take (arity t) =
      List.ofFn (fun j => edges ⟨a, ha⟩ j) := by
  have hK : 0 < arity t := by positivity
  have hle : a * arity t + arity t ≤ e * arity t := by nlinarith
  apply List.ext_getElem
  · simp; omega
  · intro j h₁ h₂
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    simp only [List.length_ofFn] at h₂
    simp only [flatten]
    have hdiv : (a * arity t + j) / arity t = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt h₂, Nat.zero_add]
    have hmod : (a * arity t + j) % arity t = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
    congr 2
    · ext; simp [finProdFinEquiv_symm_apply, Fin.divNat, hdiv]
    · ext; simp [finProdFinEquiv_symm_apply, Fin.modNat, hmod]

theorem drop_flatten_ge {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : ℕ) (ha : e ≤ a) : (List.ofFn (flatten edges)).drop (a * arity t) = [] := by
  apply List.drop_of_length_le
  simp only [List.length_ofFn]
  exact Nat.mul_le_mul_right _ ha

/-! ## Main lookup theorem -/

/-- Y3 core: the fixed program, from the exact body stream, unary `a*K`,
unary `K` and unary `vertex`, halts with all scratch empty, the vertex word
preserved, and unary `positionEval (paddedEdgesEval edges) a vertex` in `OUT`. -/
theorem physical_position_lookup {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v) (c : Option Bool) :
    RIn (cfg (some .skipLoop) c (tokens (List.ofFn (flatten edges))) (rep (a.val * arity t))
        (rep (arity t)) (rep vertex.val) [] [] [])
      (cfg none none [] [] [] (rep vertex.val) [] []
        (rep (positionEval (paddedEdgesEval edges) a vertex).val))
      (2 * (a.val * arity t) + 5 * (tokens (List.ofFn (flatten edges))).length +
        arity t * (3 * vertex.val + 6) + arity t + 6) := by
  set xs := List.ofFn (flatten edges) with hxs
  have h1 := skip_run (a.val * arity t) xs c (rep (arity t)) (rep vertex.val) [] [] []
  have hdroplen : (tokens (xs.drop (a.val * arity t))).length ≤ (tokens xs).length := by
    have hx : (tokens xs).length = (tokens (xs.take (a.val * arity t))).length +
        (tokens (xs.drop (a.val * arity t))).length := by
      conv_lhs => rw [← List.take_append_drop (a.val * arity t) xs]
      rw [tokens_append, List.length_append]
    omega
  by_cases ha : a.val < e
  · -- in range
    have hpos : positionEval (paddedEdgesEval edges) a vertex = edgePositionEval (edges ⟨a.val, ha⟩) vertex := by
      simp [positionEval, paddedEdgesEval, ha]
    set L := List.ofFn (fun j => edges ⟨a.val, ha⟩ j) with hL
    set R := (xs.drop (a.val * arity t)).drop (arity t) with hR
    have hsplit : xs.drop (a.val * arity t) = L ++ R := by
      rw [hL, ← take_drop_flatten edges a.val ha, hR, List.take_append_drop]
    have hLlen : L.length = arity t := by simp [hL]
    have hK : 0 < arity t := by positivity
    obtain ⟨y, L', hy⟩ : ∃ y L', L = y :: L' := by
      cases hc : L with
      | nil => rw [hc] at hLlen; simp at hLlen
      | cons y L' => exact ⟨y, L', rfl⟩
    rw [hsplit] at h1
    have hnb : ∃ x b, rep y.val ++ false :: tokens (L' ++ R) = x :: b := by
      cases hyv : y.val with
      | zero => exact ⟨false, tokens (L' ++ R), by simp [rep]⟩
      | succ n => exact ⟨true, rep n ++ false :: tokens (L' ++ R), by simp [rep, List.replicate_succ]⟩
    obtain ⟨x, b, hxb⟩ := hnb
    have h2 := RIn.step (s_check_some none b [] (rep (arity t)) (rep vertex.val) [] [] [] x)
    rw [← hxb, ← tokens_cons, ← List.cons_append, ← hy] at h2
    have h3 := scan_run vertex.val L R (false, 0) (some x) []
    rw [hLlen] at h3
    simp only [flagWord, Bool.false_eq_true, if_false] at h3
    have hval := fold_edge (edges ⟨a.val, ha⟩) vertex
    rw [← hL] at hval
    have hRlen : (tokens R).length ≤ (tokens xs).length := by
      have : (tokens (L ++ R)).length ≤ (tokens xs).length := by rw [← hsplit]; exact hdroplen
      rw [tokens_append, List.length_append] at this; omega
    have hLtok : (tokens L).length ≤ (tokens xs).length := by
      have : (tokens (L ++ R)).length ≤ (tokens xs).length := by rw [← hsplit]; exact hdroplen
      rw [tokens_append, List.length_append] at this; omega
    cases hf : (L.foldl (scanStep vertex.val) (false, 0)).1 with
    | true =>
        rw [hf] at h3
        simp only [↓reduceIte] at h3
        rw [hf] at hval
        simp only [↓reduceIte] at hval
        have h4 := RIn.step (s_finish_some none (tokens R) [] [] (rep vertex.val) [] []
          (rep (L.foldl (scanStep vertex.val) (false, 0)).2))
        have h5 := clearB_run (tokens R) (some true) [] [] (rep vertex.val) [] []
          (rep (L.foldl (scanStep vertex.val) (false, 0)).2)
        rw [hpos, ← hval]
        have := (h1.trans (h2.trans (h3.trans (h4.trans h5))))
        exact this.mono (by nlinarith)
    | false =>
        rw [hf] at h3
        simp only [Bool.false_eq_true, ↓reduceIte] at h3
        rw [hf] at hval
        simp only [Bool.false_eq_true, ↓reduceIte] at hval
        have h4 := RIn.step (s_finish_none none (tokens R) [] [] (rep vertex.val) []
          (rep (L.foldl (scanStep vertex.val) (false, 0)).2))
        have h5 := clearOut_run (L.foldl (scanStep vertex.val) (false, 0)).2 none (tokens R)
          [] [] (rep vertex.val) [] []
        have h6 := clearB_run (tokens R) none [] [] (rep vertex.val) [] [] []
        have hcnt : (L.foldl (scanStep vertex.val) (false, 0)).2 ≤ arity t := by
          have hmiss : ∀ z ∈ L, z.val ≠ vertex.val := by
            intro z hz hzv
            have hfold := fold_edge (edges ⟨a.val, ha⟩) vertex
            rw [← hL, hf] at hfold
            rw [hL, List.mem_ofFn] at hz
            obtain ⟨j, rfl⟩ := hz
            have hex : edges ⟨a.val, ha⟩ j = vertex := Fin.ext hzv
            rw [edgePositionEval_eq, ← hex, edgePosition_apply] at hfold
            simp at hfold
          rw [fold_miss vertex.val L 0 hmiss, hLlen]; omega
        rw [hpos, ← hval]
        have := (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))
        exact this.mono (by nlinarith)
  · -- out of range: the body is exhausted, the flag is set, nothing is output
    have hpos : positionEval (paddedEdgesEval edges) a vertex = 0 := by
      simp [positionEval, paddedEdgesEval, ha]
    rw [drop_flatten_ge edges a.val (by omega)] at h1
    rw [show tokens ([] : List (Fin v)) = [] from rfl] at h1
    have h2 := RIn.step (s_check_nil none [] (rep (arity t)) (rep vertex.val) [] [] [])
    have h3 := scan_empty_run (arity t) vertex.val none [] []
    have h4 := RIn.step (s_finish_some none [] [] [] (rep vertex.val) [] [] [])
    have h5 := clearB_run [] (some true) [] [] (rep vertex.val) [] [] []
    rw [hpos]
    have := (h1.trans (h2.trans (h3.trans (h4.trans h5))))
    exact this.mono (by simp only [List.length_nil]; nlinarith)

#print axioms skip_run
#print axioms iter_clear_run
#print axioms scan_run
#print axioms fold_edge
#print axioms take_drop_flatten
#print axioms physical_position_lookup

end Paper2.YaoPositionLookup
