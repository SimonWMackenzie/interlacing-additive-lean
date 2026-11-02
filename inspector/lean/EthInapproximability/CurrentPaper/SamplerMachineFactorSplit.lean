import EthInapproximability.CurrentPaper.SamplerMachineFactorPrepare

/-!
# Splitting one factor-pair counter by actual stack operations

Source: locked v8 Appendix E, `lem:exact-families`, finite factor search.
The candidate word supplies the width of the first factor. Four finite
passes copy both factors and restore the original pair counter and candidate.
Finite Boolean flags record whether each factor has a nonconstant term.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFactorSplit

open Turing Turing.TM2.Stmt BitMachineEncoding
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

inductive Stack where
  | candidate | counter | factorU | factorV | savedC | savedQ
  deriving DecidableEq, Fintype

inductive Label where
  | scanU | scanV | restoreV | restoreU
  deriving DecidableEq, Fintype

structure Control where
  foundU : Bool
  foundV : Bool
  seen : Bool
  readC : Option Bool
  readQ : Option Bool
  deriving DecidableEq, Fintype

def flags (u v : Bool) : Control := ⟨u, v, false, none, none⟩

def initial : Control := flags false false

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scanU => pop .candidate (fun s b => { s with readC := b })
      (branch (fun s => s.readC.isSome)
        (pop .counter (fun s b => { s with readQ := b })
          (push .savedC (fun s => s.readC.getD false)
            (push .savedQ (fun s => s.readQ.getD false)
              (load (fun s => ⟨s.foundU || (s.seen && s.readQ.getD false),
                s.foundV, true, none, none⟩) (goto (fun _ => .scanU))))))
        (load (fun s => flags s.foundU s.foundV) (goto (fun _ => .scanV))))
  | .scanV => pop .counter (fun s b => { s with readQ := b })
      (branch (fun s => s.readQ.isSome)
        (push .savedQ (fun s => s.readQ.getD false)
          (load (fun s => ⟨s.foundU, s.foundV || (s.seen && s.readQ.getD false),
            true, none, none⟩) (goto (fun _ => .scanV))))
        (load (fun s => flags s.foundU s.foundV) (goto (fun _ => .restoreV))))
  | .restoreV => pop .savedC (fun s b => { s with readC := b })
      (branch (fun s => s.readC.isSome)
        (pop .savedQ (fun s b => { s with readQ := b })
          (push .candidate (fun s => s.readC.getD false)
            (push .counter (fun s => s.readQ.getD false)
              (push .factorV (fun s => s.readQ.getD false) (goto (fun _ => .restoreV))))))
        (load (fun s => flags s.foundU s.foundV) (goto (fun _ => .restoreU))))
  | .restoreU => pop .savedQ (fun s b => { s with readQ := b })
      (branch (fun s => s.readQ.isSome)
        (push .counter (fun s => s.readQ.getD false)
          (push .factorU (fun s => s.readQ.getD false) (goto (fun _ => .restoreU))))
        (load (fun s => flags s.foundU s.foundV) halt))

def stackContents (c q u v savedC savedQ : List Bool) : Stack → List Bool
  | .candidate => c | .counter => q | .factorU => u | .factorV => v
  | .savedC => savedC | .savedQ => savedQ

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def cfg (l : Option Label) (s : Control) (c q u v savedC savedQ : List Bool) : Config :=
  ⟨l, s, stackContents c q u v savedC savedQ⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

def scanFlag (seen : Bool) (q : List Bool) : Bool :=
  if seen then q.any id else q.tail.any id

@[simp] theorem scanFlag_nil (seen : Bool) : scanFlag seen [] = false := by
  cases seen <;> rfl

theorem scanFlag_cons (seen b : Bool) (q : List Bool) :
    scanFlag seen (b :: q) = ((seen && b) || scanFlag true q) := by
  cases seen <;> rfl

private theorem step_scanU_cons (s : Control) (a b : Bool)
    (c q u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .scanU) s (a :: c) (b :: q) u v savedC savedQ) =
      some (cfg (some .scanU)
        ⟨s.foundU || (s.seen && b), s.foundV, true, none, none⟩
        c q u v (a :: savedC) (b :: savedQ)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanU_nil (s : Control) (q u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .scanU) s [] q u v savedC savedQ) =
      some (cfg (some .scanV) (flags s.foundU s.foundV) [] q u v savedC savedQ) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanV_cons (s : Control) (b : Bool)
    (c q u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .scanV) s c (b :: q) u v savedC savedQ) =
      some (cfg (some .scanV)
        ⟨s.foundU, s.foundV || (s.seen && b), true, none, none⟩
        c q u v savedC (b :: savedQ)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanV_nil (s : Control) (c u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .scanV) s c [] u v savedC savedQ) =
      some (cfg (some .restoreV) (flags s.foundU s.foundV) c [] u v savedC savedQ) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreV_cons (s : Control) (a b : Bool)
    (c q u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .restoreV) s c q u v (a :: savedC) (b :: savedQ)) =
      some (cfg (some .restoreV) { s with readC := some a, readQ := some b }
        (a :: c) (b :: q) u (b :: v) savedC savedQ) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreV_nil (s : Control) (c q u v savedQ : List Bool) :
    TM2.step program (cfg (some .restoreV) s c q u v [] savedQ) =
      some (cfg (some .restoreU) (flags s.foundU s.foundV) c q u v [] savedQ) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreU_cons (s : Control) (b : Bool)
    (c q u v savedC savedQ : List Bool) :
    TM2.step program (cfg (some .restoreU) s c q u v savedC (b :: savedQ)) =
      some (cfg (some .restoreU) { s with readQ := some b }
        c (b :: q) (b :: u) v savedC savedQ) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreU_nil (s : Control) (c q u v savedC : List Bool) :
    TM2.step program (cfg (some .restoreU) s c q u v savedC []) =
      some (cfg none (flags s.foundU s.foundV) c q u v savedC []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

theorem scanU_run (s : Control) (c us vs u v savedC savedQ : List Bool)
    (hlen : c.length = us.length) :
    run (c.length + 1) (cfg (some .scanU) s c (us ++ vs) u v savedC savedQ) =
      cfg (some .scanV) (flags (s.foundU || scanFlag s.seen us) s.foundV)
        [] vs u v (c.reverse ++ savedC) (us.reverse ++ savedQ) := by
  induction c generalizing s us savedC savedQ with
  | nil =>
      have hu : us = [] := List.length_eq_zero_iff.mp hlen.symm
      subst us
      simpa using run_succ (step_scanU_nil s vs u v savedC savedQ) 0
  | cons a c ih =>
      cases us with
      | nil => simp at hlen
      | cons b us =>
          have hl : c.length = us.length := by simpa using hlen
          rw [List.length_cons, List.cons_append,
            run_succ (step_scanU_cons s a b c (us ++ vs) u v savedC savedQ)]
          simpa only [scanFlag_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Bool.or_assoc] using
              ih ⟨s.foundU || (s.seen && b), s.foundV, true, none, none⟩
                us (a :: savedC) (b :: savedQ) hl

theorem scanV_run (s : Control) (c q u v savedC savedQ : List Bool) :
    run (q.length + 1) (cfg (some .scanV) s c q u v savedC savedQ) =
      cfg (some .restoreV) (flags s.foundU (s.foundV || scanFlag s.seen q))
        c [] u v savedC (q.reverse ++ savedQ) := by
  induction q generalizing s savedQ with
  | nil => simpa using run_succ (step_scanV_nil s c u v savedC savedQ) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_scanV_cons s b c q u v savedC savedQ)]
      simpa only [scanFlag_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Bool.or_assoc] using
          ih ⟨s.foundU, s.foundV || (s.seen && b), true, none, none⟩ (b :: savedQ)

theorem restoreV_run (s : Control) (c q u v savedC front rest : List Bool)
    (hlen : savedC.length = front.length) :
    run (savedC.length + 1) (cfg (some .restoreV) s c q u v savedC (front ++ rest)) =
      cfg (some .restoreU) (flags s.foundU s.foundV)
        (savedC.reverse ++ c) (front.reverse ++ q) u (front.reverse ++ v) [] rest := by
  induction savedC generalizing s c q v front with
  | nil =>
      have hp : front = [] := List.length_eq_zero_iff.mp hlen.symm
      subst front
      simpa using run_succ (step_restoreV_nil s c q u v rest) 0
  | cons a savedC ih =>
      cases front with
      | nil => simp at hlen
      | cons b front =>
          have hl : savedC.length = front.length := by simpa using hlen
          rw [List.length_cons, List.cons_append,
            run_succ (step_restoreV_cons s a b c q u v savedC (front ++ rest))]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih { s with readC := some a, readQ := some b }
              (a :: c) (b :: q) (b :: v) front hl

theorem restoreU_run (s : Control) (c q u v savedC savedQ : List Bool) :
    run (savedQ.length + 1) (cfg (some .restoreU) s c q u v savedC savedQ) =
      cfg none (flags s.foundU s.foundV) c (savedQ.reverse ++ q)
        (savedQ.reverse ++ u) v savedC [] := by
  induction savedQ generalizing s q u with
  | nil => simpa using run_succ (step_restoreU_nil s c q u v savedC) 0
  | cons b savedQ ih =>
      rw [List.length_cons, run_succ (step_restoreU_cons s b c q u v savedC savedQ)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih { s with readQ := some b } (b :: q) (b :: u)

/-- The complete split preserves candidate and counter and returns copied
factors together with their two nonconstant flags. -/
theorem split_run (c u v : List Bool) (hcu : c.length = u.length)
    (hcv : c.length = v.length) :
    run (4 * c.length + 4)
      (cfg (some .scanU) (flags false false) c (u ++ v) [] [] [] []) =
      cfg none (flags (u.tail.any id) (v.tail.any id)) c (u ++ v) u v [] [] := by
  have h1 := scanU_run (flags false false) c u v [] [] [] [] hcu
  simp only [flags, scanFlag, Bool.false_eq_true, if_false, Bool.false_or,
    List.append_nil] at h1
  have h2 := scanV_run (flags (u.tail.any id) false) [] v [] [] c.reverse u.reverse
  simp only [flags, scanFlag, Bool.false_eq_true, if_false, Bool.false_or, ← hcv] at h2
  have h3 := restoreV_run (flags (u.tail.any id) (v.tail.any id)) [] [] [] []
    c.reverse v.reverse u.reverse (by simpa using hcv)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3
  have h4 := restoreU_run (flags (u.tail.any id) (v.tail.any id)) c v [] v [] u.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, ← hcu] at h4
  simp only [flags] at h3 h4
  rw [show 4 * c.length + 4 = (c.length + 1) +
    ((c.length + 1) + ((c.length + 1) + (c.length + 1))) by omega]
  rw [run_add (c.length + 1) ((c.length + 1) + ((c.length + 1) + (c.length + 1))),
    run_add (c.length + 1) ((c.length + 1) + (c.length + 1)),
    run_add (c.length + 1) (c.length + 1)]
  simp only [flags] at ⊢
  rw [h1, h2, h3, h4]

theorem split_coefficients {n : ℕ} (c u v : BinaryWord n) :
    run (4 * n + 4)
      (cfg (some .scanU) (flags false false) (encodeWord c)
        (encodeWord u ++ encodeWord v) [] [] [] []) =
      cfg none (flags (decide (Nonconstant u)) (decide (Nonconstant v)))
        (encodeWord c) (encodeWord u ++ encodeWord v) (encodeWord u) (encodeWord v) [] [] := by
  have heq {m : ℕ} (w : BinaryWord m) :
      ((encodeWord w).tail.any id) = decide (Nonconstant w) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.decide_iff]
    simpa only [List.drop_one] using (nonconstant_iff_tail_any w).symm
  simpa only [encodeWord_length, heq] using
    split_run (encodeWord c) (encodeWord u) (encodeWord v) (by simp) (by simp)

end EthInapproximability.CurrentPaper.SamplerMachineFactorSplit
