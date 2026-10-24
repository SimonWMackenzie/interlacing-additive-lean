import EthInapproximability.CurrentPaper.SamplerMachineFactorTest

/-!
# Preparing trial-factor inputs by explicit stack operations

Source: locked v8 Appendix E, `lem:exact-families`, finite polynomial
factor testing. This fixed nine-stack program preserves the three input
coefficient words while constructing every padded input used by the
factor-product comparison controller. It performs no field arithmetic.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFactorPrepare

open Turing Turing.TM2.Stmt BitMachineEncoding
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

inductive Stack where
  | candidate | factorU | factorV | target | paddedU | reversedV | zeroA | zeroM | work
  deriving DecidableEq, Fintype

inductive Label where
  | scanC | restoreC | scanU | restoreU | scanV | restoreV
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scanC => pop .candidate (fun _ b => b)
      (branch Option.isSome
        (push .work (fun b => b.getD false)
          (push .target (fun _ => false)
            (push .paddedU (fun _ => false)
              (push .zeroA (fun _ => false) (push .zeroA (fun _ => false)
                (push .zeroM (fun _ => false) (push .zeroM (fun _ => false)
                  (goto (fun _ => .scanC)))))))))
        (pop .target (fun _ _ => none)
          (push .target (fun _ => true) (goto (fun _ => .restoreC)))))
  | .restoreC => pop .work (fun _ b => b)
      (branch Option.isSome
        (push .candidate (fun b => b.getD false)
          (push .target (fun b => b.getD false) (goto (fun _ => .restoreC))))
        (goto (fun _ => .scanU)))
  | .scanU => pop .factorU (fun _ b => b)
      (branch Option.isSome
        (push .work (fun b => b.getD false) (goto (fun _ => .scanU)))
        (goto (fun _ => .restoreU)))
  | .restoreU => pop .work (fun _ b => b)
      (branch Option.isSome
        (push .factorU (fun b => b.getD false)
          (push .paddedU (fun b => b.getD false) (goto (fun _ => .restoreU))))
        (goto (fun _ => .scanV)))
  | .scanV => pop .factorV (fun _ b => b)
      (branch Option.isSome
        (push .work (fun b => b.getD false)
          (push .reversedV (fun b => b.getD false) (goto (fun _ => .scanV))))
        (goto (fun _ => .restoreV)))
  | .restoreV => pop .work (fun _ b => b)
      (branch Option.isSome
        (push .factorV (fun b => b.getD false)
          (push .reversedV (fun _ => false) (goto (fun _ => .restoreV))))
        halt)

def stackContents (c u v target padded multiplier zeroA zeroM work : List Bool) :
    Stack → List Bool
  | .candidate => c | .factorU => u | .factorV => v | .target => target
  | .paddedU => padded | .reversedV => multiplier | .zeroA => zeroA
  | .zeroM => zeroM | .work => work

def cfg (l : Option Label) (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) : Config :=
  ⟨l, s, stackContents c u v target padded multiplier zeroA zeroM work⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_scanC_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanC) s (b :: c) u v target padded multiplier zeroA zeroM work) =
      some (cfg (some .scanC) (some b) c u v (false :: target) (false :: padded) multiplier
        (false :: false :: zeroA) (false :: false :: zeroM) (b :: work)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanC_nil (s : Control)
    (u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanC) s [] u v target padded multiplier zeroA zeroM work) =
      some (cfg (some .restoreC) none [] u v (true :: target.tail) padded multiplier
        zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreC_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .restoreC) s c u v target padded multiplier zeroA zeroM (b :: work)) =
      some (cfg (some .restoreC) (some b) (b :: c) u v (b :: target) padded multiplier
        zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreC_nil (s : Control)
    (c u v target padded multiplier zeroA zeroM : List Bool) :
    TM2.step program (cfg (some .restoreC) s c u v target padded multiplier zeroA zeroM []) =
      some (cfg (some .scanU) none c u v target padded multiplier zeroA zeroM []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanU_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanU) s c (b :: u) v target padded multiplier zeroA zeroM work) =
      some (cfg (some .scanU) (some b) c u v target padded multiplier zeroA zeroM (b :: work)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanU_nil (s : Control)
    (c v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanU) s c [] v target padded multiplier zeroA zeroM work) =
      some (cfg (some .restoreU) none c [] v target padded multiplier zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreU_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .restoreU) s c u v target padded multiplier zeroA zeroM (b :: work)) =
      some (cfg (some .restoreU) (some b) c (b :: u) v target (b :: padded) multiplier
        zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreU_nil (s : Control)
    (c u v target padded multiplier zeroA zeroM : List Bool) :
    TM2.step program (cfg (some .restoreU) s c u v target padded multiplier zeroA zeroM []) =
      some (cfg (some .scanV) none c u v target padded multiplier zeroA zeroM []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanV_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanV) s c u (b :: v) target padded multiplier zeroA zeroM work) =
      some (cfg (some .scanV) (some b) c u v target padded (b :: multiplier) zeroA zeroM (b :: work)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scanV_nil (s : Control)
    (c u target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .scanV) s c u [] target padded multiplier zeroA zeroM work) =
      some (cfg (some .restoreV) none c u [] target padded multiplier zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreV_cons (s : Control) (b : Bool)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    TM2.step program (cfg (some .restoreV) s c u v target padded multiplier zeroA zeroM (b :: work)) =
      some (cfg (some .restoreV) (some b) c u (b :: v) target padded (false :: multiplier)
        zeroA zeroM work) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restoreV_nil (s : Control)
    (c u v target padded multiplier zeroA zeroM : List Bool) :
    TM2.step program (cfg (some .restoreV) s c u v target padded multiplier zeroA zeroM []) =
      some (cfg none none c u v target padded multiplier zeroA zeroM []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, stackContents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

theorem scanC_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (c.length + 1) (cfg (some .scanC) s c u v target padded multiplier zeroA zeroM work) =
      cfg (some .restoreC) none [] u v
        (true :: (List.replicate c.length false ++ target).tail)
        (List.replicate c.length false ++ padded) multiplier
        (List.replicate (2 * c.length) false ++ zeroA)
        (List.replicate (2 * c.length) false ++ zeroM) (c.reverse ++ work) := by
  induction c generalizing s target padded zeroA zeroM work with
  | nil => simpa using run_succ (step_scanC_nil s u v target padded multiplier zeroA zeroM work) 0
  | cons b c ih =>
      rw [List.length_cons, run_succ (step_scanC_cons s b c u v target padded multiplier zeroA zeroM work)]
      have hrep (xs : List Bool) :
          List.replicate (2 * c.length) false ++ false :: false :: xs =
            List.replicate (2 * (c.length + 1)) false ++ xs := by
        rw [show 2 * (c.length + 1) = 2 * c.length + 2 by omega, List.replicate_add]
        simp
      simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append, List.reverse_cons, hrep] using
          ih (some b) (false :: target) (false :: padded)
            (false :: false :: zeroA) (false :: false :: zeroM) (b :: work)

theorem restoreC_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (work.length + 1) (cfg (some .restoreC) s c u v target padded multiplier zeroA zeroM work) =
      cfg (some .scanU) none (work.reverse ++ c) u v (work.reverse ++ target)
        padded multiplier zeroA zeroM [] := by
  induction work generalizing s c target with
  | nil => simpa using run_succ (step_restoreC_nil s c u v target padded multiplier zeroA zeroM) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restoreC_cons s b c u v target padded multiplier zeroA zeroM work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some b) (b :: c) (b :: target)

theorem scanU_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (u.length + 1) (cfg (some .scanU) s c u v target padded multiplier zeroA zeroM work) =
      cfg (some .restoreU) none c [] v target padded multiplier zeroA zeroM (u.reverse ++ work) := by
  induction u generalizing s work with
  | nil => simpa using run_succ (step_scanU_nil s c v target padded multiplier zeroA zeroM work) 0
  | cons b u ih =>
      rw [List.length_cons, run_succ (step_scanU_cons s b c u v target padded multiplier zeroA zeroM work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some b) (b :: work)

theorem restoreU_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (work.length + 1) (cfg (some .restoreU) s c u v target padded multiplier zeroA zeroM work) =
      cfg (some .scanV) none c (work.reverse ++ u) v target
        (work.reverse ++ padded) multiplier zeroA zeroM [] := by
  induction work generalizing s u padded with
  | nil => simpa using run_succ (step_restoreU_nil s c u v target padded multiplier zeroA zeroM) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restoreU_cons s b c u v target padded multiplier zeroA zeroM work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some b) (b :: u) (b :: padded)

theorem scanV_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (v.length + 1) (cfg (some .scanV) s c u v target padded multiplier zeroA zeroM work) =
      cfg (some .restoreV) none c u [] target padded (v.reverse ++ multiplier)
        zeroA zeroM (v.reverse ++ work) := by
  induction v generalizing s multiplier work with
  | nil => simpa using run_succ (step_scanV_nil s c u target padded multiplier zeroA zeroM work) 0
  | cons b v ih =>
      rw [List.length_cons, run_succ (step_scanV_cons s b c u v target padded multiplier zeroA zeroM work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some b) (b :: multiplier) (b :: work)

theorem restoreV_run (s : Control)
    (c u v target padded multiplier zeroA zeroM work : List Bool) :
    run (work.length + 1) (cfg (some .restoreV) s c u v target padded multiplier zeroA zeroM work) =
      cfg none none c u (work.reverse ++ v) target padded
        (List.replicate work.length false ++ multiplier) zeroA zeroM [] := by
  induction work generalizing s v multiplier with
  | nil => simpa using run_succ (step_restoreV_nil s c u v target padded multiplier zeroA zeroM) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restoreV_cons s b c u v target padded multiplier zeroA zeroM work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, List.replicate_succ'] using
          ih (some b) (b :: v) (false :: multiplier)

theorem candidate_run (c u v : List Bool) :
    run (2 * c.length + 2) (cfg (some .scanC) none c u v [] [] [] [] [] []) =
      cfg (some .scanU) none c u v
        (c ++ true :: List.replicate (c.length - 1) false)
        (List.replicate c.length false) [] (List.replicate (2 * c.length) false)
        (List.replicate (2 * c.length) false) [] := by
  have ht (n : ℕ) : (List.replicate n false).tail = List.replicate (n - 1) false := by
    cases n <;> simp [List.replicate_succ]
  have hs := scanC_run none c u v [] [] [] [] [] []
  simp only [List.append_nil, ht] at hs
  have hr := restoreC_run none [] u v (true :: List.replicate (c.length - 1) false)
    (List.replicate c.length false) [] (List.replicate (2 * c.length) false)
    (List.replicate (2 * c.length) false) c.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * c.length + 2 = (c.length + 1) + (c.length + 1) by omega,
    run_add, hs, hr]

theorem factorU_run (c u v target padded multiplier zeroA zeroM : List Bool) :
    run (2 * u.length + 2) (cfg (some .scanU) none c u v target padded multiplier zeroA zeroM []) =
      cfg (some .scanV) none c u v target (u ++ padded) multiplier zeroA zeroM [] := by
  have hs := scanU_run none c u v target padded multiplier zeroA zeroM []
  simp only [List.append_nil] at hs
  have hr := restoreU_run none c [] v target padded multiplier zeroA zeroM u.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * u.length + 2 = (u.length + 1) + (u.length + 1) by omega,
    run_add, hs, hr]

theorem factorV_run (c u v target padded zeroA zeroM : List Bool) :
    run (2 * v.length + 2) (cfg (some .scanV) none c u v target padded [] zeroA zeroM []) =
      cfg none none c u v target padded
        (List.replicate v.length false ++ v.reverse) zeroA zeroM [] := by
  have hs := scanV_run none c u v target padded [] zeroA zeroM []
  simp only [List.append_nil] at hs
  have hr := restoreV_run none c u [] target padded v.reverse zeroA zeroM v.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * v.length + 2 = (v.length + 1) + (v.length + 1) by omega,
    run_add, hs, hr]

/-- All copying, reversal and zero-padding is paid for by the six passes. -/
theorem prepare_run (c u v : List Bool) :
    run (2 * c.length + 2 * u.length + 2 * v.length + 6)
      (cfg (some .scanC) none c u v [] [] [] [] [] []) =
      cfg none none c u v (c ++ true :: List.replicate (c.length - 1) false)
        (u ++ List.replicate c.length false)
        (List.replicate v.length false ++ v.reverse)
        (List.replicate (2 * c.length) false) (List.replicate (2 * c.length) false) [] := by
  rw [show 2 * c.length + 2 * u.length + 2 * v.length + 6 =
    (2 * v.length + 2) + ((2 * u.length + 2) + (2 * c.length + 2)) by omega]
  rw [run_add (2 * v.length + 2) ((2 * u.length + 2) + (2 * c.length + 2)),
    run_add (2 * u.length + 2) (2 * c.length + 2), candidate_run, factorU_run, factorV_run]

theorem encode_padded {n : ℕ} (u : BinaryWord n) :
    encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val) =
      encodeWord u ++ List.replicate n false := by
  apply List.ext_getElem
  · simp only [encodeWord_length, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    by_cases hit : i < n
    · simp [encodeWord, rawCoeff, hit, List.getElem_append]
    · simp [encodeWord, rawCoeff, hit, List.getElem_append, encodeBit]

theorem encode_monic_padded {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val) =
      encodeWord c ++ true :: List.replicate (n - 1) false := by
  apply List.ext_getElem
  · simp only [encodeWord_length, List.length_append, List.length_cons, List.length_replicate]
    omega
  · intro i hi hj
    by_cases hit : i < n
    · simp [encodeWord, monicCoeff, hit, List.getElem_append]
    · by_cases heq : i = n
      · subst i
        simp [encodeWord, monicCoeff, List.getElem_append, encodeBit]
      · have hgt : 0 < i - n := by omega
        simp [encodeWord, monicCoeff, hit, heq, List.getElem_append, encodeBit,
          List.getElem_cons, hgt.ne']

/-- Exact typed inputs for the actual factor-product comparator, with every
original coefficient word preserved and the preparation scratch empty. -/
theorem prepare_coefficients {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) :
    run (6 * n + 6)
      (cfg (some .scanC) none (encodeWord c) (encodeWord u) (encodeWord v) [] [] [] [] [] []) =
      cfg none none (encodeWord c) (encodeWord u) (encodeWord v)
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) [] := by
  have h := prepare_run (encodeWord c) (encodeWord u) (encodeWord v)
  simp only [encodeWord_length] at h
  rw [show 6 * n + 6 = 2 * n + 2 * n + 2 * n + 6 by omega]
  simpa only [encode_monic_padded hn, encode_padded, List.reverse_append,
    List.reverse_replicate, encodeWord_zero] using h

end EthInapproximability.CurrentPaper.SamplerMachineFactorPrepare
