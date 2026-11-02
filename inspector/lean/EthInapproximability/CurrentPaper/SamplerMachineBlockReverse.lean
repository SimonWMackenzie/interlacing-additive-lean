import EthInapproximability.CurrentPaper.SamplerMachineFieldTable

/-!
# Physical reversal inside fixed-width sampler symbols

Source: locked v8 Appendix E, `lem:exact-families`, and Appendix B's
MSB-first stored word code. A fixed six-stack controller preserves the unary
symbol width, consumes a concatenation of complete blocks, and reverses
the bits inside each block without changing block order.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineBlockReverse

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | check | scan | restore | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 6
abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (none, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .check => peek 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (load (fun _ => initial) (goto (fun _ => .scan)))
        (load (fun _ => initial) (goto (fun _ => .finish))))
  | .scan => pop 1 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (pop 0 (fun s b => (s.1, b))
          (branch (fun s => s.2.isSome)
            (push 2 (fun s => s.1.getD false)
              (push 3 (fun s => s.2.getD false) (goto (fun _ => .scan))))
            (load (fun _ => initial) (goto (fun _ => .restore)))))
        (load (fun _ => initial) (goto (fun _ => .restore))))
  | .restore => pop 3 (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (pop 2 (fun s b => (b, s.2))
          (push 1 (fun s => s.1.getD false)
            (push 4 (fun s => s.2.getD false) (goto (fun _ => .restore)))))
        (load (fun _ => initial) (goto (fun _ => .check))))
  | .finish => pop 4 (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push 5 (fun s => s.2.getD false) (goto (fun _ => .finish)))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control)
    (input width saved scratch acc output : List Bool) : Config :=
  ⟨l, s, ![input, width, saved, scratch, acc, output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add (t u : ℕ) (c : Config) :
    run (t + u) c = run t (run u c) := Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_check_cons (s : Control) (b : Bool)
    (xs width saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .check) s (b :: xs) width saved scratch acc output) =
      some (cfg (some .scan) initial (b :: xs) width saved scratch acc output) := by
  rfl

private theorem step_check_nil (s : Control)
    (width saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .check) s [] width saved scratch acc output) =
      some (cfg (some .finish) initial [] width saved scratch acc output) := by
  rfl

private theorem step_scan_cons (s : Control) (u b : Bool)
    (width xs saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .scan) s (b :: xs) (u :: width) saved scratch acc output) =
      some (cfg (some .scan) (some u, some b) xs width (u :: saved)
        (b :: scratch) acc output) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Control)
    (xs saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .scan) s xs [] saved scratch acc output) =
      some (cfg (some .restore) initial xs [] saved scratch acc output) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_restore_cons (s : Control) (u b : Bool)
    (xs width saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .restore) s xs width (u :: saved)
      (b :: scratch) acc output) =
      some (cfg (some .restore) (some u, some b) xs (u :: width)
        saved scratch (b :: acc) output) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Control)
    (xs width acc output : List Bool) :
    TM2.step program (cfg (some .restore) s xs width [] [] acc output) =
      some (cfg (some .check) initial xs width [] [] acc output) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_finish_cons (s : Control) (b : Bool)
    (xs width saved scratch acc output : List Bool) :
    TM2.step program (cfg (some .finish) s xs width saved scratch
      (b :: acc) output) =
      some (cfg (some .finish) (s.1, some b) xs width saved scratch
        acc (b :: output)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_finish_nil (s : Control)
    (xs width saved scratch output : List Bool) :
    TM2.step program (cfg (some .finish) s xs width saved scratch [] output) =
      some (cfg none initial xs width saved scratch [] output) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem scan_run (s : Control) (width chunk suffix saved scratch acc output : List Bool)
    (h : width.length = chunk.length) :
    run (width.length + 1)
      (cfg (some .scan) s (chunk ++ suffix) width saved scratch acc output) =
    cfg (some .restore) initial suffix [] (width.reverse ++ saved)
      (chunk.reverse ++ scratch) acc output := by
  induction width generalizing chunk s saved scratch with
  | nil =>
      have hc : chunk = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
      subst chunk
      simpa using run_succ (step_scan_nil s suffix saved scratch acc output) 0
  | cons u width ih =>
      cases chunk with
      | nil => simp at h
      | cons b chunk =>
          have hh : width.length = chunk.length := by simpa using h
          rw [List.cons_append, List.length_cons,
            show width.length + 1 + 1 = (width.length + 1) + 1 by omega,
            run_succ (step_scan_cons s u b width (chunk ++ suffix) saved scratch acc output)]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih (some u, some b) chunk (u :: saved) (b :: scratch) hh

theorem restore_run (s : Control) (xs width saved scratch acc output : List Bool)
    (h : saved.length = scratch.length) :
    run (scratch.length + 1)
      (cfg (some .restore) s xs width saved scratch acc output) =
    cfg (some .check) initial xs (saved.reverse ++ width) [] []
      (scratch.reverse ++ acc) output := by
  induction scratch generalizing saved s width acc with
  | nil =>
      have hs : saved = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst saved
      simpa using run_succ (step_restore_nil s xs width acc output) 0
  | cons b scratch ih =>
      cases saved with
      | nil => simp at h
      | cons u saved =>
          have hh : saved.length = scratch.length := by simpa using h
          rw [List.length_cons,
            show scratch.length + 1 + 1 = (scratch.length + 1) + 1 by omega,
            run_succ (step_restore_cons s u b xs width saved scratch acc output)]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih (some u, some b) (u :: width) saved (b :: acc) hh

theorem block_run (width chunk suffix acc output : List Bool)
    (h : width.length = chunk.length) (hw : 0 < width.length) :
    run (2 * width.length + 3)
      (cfg (some .check) initial (chunk ++ suffix) width [] [] acc output) =
    cfg (some .check) initial suffix width [] [] (chunk ++ acc) output := by
  have hchunk : chunk ≠ [] := by
    intro he
    have hz : width.length = 0 := by simpa [he] using h
    omega
  cases chunk with
  | nil => exact (hchunk rfl).elim
  | cons b chunk =>
      have hc : run 1 (cfg (some .check) initial
          ((b :: chunk) ++ suffix) width [] [] acc output) =
          cfg (some .scan) initial ((b :: chunk) ++ suffix) width [] [] acc output := by
        simpa using run_succ
          (step_check_cons initial b (chunk ++ suffix) width [] [] acc output) 0
      have hs := scan_run initial width (b :: chunk) suffix [] [] acc output h
      have hr := restore_run initial suffix [] width.reverse (b :: chunk).reverse
        acc output (by simp [h])
      simp only [List.reverse_reverse, List.append_nil] at hr
      rw [show 2 * width.length + 3 =
          (width.length + 1) + ((width.length + 1) + 1) by omega,
        run_add (width.length + 1) ((width.length + 1) + 1),
        run_add (width.length + 1) 1, hc, hs]
      simpa only [List.append_nil, List.length_reverse, h] using hr

def blockStep (a : ℕ) : ℕ := 2 * a + 3

theorem blocks_run (a : ℕ) (ha : 0 < a) (blocks : List (List Bool))
    (hblocks : ∀ b ∈ blocks, b.length = a) (acc output : List Bool) :
    run (blocks.length * blockStep a)
      (cfg (some .check) initial blocks.flatten (List.replicate a true)
        [] [] acc output) =
      cfg (some .check) initial [] (List.replicate a true) [] []
        (blocks.reverse.flatten ++ acc) output := by
  induction blocks generalizing acc with
  | nil => simp [run]
  | cons b blocks ih =>
      have hb : b.length = a := hblocks b (List.mem_cons_self)
      have htail : ∀ c ∈ blocks, c.length = a := by
        intro c hc
        exact hblocks c (List.mem_cons_of_mem b hc)
      have hstep := block_run (List.replicate a true) b blocks.flatten acc output
        (by simpa [hb]) (by simpa using ha)
      have hstep' : run (blockStep a)
          (cfg (some .check) initial (b ++ blocks.flatten)
            (List.replicate a true) [] [] acc output) =
          cfg (some .check) initial blocks.flatten (List.replicate a true)
            [] [] (b ++ acc) output := by simpa [blockStep] using hstep
      rw [List.length_cons, show (blocks.length + 1) * blockStep a =
          blocks.length * blockStep a + blockStep a by ring,
        run_add (blocks.length * blockStep a) (blockStep a), List.flatten_cons,
        hstep']
      simpa only [List.reverse_cons, List.flatten_append, List.flatten_singleton,
        List.append_assoc] using ih htail (b ++ acc)

theorem finish_run (s : Control) (xs width saved scratch acc output : List Bool) :
    run (acc.length + 1)
      (cfg (some .finish) s xs width saved scratch acc output) =
    cfg none initial xs width saved scratch [] (acc.reverse ++ output) := by
  induction acc generalizing s output with
  | nil => simpa using run_succ (step_finish_nil s xs width saved scratch output) 0
  | cons b acc ih =>
      rw [List.length_cons, run_succ
        (step_finish_cons s b xs width saved scratch acc output)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, some b) (b :: output)

theorem run_blocks (a : ℕ) (ha : 0 < a) (blocks : List (List Bool))
    (hblocks : ∀ b ∈ blocks, b.length = a) :
    run (blocks.length * blockStep a + (blocks.reverse.flatten).length + 2)
      (cfg (some .check) initial blocks.flatten (List.replicate a true)
        [] [] [] []) =
      cfg none initial [] (List.replicate a true) [] [] []
        (blocks.map List.reverse).flatten := by
  have hprocess := blocks_run a ha blocks hblocks [] []
  simp only [List.append_nil] at hprocess
  have hc : run 1 (cfg (some .check) initial []
      (List.replicate a true) [] [] blocks.reverse.flatten []) =
      cfg (some .finish) initial [] (List.replicate a true)
        [] [] blocks.reverse.flatten [] := by
    simpa using run_succ (step_check_nil initial (List.replicate a true)
      [] [] blocks.reverse.flatten []) 0
  have hf := finish_run initial [] (List.replicate a true)
    [] [] blocks.reverse.flatten []
  rw [show blocks.length * blockStep a + (blocks.reverse.flatten).length + 2 =
      ((blocks.reverse.flatten).length + 1) +
        (1 + blocks.length * blockStep a) by omega,
    run_add ((blocks.reverse.flatten).length + 1)
      (1 + blocks.length * blockStep a),
    run_add 1 (blocks.length * blockStep a), hprocess, hc, hf]
  simp [List.reverse_flatten]

end EthInapproximability.CurrentPaper.SamplerMachineBlockReverse
