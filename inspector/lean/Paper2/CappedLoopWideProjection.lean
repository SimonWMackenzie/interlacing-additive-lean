import Paper2.CappedLoopDrain
import Paper2.RecursiveSamplingTape

/-!
Scratch physical projection of each public B-bit attempt word onto its
required b-bit low-order prefix, preserving the later-draw tape suffix.
All counters are unary stacks; the program's labels do not depend on B,b,R.
-/

namespace Paper2.CappedLoop.WideProjection

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | start | read | restoreB | skip | restorePad | restoreAttempts | prepend
  deriving DecidableEq, Fintype

abbrev Control := CappedLoop.Comparator.Control

/-- Stacks: 0 input/output tape, 1 unary b, 2 b scratch, 3 reverse
projected bits, 4 unary padding width, 5 unary attempts, 6 attempts scratch,
7 padding scratch. Stacks 8 and 9 are foreign. -/
def program : Label → TM2.Stmt (fun _ : Fin 10 => Bool) Label Control
  | .start =>
      pop 5 (fun s a => (a, s.2))
        (branch (fun s => s.1.isSome)
          (push 6 (fun _ => true) (goto (fun _ => .read)))
          (goto (fun _ => .restoreAttempts)))
  | .read =>
      pop 1 (fun s w => (w, s.2))
        (branch (fun s => s.1.isSome)
          (pop 0 (fun s bit => (bit, s.2))
            (branch (fun s => s.1.isSome)
              (push 2 (fun _ => true)
                (push 3 (fun s => s.1.getD false) (goto (fun _ => .read))))
              halt))
          (goto (fun _ => .restoreB)))
  | .restoreB =>
      pop 2 (fun s w => (w, s.2))
        (branch (fun s => s.1.isSome)
          (push 1 (fun _ => true) (goto (fun _ => .restoreB)))
          (goto (fun _ => .skip)))
  | .skip =>
      pop 4 (fun s w => (w, s.2))
        (branch (fun s => s.1.isSome)
          (pop 0 (fun s bit => (bit, s.2))
            (branch (fun s => s.1.isSome)
              (push 7 (fun _ => true) (goto (fun _ => .skip)))
              halt))
          (goto (fun _ => .restorePad)))
  | .restorePad =>
      pop 7 (fun s w => (w, s.2))
        (branch (fun s => s.1.isSome)
          (push 4 (fun _ => true) (goto (fun _ => .restorePad)))
          (goto (fun _ => .start)))
  | .restoreAttempts =>
      pop 6 (fun s a => (a, s.2))
        (branch (fun s => s.1.isSome)
          (push 5 (fun _ => true) (goto (fun _ => .restoreAttempts)))
          (goto (fun _ => .prepend)))
  | .prepend =>
      pop 3 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (push 0 (fun s => s.1.getD false) (goto (fun _ => .prepend)))
          halt)

def bank (tape width widthWork compact pad attempts attemptsWork padWork
    foreignA foreignB : List Bool) : Fin 10 → List Bool :=
  fun k => if k = 0 then tape else if k = 1 then width else
    if k = 2 then widthWork else if k = 3 then compact else
    if k = 4 then pad else if k = 5 then attempts else
    if k = 6 then attemptsWork else if k = 7 then padWork else
    if k = 8 then foreignA else foreignB

def cfg (l : Option Label) (v : Control)
    (tape width widthWork compact pad attempts attemptsWork padWork
      foreignA foreignB : List Bool) :
    TM2.Cfg (fun _ : Fin 10 => Bool) Label Control :=
  ⟨l, v, bank tape width widthWork compact pad attempts attemptsWork
    padWork foreignA foreignB⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem start_cons (v : Control) (tape width compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .start) v tape width [] compact pad
      (true :: attempts) attemptsWork [] foreignA foreignB) =
      some (cfg (some .read) (some true, v.2) tape width [] compact pad
        attempts (true :: attemptsWork) [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem start_nil (v : Control) (tape width compact pad attemptsWork
    foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .start) v tape width [] compact pad []
      attemptsWork [] foreignA foreignB) =
      some (cfg (some .restoreAttempts) (none, v.2) tape width [] compact pad []
        attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem read_cons (v : Control) (bit : Bool)
    (tape width work compact pad attempts attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .read) v (bit :: tape) (true :: width) work
      compact pad attempts attemptsWork [] foreignA foreignB) =
      some (cfg (some .read) (some bit, v.2) tape width (true :: work)
        (bit :: compact) pad attempts attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem read_nil (v : Control) (tape work compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .read) v tape [] work compact pad attempts
      attemptsWork [] foreignA foreignB) =
      some (cfg (some .restoreB) (none, v.2) tape [] work compact pad attempts
        attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem restoreB_cons (v : Control) (tape width work compact pad
    attempts attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restoreB) v tape width (true :: work)
      compact pad attempts attemptsWork [] foreignA foreignB) =
      some (cfg (some .restoreB) (some true, v.2) tape (true :: width) work
        compact pad attempts attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restoreB_nil (v : Control) (tape width compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restoreB) v tape width [] compact pad attempts
      attemptsWork [] foreignA foreignB) =
      some (cfg (some .skip) (none, v.2) tape width [] compact pad attempts
        attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem skip_cons (v : Control) (bit : Bool)
    (tape width compact pad work attempts attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .skip) v (bit :: tape) width [] compact
      (true :: pad) attempts attemptsWork work foreignA foreignB) =
      some (cfg (some .skip) (some bit, v.2) tape width [] compact pad
        attempts attemptsWork (true :: work) foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem skip_nil (v : Control) (tape width compact attempts
    attemptsWork work foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .skip) v tape width [] compact [] attempts
      attemptsWork work foreignA foreignB) =
      some (cfg (some .restorePad) (none, v.2) tape width [] compact [] attempts
        attemptsWork work foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem restorePad_cons (v : Control) (tape width compact pad work
    attempts attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restorePad) v tape width [] compact pad
      attempts attemptsWork (true :: work) foreignA foreignB) =
      some (cfg (some .restorePad) (some true, v.2) tape width [] compact
        (true :: pad) attempts attemptsWork work foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restorePad_nil (v : Control) (tape width compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restorePad) v tape width [] compact pad
      attempts attemptsWork [] foreignA foreignB) =
      some (cfg (some .start) (none, v.2) tape width [] compact pad attempts
        attemptsWork [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem unary_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem read_phase (v : Control) (block tape work compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    run (block.length + 1)
      (cfg (some .read) v (block ++ tape)
        (List.replicate block.length true) work compact pad attempts
        attemptsWork [] foreignA foreignB) =
      cfg (some .restoreB) (none, v.2) tape []
        (List.replicate block.length true ++ work)
        (block.reverse ++ compact) pad attempts attemptsWork [] foreignA foreignB := by
  induction block generalizing v work compact with
  | nil => simpa using (run_succ
      (read_nil v tape work compact pad attempts attemptsWork foreignA foreignB) 0)
  | cons bit block ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (read_cons v bit (block ++ tape)
        (List.replicate block.length true) work compact pad attempts
        attemptsWork foreignA foreignB), ih (some bit, v.2)]
      simp only [List.reverse_cons, List.append_assoc]
      rw [unary_comm]
      simp

theorem restoreB_phase (v : Control) (n : ℕ) (tape width compact pad attempts
    attemptsWork foreignA foreignB : List Bool) :
    run (n + 1)
      (cfg (some .restoreB) v tape width (List.replicate n true)
        compact pad attempts attemptsWork [] foreignA foreignB) =
      cfg (some .skip) (none, v.2) tape
        (List.replicate n true ++ width) [] compact pad attempts
        attemptsWork [] foreignA foreignB := by
  induction n generalizing v width with
  | zero => simpa using (run_succ
      (restoreB_nil v tape width compact pad attempts attemptsWork foreignA foreignB) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (restoreB_cons v tape width (List.replicate n true)
          compact pad attempts attemptsWork foreignA foreignB),
        ih (some true, v.2)]
      rw [unary_comm]
      simp

theorem skip_phase (v : Control) (padding tape width compact work attempts
    attemptsWork foreignA foreignB : List Bool) :
    run (padding.length + 1)
      (cfg (some .skip) v (padding ++ tape) width [] compact
        (List.replicate padding.length true) attempts attemptsWork work
        foreignA foreignB) =
      cfg (some .restorePad) (none, v.2) tape width [] compact []
        attempts attemptsWork
        (List.replicate padding.length true ++ work) foreignA foreignB := by
  induction padding generalizing v work with
  | nil => simpa using (run_succ
      (skip_nil v tape width compact attempts attemptsWork work foreignA foreignB) 0)
  | cons bit padding ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (skip_cons v bit (padding ++ tape) width compact
        (List.replicate padding.length true) work attempts attemptsWork
        foreignA foreignB), ih (some bit, v.2)]
      rw [unary_comm]

theorem restorePad_phase (v : Control) (n : ℕ) (tape width compact pad
    attempts attemptsWork foreignA foreignB : List Bool) :
    run (n + 1)
      (cfg (some .restorePad) v tape width [] compact pad attempts
        attemptsWork (List.replicate n true) foreignA foreignB) =
      cfg (some .start) (none, v.2) tape width [] compact
        (List.replicate n true ++ pad) attempts attemptsWork []
        foreignA foreignB := by
  induction n generalizing v pad with
  | zero => simpa using (run_succ
      (restorePad_nil v tape width compact pad attempts attemptsWork
        foreignA foreignB) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (restorePad_cons v tape width compact pad
          (List.replicate n true) attempts attemptsWork foreignA foreignB),
        ih (some true, v.2)]
      rw [unary_comm]
      simp

/-- One wide physical word: read exactly its `b` prefix bits, skip exactly
its padding, restore both widths and save one unary attempt symbol. -/
theorem one_word (v : Control) (pref padding rest compact attemptsWork
    attempts foreignA foreignB : List Bool) :
    run (2 * pref.length + 2 * padding.length + 5)
      (cfg (some .start) v (pref ++ padding ++ rest)
        (List.replicate pref.length true) [] compact
        (List.replicate padding.length true) (true :: attempts)
        attemptsWork [] foreignA foreignB) =
      cfg (some .start) (none, v.2) rest
        (List.replicate pref.length true) []
        (pref.reverse ++ compact) (List.replicate padding.length true)
        attempts (true :: attemptsWork) [] foreignA foreignB := by
  have hs := start_cons v (pref ++ padding ++ rest)
    (List.replicate pref.length true) compact
    (List.replicate padding.length true) attempts attemptsWork foreignA foreignB
  rw [List.append_assoc] at hs
  have hr := read_phase (some true, v.2) pref (padding ++ rest) []
    compact (List.replicate padding.length true) attempts
    (true :: attemptsWork) foreignA foreignB
  simp only [List.append_nil] at hr
  have hw := restoreB_phase (none, v.2) pref.length (padding ++ rest)
    [] (pref.reverse ++ compact) (List.replicate padding.length true)
    attempts (true :: attemptsWork) foreignA foreignB
  simp only [List.append_nil] at hw
  have hp := skip_phase (none, v.2) padding rest
    (List.replicate pref.length true) (pref.reverse ++ compact)
    [] attempts (true :: attemptsWork) foreignA foreignB
  simp only [List.append_nil] at hp
  have hq := restorePad_phase (none, v.2) padding.length rest
    (List.replicate pref.length true) (pref.reverse ++ compact)
    [] attempts (true :: attemptsWork) foreignA foreignB
  simp only [List.append_nil] at hq
  have h1 := (run_succ hs (pref.length + 1)).trans hr
  have h2 := (run_add h1 (pref.length + 1)).trans hw
  have h3 := (run_add h2 (padding.length + 1)).trans hp
  have h4 := (run_add h3 (padding.length + 1)).trans hq
  simpa only [List.append_assoc,
    show pref.length + 1 + 1 + (pref.length + 1) +
      (padding.length + 1) + (padding.length + 1) =
      2 * pref.length + 2 * padding.length + 5 by omega] using h4

private theorem restoreAttempts_cons (v : Control) (tape width compact pad
    attempts work foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restoreAttempts) v tape width [] compact pad
      attempts (true :: work) [] foreignA foreignB) =
      some (cfg (some .restoreAttempts) (some true, v.2) tape width [] compact
        pad (true :: attempts) work [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restoreAttempts_nil (v : Control) (tape width compact pad
    attempts foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .restoreAttempts) v tape width [] compact pad
      attempts [] [] foreignA foreignB) =
      some (cfg (some .prepend) (none, v.2) tape width [] compact pad attempts
        [] [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem restoreAttempts_phase (v : Control) (n : ℕ) (tape width compact pad
    attempts foreignA foreignB : List Bool) :
    run (n + 1)
      (cfg (some .restoreAttempts) v tape width [] compact pad attempts
        (List.replicate n true) [] foreignA foreignB) =
      cfg (some .prepend) (none, v.2) tape width [] compact pad
        (List.replicate n true ++ attempts) [] [] foreignA foreignB := by
  induction n generalizing v attempts with
  | zero => simpa using (run_succ
      (restoreAttempts_nil v tape width compact pad attempts foreignA foreignB) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (restoreAttempts_cons v tape width compact pad attempts
          (List.replicate n true) foreignA foreignB), ih (some true, v.2)]
      rw [unary_comm]
      simp

private theorem prepend_cons (v : Control) (bit : Bool) (tape width compact pad
    attempts foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .prepend) v tape width [] (bit :: compact)
      pad attempts [] [] foreignA foreignB) =
      some (cfg (some .prepend) (some bit, v.2) (bit :: tape) width [] compact
        pad attempts [] [] foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem prepend_nil (v : Control) (tape width pad attempts
    foreignA foreignB : List Bool) :
    TM2.step program (cfg (some .prepend) v tape width [] [] pad attempts [] []
      foreignA foreignB) =
      some (cfg none (none, v.2) tape width [] [] pad attempts [] []
        foreignA foreignB) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem prepend_phase (v : Control) (compact tape width pad attempts
    foreignA foreignB : List Bool) :
    run (compact.length + 1)
      (cfg (some .prepend) v tape width [] compact pad attempts [] []
        foreignA foreignB) =
      cfg none (none, v.2) (compact.reverse ++ tape) width [] [] pad attempts
        [] [] foreignA foreignB := by
  induction compact generalizing v tape with
  | nil => simpa using (run_succ
      (prepend_nil v tape width pad attempts foreignA foreignB) 0)
  | cons bit compact ih =>
      rw [show (bit :: compact).length + 1 = (compact.length + 1) + 1 by simp,
        run_succ (prepend_cons v bit tape width compact pad attempts
          foreignA foreignB), ih (some bit, v.2)]
      simp [List.reverse_cons, List.append_assoc]

def prefWord (b p : ℕ) (x : Fin (b + p) → Bool) : List Bool :=
  List.ofFn (fun i : Fin b => x (Fin.castAdd p i))

def padWord (b p : ℕ) (x : Fin (b + p) → Bool) : List Bool :=
  List.ofFn (fun i : Fin p => x (Fin.natAdd b i))

theorem word_split (b p : ℕ) (x : Fin (b + p) → Bool) :
    List.ofFn x = prefWord b p x ++ padWord b p x := by
  calc
    List.ofFn x = List.ofFn (Fin.append
      (fun i : Fin b => x (Fin.castAdd p i))
      (fun i : Fin p => x (Fin.natAdd b i))) := by
        rw [Fin.append_castAdd_natAdd]
    _ = prefWord b p x ++ padWord b p x := by
      simp [prefWord, padWord]

theorem prefWord_length (b p : ℕ) (x : Fin (b + p) → Bool) :
    (prefWord b p x).length = b := by simp [prefWord]

theorem padWord_length (b p : ℕ) (x : Fin (b + p) → Bool) :
    (padWord b p x).length = p := by simp [padWord]

def compactTape (b p : ℕ) : (R : ℕ) →
    Paper2.CappedSampler.BitTape (b + p) R → List Bool
  | 0, _ => []
  | R + 1, tape => prefWord b p tape.1 ++ compactTape b p R tape.2

theorem compactTape_length (b p R : ℕ)
    (tape : Paper2.CappedSampler.BitTape (b + p) R) :
    (compactTape b p R tape).length = b * R := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp [compactTape, prefWord_length, ih, Nat.mul_succ,
        Nat.add_comm]

/-- Before final reversal, the accumulator is the reverse of all extracted
prefix words. The later-draw suffix remains literally on stack 0. -/
theorem project_blocks (b p R : ℕ)
    (tape : Paper2.CappedSampler.BitTape (b + p) R)
    (suffix compact attemptsWork foreignA foreignB : List Bool) :
    run (R * (2 * (b + p) + 5))
      (cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape (b + p) R tape ++ suffix)
        (List.replicate b true) [] compact (List.replicate p true)
        (List.replicate R true) attemptsWork [] foreignA foreignB) =
      cfg (some .start) (none, false) suffix (List.replicate b true) []
        ((compactTape b p R tape).reverse ++ compact)
        (List.replicate p true) []
        (List.replicate R true ++ attemptsWork) [] foreignA foreignB := by
  induction R generalizing compact attemptsWork with
  | zero => simp [BlockTransfer.flatBitTape, compactTape, run]
  | succ R ih =>
      let pref := prefWord b p tape.1
      let pad := padWord b p tape.1
      let rest := BlockTransfer.flatBitTape (b + p) R tape.2 ++ suffix
      have hlen1 : pref.length = b := prefWord_length b p tape.1
      have hlen2 : pad.length = p := padWord_length b p tape.1
      have hword := one_word (none, false) pref pad rest compact attemptsWork
        (List.replicate R true) foreignA foreignB
      simp only [hlen1, hlen2] at hword
      have htail := ih tape.2 (pref.reverse ++ compact) (true :: attemptsWork)
      rw [show (R + 1) * (2 * (b + p) + 5) =
        (2 * b + 2 * p + 5) + R * (2 * (b + p) + 5) by ring,
        run_add (by
          simpa [BlockTransfer.flatBitTape, word_split, pref, pad, rest,
            List.append_assoc, List.replicate_succ] using hword)
          (R * (2 * (b + p) + 5))]
      rw [unary_comm] at htail
      simpa [compactTape, pref, rest, List.reverse_append,
        List.append_assoc, List.replicate_succ] using htail

/-- Full charged physical projection, including restoration of the unary
attempt counter and reversal of the compacted bits onto the original tape
stack. The next draw begins at the unchanged `suffix`. -/
theorem project_wide_tape (b p R : ℕ)
    (tape : Paper2.CappedSampler.BitTape (b + p) R)
    (suffix foreignA foreignB : List Bool) :
    run (R * (2 * (b + p) + b + 6) + 3)
      (cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape (b + p) R tape ++ suffix)
        (List.replicate b true) [] [] (List.replicate p true)
        (List.replicate R true) [] [] foreignA foreignB) =
      cfg none (none, false) (compactTape b p R tape ++ suffix)
        (List.replicate b true) [] [] (List.replicate p true)
        (List.replicate R true) [] [] foreignA foreignB := by
  have hp := project_blocks b p R tape suffix [] [] foreignA foreignB
  simp only [List.append_nil] at hp
  have hs := start_nil (none, false) suffix (List.replicate b true)
    (compactTape b p R tape).reverse (List.replicate p true)
    (List.replicate R true) foreignA foreignB
  have hr := restoreAttempts_phase (none, false) R suffix
    (List.replicate b true) (compactTape b p R tape).reverse
    (List.replicate p true) [] foreignA foreignB
  simp only [List.append_nil] at hr
  have hpr := prepend_phase (none, false) (compactTape b p R tape).reverse
    suffix (List.replicate b true) (List.replicate p true)
    (List.replicate R true) foreignA foreignB
  simp only [List.length_reverse, List.reverse_reverse] at hpr
  have h1 := (run_succ hs (R + 1)).trans hr
  have h2 := (run_add h1 (b * R + 1)).trans
    (by simpa [compactTape_length] using hpr)
  have h3 := (run_add hp (R + 1 + 1 + (b * R + 1))).trans h2
  simpa only [show R * (2 * (b + p) + 5) +
      (R + 1 + 1 + (b * R + 1)) =
      R * (2 * (b + p) + b + 6) + 3 by ring] using h3


theorem prefWord_eq_source_prefix (b p : ℕ) (x : Fin (b + p) → Bool) :
    prefWord b p x = List.ofFn
      (Paper2.CappedSampler.prefixBits (Nat.le_add_right b p) x) := by
  apply List.ofFn_inj.mpr
  funext i
  simp only [Paper2.CappedSampler.prefixBits]
  congr 1

theorem compactTape_eq_source_prefix (b p R : ℕ)
    (tape : Paper2.CappedSampler.BitTape (b + p) R) :
    compactTape b p R tape =
      BlockTransfer.flatBitTape b R
        (Paper2.CappedSampler.prefixBitTape (Nat.le_add_right b p) R tape) := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp [compactTape, BlockTransfer.flatBitTape,
        Paper2.CappedSampler.prefixBitTape, prefWord_eq_source_prefix, ih]


namespace Prepare

inductive Label where
  | moveCap | clearPad
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 10 => Bool) Label Control
  | .moveCap =>
      pop 8 (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (push 6 (fun _ => true) (goto (fun _ => .moveCap)))
          (goto (fun _ => .clearPad)))
  | .clearPad =>
      pop 4 (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (goto (fun _ => .clearPad))
          halt)

def cfg (l : Option Label) (v : Control) (tape width pad attempts
    capWork savedCap foreign : List Bool) :
    TM2.Cfg (fun _ : Fin 10 => Bool) Label Control :=
  ⟨l, v, Comparator.bank tape width [] [] pad attempts capWork [] savedCap foreign⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem cap_cons (v : Control) (tape width pad attempts capWork
    savedCap foreign : List Bool) :
    TM2.step program
      (cfg (some .moveCap) v tape width pad attempts capWork
        (true :: savedCap) foreign) =
      some (cfg (some .moveCap) (some true, v.2) tape width pad attempts
        (true :: capWork) savedCap foreign) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]
  funext k
  fin_cases k <;> rfl

private theorem cap_nil (v : Control) (tape width pad attempts capWork
    foreign : List Bool) :
    TM2.step program
      (cfg (some .moveCap) v tape width pad attempts capWork [] foreign) =
      some (cfg (some .clearPad) (none, v.2) tape width pad attempts capWork
        [] foreign) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]

private theorem pad_cons (v : Control) (tape width pad attempts capWork
    foreign : List Bool) :
    TM2.step program
      (cfg (some .clearPad) v tape width (true :: pad) attempts capWork
        [] foreign) =
      some (cfg (some .clearPad) (some true, v.2) tape width pad attempts
        capWork [] foreign) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]
  funext k
  fin_cases k <;> rfl

private theorem pad_nil (v : Control) (tape width attempts capWork
    foreign : List Bool) :
    TM2.step program
      (cfg (some .clearPad) v tape width [] attempts capWork [] foreign) =
      some (cfg none (none, v.2) tape width [] attempts capWork [] foreign) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]

private theorem unary_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem move_cap (v : Control) (n : ℕ) (tape width pad attempts capWork
    foreign : List Bool) :
    run (n + 1)
      (cfg (some .moveCap) v tape width pad attempts capWork
        (List.replicate n true) foreign) =
      cfg (some .clearPad) (none, v.2) tape width pad attempts
        (List.replicate n true ++ capWork) [] foreign := by
  induction n generalizing v capWork with
  | zero => simpa using (run_succ
      (cap_nil v tape width pad attempts capWork foreign) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (cap_cons v tape width pad attempts capWork
          (List.replicate n true) foreign), ih (some true, v.2)]
      rw [unary_comm]
      simp

theorem clear_pad (v : Control) (n : ℕ) (tape width attempts capWork
    foreign : List Bool) :
    run (n + 1)
      (cfg (some .clearPad) v tape width (List.replicate n true)
        attempts capWork [] foreign) =
      cfg none (none, v.2) tape width [] attempts capWork [] foreign := by
  induction n generalizing v with
  | zero => simpa using (run_succ
      (pad_nil v tape width attempts capWork foreign) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (pad_cons v tape width (List.replicate n true) attempts
          capWork foreign), ih (some true, v.2)]

/-- Reorganize the projector bank for the existing capped-loop program.
Cap copying and padding deletion cost one physical step per unary cell. -/
theorem prepare_bank (n p : ℕ) (tape width attempts : List Bool) :
    run (n + p + 2)
      (cfg (some .moveCap) (none, false) tape width
        (List.replicate p true) attempts [] (List.replicate n true) []) =
      cfg none (none, false) tape width [] attempts
        (List.replicate n true) [] [] := by
  have hm := move_cap (none, false) n tape width (List.replicate p true)
    attempts [] []
  simp only [List.append_nil] at hm
  have hp := clear_pad (none, false) p tape width attempts
    (List.replicate n true) []
  have h := (run_add hm (p + 1)).trans hp
  simpa only [show n + 1 + (p + 1) = n + p + 2 by omega] using h


end Prepare

open EthInapproximability.CurrentPaper

/-- Physical projection, bank preparation, and the frozen capped loop/drain
are syntactically inlined in that order on the same ten Boolean stacks. -/
def projectionThenPrepare :=
  BitMachineRawSequence.program program Prepare.program
    Prepare.Label.moveCap (none, false) (none, false)

def wideProgram :=
  BitMachineRawSequence.program projectionThenPrepare Drain.wrappedProgram
    (BitMachineRawSequence.leftLabel Comparator.Label.start)
    ((none, false), (none, false)) ((none, false), (none, false))

theorem wide_loop_drains (D p R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D + p) R)
    (suffix : List Bool) :
    ∃ t c,
      t ≤ R * (2 * (Nat.clog 2 D + p) + Nat.clog 2 D + 6) + 3 +
        (D - 1 + p + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance wideProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel Label.start)),
          (((none, false), (none, false)), ((none, false), (none, false))),
          bank
            (BlockTransfer.flatBitTape (Nat.clog 2 D + p) R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate p true) (List.replicate R true) [] []
            (List.replicate (D - 1) true) []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label Label Prepare.Label)
              (BitMachineRawSequence.Label Comparator.Label Drain.Label))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control Control Control)
              (BitMachineRawSequence.Control Comparator.Control Drain.Control))) = c ∧
      c.l = none ∧ c.stk 0 = suffix ∧
      (if (c.stk 9).head? = some true then some (c.stk 9).tail.length
        else none) =
        (Paper2.CappedSampler.runWideBits D (Nat.clog 2 D + p) R
          (Nat.le_add_right (Nat.clog 2 D) p) tape).map Fin.val := by
  let b := Nat.clog 2 D
  let n := D - 1
  let prefTape := Paper2.CappedSampler.prefixBitTape
    (Nat.le_add_right b p) R tape
  let S := bank (BlockTransfer.flatBitTape (b + p) R tape ++ suffix)
    (List.replicate b true) [] [] (List.replicate p true)
    (List.replicate R true) [] [] (List.replicate n true) []
  let T := bank (compactTape b p R tape ++ suffix)
    (List.replicate b true) [] [] (List.replicate p true)
    (List.replicate R true) [] [] (List.replicate n true) []
  let U := Comparator.bank (BlockTransfer.flatBitTape b R prefTape ++ suffix)
    (List.replicate b true) [] [] [] (List.replicate R true)
    (List.replicate n true) [] [] []
  have hproj : run (R * (2 * (b + p) + b + 6) + 3)
      (⟨some Label.start, (none, false), S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none, (none, false), T⟩ := by
    simpa [S, T, cfg] using
      project_wide_tape b p R tape suffix (List.replicate n true) []
  have hprep : Prepare.run (n + p + 2)
      (⟨some Prepare.Label.moveCap, (none, false), T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Prepare.Label Control) =
      ⟨none, (none, false), U⟩ := by
    simpa [T, U, prefTape, compactTape_eq_source_prefix, Prepare.cfg,
      bank, Comparator.bank] using
      Prepare.prepare_bank n p (compactTape b p R tape ++ suffix)
        (List.replicate b true) (List.replicate R true)
  obtain ⟨t₁, ht₁, hr₁⟩ := BitMachineRawSequence.runs program
    Prepare.program Label.start Prepare.Label.moveCap (none, false)
    (none, false) (none, false) (none, false) S T U
    (R * (2 * (b + p) + b + 6) + 3) (n + p + 2) hproj hprep
  obtain ⟨t₂, c₂, ht₂, hr₂, hhalt₂, htape₂, hout₂⟩ :=
    Drain.wrapped_loop_drains D R hD prefTape suffix
  have hc₂ : c₂ = ⟨none, c₂.var, c₂.stk⟩ := by
    cases c₂ with
    | mk l v stk =>
      cases l with
      | none => rfl
      | some l => exact (Option.some_ne_none l hhalt₂).elim
  have hr₂' : ((advance Drain.wrappedProgram)^[t₂])
      (⟨some (BitMachineRawSequence.leftLabel Comparator.Label.start),
        ((none, false), (none, false)), U⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool)
          (BitMachineRawSequence.Label Comparator.Label Drain.Label)
          (BitMachineRawSequence.Control Comparator.Control Drain.Control)) =
      ⟨none, c₂.var, c₂.stk⟩ := by
    simpa [U, prefTape, b, n, compactTape_eq_source_prefix] using
      hr₂.trans hc₂
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    projectionThenPrepare Drain.wrappedProgram
    (BitMachineRawSequence.leftLabel Label.start)
    (BitMachineRawSequence.leftLabel Comparator.Label.start)
    ((none, false), (none, false)) ((none, false), (none, false))
    ((none, false), (none, false)) c₂.var S U c₂.stk t₁ t₂
    (by simpa [projectionThenPrepare] using hr₁) hr₂'
  let c : TM2.Cfg (fun _ : Fin 10 => Bool)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label Label Prepare.Label)
        (BitMachineRawSequence.Label Comparator.Label Drain.Label))
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control Control Control)
        (BitMachineRawSequence.Control Comparator.Control Drain.Control)) :=
    ⟨none, (((none, false), (none, false)), c₂.var), c₂.stk⟩
  refine ⟨t, c, ?_, ?_, rfl, ?_, ?_⟩
  · dsimp [b, n] at *
    omega
  · simpa [wideProgram, S, c, b, n] using hr
  · exact htape₂
  · simpa [c, Paper2.CappedSampler.runWideBits, prefTape] using hout₂


/-- Reparameterization by the public attempt width `B`; the padding width
is the physical unary word of length `B-b`. This theorem does not claim a
machine conversion from a binary header into that unary word. -/
theorem wide_loop_drains_public (D B R : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Paper2.CappedSampler.BitTape B R) (suffix : List Bool) :
    ∃ t c,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D +
          (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance wideProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel Label.start)),
          (((none, false), (none, false)), ((none, false), (none, false))),
          bank (BlockTransfer.flatBitTape B R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true)
            (List.replicate R true) [] [] (List.replicate (D - 1) true) []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label Label Prepare.Label)
              (BitMachineRawSequence.Label Comparator.Label Drain.Label))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control Control Control)
              (BitMachineRawSequence.Control Comparator.Control Drain.Control))) = c ∧
      c.l = none ∧ c.stk 0 = suffix ∧
      (if (c.stk 9).head? = some true then some (c.stk 9).tail.length
        else none) =
        (Paper2.CappedSampler.runWideBits D B R hB tape).map Fin.val := by
  obtain ⟨p, hp⟩ : ∃ p, B = Nat.clog 2 D + p :=
    ⟨B - Nat.clog 2 D, by omega⟩
  subst B
  simpa [Nat.add_sub_cancel_left] using wide_loop_drains D p R hD tape suffix


/-- Direct physical row-major layout of the source recursive product. This
definition is for displaying the consecutive-draw boundary; it is not yet
proved equal to `RecursiveSamplingTape.writeTape`. -/
def flatAdaptiveTape (B R : ℕ) : (N : ℕ) →
    Paper2.CappedSampler.Adaptive.Tape B R N → List Bool
  | 0, _ => []
  | N + 1, tape =>
      BlockTransfer.flatBitTape B R tape.1 ++ flatAdaptiveTape B R N tape.2

theorem flatAdaptiveTape_length (B R N : ℕ)
    (tape : Paper2.CappedSampler.Adaptive.Tape B R N) :
    (flatAdaptiveTape B R N tape).length =
      Paper2.RecursiveSamplingTape.bitCount B R N := by
  induction N with
  | zero => simp [flatAdaptiveTape, Paper2.RecursiveSamplingTape.bitCount]
  | succ N ih =>
      simp [flatAdaptiveTape, BlockTransfer.flatBitTape_length, ih,
        Paper2.RecursiveSamplingTape.bitCount]
      ring

/-- One completed wide draw leaves the literal remaining recursive draws
at the head of stack 0. The public width `B` is the same in every draw;
the state-dependent denominator is this call's `D`. -/
theorem next_draw_framed (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Paper2.CappedSampler.Adaptive.Tape B R (N + 1)) :
    ∃ t c,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D +
          (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance wideProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel Label.start)),
          (((none, false), (none, false)), ((none, false), (none, false))),
          bank (flatAdaptiveTape B R (N + 1) tape)
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true)
            (List.replicate R true) [] [] (List.replicate (D - 1) true) []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label Label Prepare.Label)
              (BitMachineRawSequence.Label Comparator.Label Drain.Label))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control Control Control)
              (BitMachineRawSequence.Control Comparator.Control Drain.Control))) = c ∧
      c.l = none ∧ c.stk 0 = flatAdaptiveTape B R N tape.2 ∧
      (if (c.stk 9).head? = some true then some (c.stk 9).tail.length
        else none) =
        (Paper2.CappedSampler.runWideBits D B R hB tape.1).map Fin.val := by
  simpa [flatAdaptiveTape] using
    wide_loop_drains_public D B R hD hB tape.1
      (flatAdaptiveTape B R N tape.2)


end Paper2.CappedLoop.WideProjection
