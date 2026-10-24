import Paper2.CappedLoopComparator
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
Scratch implementation of the fixed-block acceptance drain for Paper 2 v12.
The standalone capped loop may halt as soon as a ticket is accepted; this
finite-control TM2 program physically skips its unused, already allocated
attempt words before the next draw begins. The accepting output stack is
never touched. The final theorem composes the loop and drain on one bank.
-/

namespace Paper2.CappedLoop.Drain

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | start | read | restoreWidth
  deriving DecidableEq, Fintype

abbrev Control := CappedLoop.Comparator.Control

def program : Label → TM2.Stmt (fun _ : Fin 10 => Bool) Label Control
  | .start =>
      pop 5 (fun s attempt => (attempt, s.2))
        (branch (fun s => s.1.isSome)
          (goto (fun _ => .read))
          halt)
  | .read =>
      pop 1 (fun s width => (width, s.2))
        (branch (fun s => s.1.isSome)
          (pop 0 (fun s bit => (bit, s.2))
            (branch (fun s => s.1.isSome)
              (push 2 (fun _ => true) (goto (fun _ => .read)))
              halt))
          (goto (fun _ => .restoreWidth)))
  | .restoreWidth =>
      pop 2 (fun s width => (width, s.2))
        (branch (fun s => s.1.isSome)
          (push 1 (fun _ => true) (goto (fun _ => .restoreWidth)))
          (goto (fun _ => .start)))

def cfg (l : Option Label) (v : Control)
    (tape width work bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.Cfg (fun _ : Fin 10 => Bool) Label Control :=
  ⟨l, v, Comparator.bank tape width work bitsWork ticket
    attempts savedCap cap cmpWork out⟩

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

private theorem start_cons (v : Control) (tape width work bitsWork ticket attempts
    savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .start) v tape width work bitsWork ticket
      (true :: attempts) savedCap cap cmpWork out) =
      some (cfg (some .read) (some true, v.2) tape width work bitsWork ticket
        attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]
  funext k
  fin_cases k <;> rfl

private theorem start_nil (v : Control) (tape width work bitsWork ticket
    savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .start) v tape width work bitsWork ticket []
      savedCap cap cmpWork out) =
      some (cfg none (none, v.2) tape width work bitsWork ticket []
        savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]

private theorem read_cons (v : Control) (bit : Bool) (tape width work bitsWork ticket
    attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .read) v (bit :: tape) (true :: width) work
      bitsWork ticket attempts savedCap cap cmpWork out) =
      some (cfg (some .read) (some bit, v.2) tape width (true :: work)
        bitsWork ticket attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]
  funext k
  fin_cases k <;> rfl

private theorem read_nil (v : Control) (tape work bitsWork ticket attempts
    savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .read) v tape [] work bitsWork ticket attempts
      savedCap cap cmpWork out) =
      some (cfg (some .restoreWidth) (none, v.2) tape [] work bitsWork ticket
        attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]

private theorem restore_cons (v : Control) (tape width work bitsWork ticket
    attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .restoreWidth) v tape width (true :: work)
      bitsWork ticket attempts savedCap cap cmpWork out) =
      some (cfg (some .restoreWidth) (some true, v.2) tape (true :: width) work
        bitsWork ticket attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (v : Control) (tape width bitsWork ticket
    attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program (cfg (some .restoreWidth) v tape width [] bitsWork ticket
      attempts savedCap cap cmpWork out) =
      some (cfg (some .start) (none, v.2) tape width [] bitsWork ticket attempts
        savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, Comparator.bank]

private theorem unary_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem read_prefix (v : Control) (block tape work bitsWork ticket attempts
    savedCap cap cmpWork out : List Bool) :
    run (block.length + 1)
      (cfg (some .read) v (block ++ tape) (List.replicate block.length true)
        work bitsWork ticket attempts savedCap cap cmpWork out) =
      cfg (some .restoreWidth) (none, v.2) tape []
        (List.replicate block.length true ++ work) bitsWork ticket attempts
        savedCap cap cmpWork out := by
  induction block generalizing v work with
  | nil => simpa using (run_succ
      (read_nil v tape work bitsWork ticket attempts savedCap cap cmpWork out) 0)
  | cons bit block ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (read_cons v bit (block ++ tape)
        (List.replicate block.length true) work bitsWork ticket attempts
        savedCap cap cmpWork out), ih (some bit, v.2)]
      rw [unary_comm]

theorem restore_width (v : Control) (n : ℕ) (tape width bitsWork ticket attempts
    savedCap cap cmpWork out : List Bool) :
    run (n + 1)
      (cfg (some .restoreWidth) v tape width (List.replicate n true)
        bitsWork ticket attempts savedCap cap cmpWork out) =
      cfg (some .start) (none, v.2) tape
        (List.replicate n true ++ width) [] bitsWork ticket attempts
        savedCap cap cmpWork out := by
  induction n generalizing v width with
  | zero => simpa using (run_succ
      (restore_nil v tape width bitsWork ticket attempts savedCap cap cmpWork out) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (restore_cons v tape width (List.replicate n true)
          bitsWork ticket attempts savedCap cap cmpWork out),
        ih (some true, v.2)]
      rw [unary_comm]
      simp

/-- Exactly one physical block is skipped. Width is restored, the attempt
counter loses one symbol, every foreign stack (including accepted output)
is unchanged, and the suffix is untouched. -/
theorem drain_one (v : Control) (block suffix bitsWork ticket attempts savedCap
    cap cmpWork out : List Bool) :
    run (2 * block.length + 3)
      (cfg (some .start) v (block ++ suffix)
        (List.replicate block.length true) [] bitsWork ticket
        (true :: attempts) savedCap cap cmpWork out) =
      cfg (some .start) (none, v.2) suffix
        (List.replicate block.length true) [] bitsWork ticket attempts
        savedCap cap cmpWork out := by
  have hs := start_cons v (block ++ suffix)
    (List.replicate block.length true) [] bitsWork ticket attempts
    savedCap cap cmpWork out
  have hr := read_prefix (some true, v.2) block suffix [] bitsWork ticket
    attempts savedCap cap cmpWork out
  simp only [List.append_nil] at hr
  have hw := restore_width (none, v.2) block.length suffix [] bitsWork ticket
    attempts savedCap cap cmpWork out
  simp only [List.append_nil] at hw
  have h₁ := (run_succ hs (block.length + 1)).trans hr
  have h₂ := (run_add h₁ (block.length + 1)).trans hw
  simpa only [show block.length + 1 + 1 + (block.length + 1) =
    2 * block.length + 3 by omega] using h₂

/-- For a literal `R`-attempt tape followed by a later-draw suffix, drain
all exactly `b*R` reserved bits using the unary width and attempt stacks.
This includes `b=0` and `R=0`, with one final charged halt step. -/
theorem drain_bitTape (b R : ℕ) (tape : Paper2.CappedSampler.BitTape b R)
    (suffix bitsWork ticket savedCap cap cmpWork out : List Bool) :
    run (R * (2 * b + 3) + 1)
      (cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape b R tape ++ suffix)
        (List.replicate b true) [] bitsWork ticket
        (List.replicate R true) savedCap cap cmpWork out) =
      cfg none (none, false) suffix (List.replicate b true) [] bitsWork ticket
        [] savedCap cap cmpWork out := by
  induction R with
  | zero =>
      simpa [BlockTransfer.flatBitTape] using
        run_succ (start_nil (none, false) suffix (List.replicate b true) []
          bitsWork ticket savedCap cap cmpWork out) 0
  | succ R ih =>
      let block := List.ofFn tape.1
      let rest := BlockTransfer.flatBitTape b R tape.2
      have hlen : block.length = b := List.length_ofFn
      have hfirst := drain_one (none, false) block (rest ++ suffix)
        bitsWork ticket (List.replicate R true) savedCap cap cmpWork out
      simp only [hlen] at hfirst
      have htail := ih tape.2
      rw [show (R + 1) * (2 * b + 3) + 1 =
        (2 * b + 3) + (R * (2 * b + 3) + 1) by ring,
        run_add (by simpa [BlockTransfer.flatBitTape, block, rest,
          List.append_assoc] using hfirst) (R * (2 * b + 3) + 1)]
      simpa [rest] using htail


private theorem cmp_run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool)
    Comparator.Label Comparator.Control} {m : ℕ}
    (h : Comparator.run m c = d) (n : ℕ) :
    Comparator.run (m + n) c = Comparator.run n d := by
  rw [Nat.add_comm m n]
  simp only [Comparator.run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-! The following framed comparison deliberately uses the frozen program,
not a new comparator. The later-draw suffix is kept in stack 0 throughout
the public transfer/copy/comparison theorems. -/

theorem one_complete_framed (b n : ℕ) (block rest : List Bool)
    (hb : block.length = b) (attempts : List Bool) :
    ∃ t c,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false) (block ++ rest)
          (List.replicate b true) [] [] [] (true :: attempts)
          (List.replicate n true) [] [] []) =
        Comparator.injectCmp
          (Comparator.bank rest (List.replicate b true) [] [] block attempts
            (List.replicate n true) (List.replicate n true) [] []) c ∧
      c.l = none ∧
      c.stk 3 = EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result
        block (List.replicate n true) [] ∧
      (c.stk 0).length = b ∧ c.stk 2 = [] ∧ (c.stk 1).length ≤ n := by
  have htransfer := Comparator.transfer_to_copyCap block rest attempts
    (List.replicate n true)
  rw [hb] at htransfer
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    Comparator.copy_cap_then_compare n rest (List.replicate b true) [] []
      block attempts
  refine ⟨3 * b + 4 + t, c, ?_, ?_, hhalt, hout, ?_, hwork, hcaplen⟩
  · rw [← hb]
    omega
  · exact (cmp_run_add htransfer t).trans hr
  · simpa [hb] using hlen

theorem one_success_framed (b n : ℕ) (block rest : List Bool)
    (hb : block.length = b) (attempts : List Bool)
    (hs : EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block ≤ n) :
    ∃ t c,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) + 1 ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false) (block ++ rest)
          (List.replicate b true) [] [] [] (true :: attempts)
          (List.replicate n true) [] [] []) = c ∧
      c.l = none ∧ c.stk 0 = rest ∧
      c.stk 1 = List.replicate b true ∧
      c.stk 2 = [] ∧
      c.stk 5 = attempts ∧ c.stk 6 = List.replicate n true ∧
      c.stk 9 = true :: List.replicate
        (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) true := by
  obtain ⟨t, c, ht, hr, hhalt, hout, _hlen, hwork, _hcaplen⟩ :=
    one_complete_framed b n block rest hb attempts
  let cap := List.replicate n true
  let base := Comparator.bank rest (List.replicate b true) [] [] block attempts
    cap cap [] []
  have hout' : c.stk 3 = true :: List.replicate
      (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) true := by
    rw [hout]
    simp [EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result, hs]
  have hcfg : Comparator.injectCmp base c =
      Comparator.cfg (some .decision) c.var rest (List.replicate b true)
        [] [] (c.stk 0) attempts cap (c.stk 1) []
        (true :: List.replicate
          (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) true) := by
    rw [Comparator.cmp_endpoint_cfg rest (List.replicate b true) [] [] block
      attempts cap cap [] [] c hhalt hwork, hout']
  let finalCfg := Comparator.cfg none (some true, c.var.2) rest
    (List.replicate b true) [] [] (c.stk 0) attempts cap (c.stk 1) []
    (true :: List.replicate
      (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) true)
  refine ⟨t + 1, finalCfg, by omega, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [cmp_run_add hr 1, hcfg]
  simp [Comparator.run, finalCfg, advance, TM2.step, TM2.stepAux,
    Comparator.program, Comparator.cfg, Comparator.bank]

theorem one_reject_framed (b n : ℕ) (block rest : List Bool)
    (hb : block.length = b) (attempts : List Bool)
    (hf : n < EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) :
    ∃ t,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) +
        (b + 2 * n + 5) ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false) (block ++ rest)
          (List.replicate b true) [] [] [] (true :: attempts)
          (List.replicate n true) [] [] []) =
        Comparator.cfg (some .start) (none, false) rest
          (List.replicate b true) [] [] [] attempts
          (List.replicate n true) [] [] [] := by
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    one_complete_framed b n block rest hb attempts
  let cap := List.replicate n true
  let base := Comparator.bank rest (List.replicate b true) [] [] block attempts
    cap cap [] []
  have hout' : c.stk 3 = false :: List.replicate n true := by
    rw [hout]
    have hle : n ≤ EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        block := by omega
    simp [EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result,
      Nat.not_le.mpr hf, min_eq_right hle]
  have hcfg : Comparator.injectCmp base c =
      Comparator.cfg (some .decision) c.var rest (List.replicate b true)
        [] [] (c.stk 0) attempts cap (c.stk 1) []
        (false :: List.replicate n true) := by
    rw [Comparator.cmp_endpoint_cfg rest (List.replicate b true) [] [] block
      attempts cap cap [] [] c hhalt hwork, hout']
  have hcleanup := Comparator.rejected_cleanup c.var (c.stk 0) (c.stk 1)
    (List.replicate n true) rest (List.replicate b true) [] [] attempts cap
  let u := (c.stk 0).length + (c.stk 1).length + n + 5
  refine ⟨t + u, ?_, ?_⟩
  · dsimp [u]
    omega
  · rw [cmp_run_add hr u, hcfg]
    simpa [u, cap] using hcleanup

/-- Framed full capped loop. On acceptance, the residual bank begins with
the unused attempt blocks and then the later-draw suffix. On exhaustion it
is precisely the suffix. This is the boundary required for a drain wrapper. -/
theorem loop_framed (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R)
    (suffix : List Bool) :
    ∃ t c r, ∃ tail : Paper2.CappedSampler.BitTape (Nat.clog 2 D) r,
      t ≤ R * Comparator.attemptBound D + 1 ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false)
          (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape ++ suffix)
          (List.replicate (Nat.clog 2 D) true) [] [] []
          (List.replicate R true) (List.replicate (D - 1) true) [] [] []) = c ∧
      c.l = none ∧
      Comparator.machineOutput c =
        (Paper2.CappedSampler.runBits D R tape).map Fin.val ∧
      c.stk 0 = BlockTransfer.flatBitTape (Nat.clog 2 D) r tail ++ suffix ∧
      c.stk 1 = List.replicate (Nat.clog 2 D) true ∧
      c.stk 2 = [] ∧ c.stk 5 = List.replicate r true ∧ r ≤ R := by
  induction R with
  | zero =>
      let c := Comparator.cfg none (none, false) suffix
        (List.replicate (Nat.clog 2 D) true) [] [] [] []
        (List.replicate (D - 1) true) [] [] []
      refine ⟨1, c, 0, (), by simp, ?_, rfl, ?_, rfl, rfl, rfl, rfl,
        Nat.le_refl 0⟩
      · simpa [BlockTransfer.flatBitTape, c] using
          Comparator.empty_attempts_halt suffix
            (List.replicate (Nat.clog 2 D) true)
            (List.replicate (D - 1) true)
      · simp [Comparator.machineOutput, c, Paper2.CappedSampler.runBits,
          Paper2.CappedSampler.run, Comparator.cfg, Comparator.bank]
  | succ R ih =>
      let b := Nat.clog 2 D
      let n := D - 1
      let block := List.ofFn tape.1
      let rest := BlockTransfer.flatBitTape b R tape.2 ++ suffix
      let q := EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block
      have hblen : block.length = b := List.length_ofFn
      have hv : q = (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val := by
        simpa [q, block, b, Paper2.CappedTicketMachine.ticketWord] using
          Paper2.CappedTicketMachine.bitsValue_ofFn tape.1
      by_cases hs : q ≤ n
      · obtain ⟨t, c, ht, hr, hhalt, htape, hwidth, hwork, hattempts, _hsaved,
          hout⟩ := one_success_framed b n block rest hblen
            (List.replicate R true) hs
        refine ⟨t, c, R, tape.2, ?_, ?_, hhalt, ?_, htape, hwidth, hwork,
          hattempts, by omega⟩
        · dsimp [Comparator.attemptBound, b, n] at *
          nlinarith
        · simpa [BlockTransfer.flatBitTape, block, rest, List.append_assoc]
            using hr
        · have hlt : (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_pos hlt]
          simp [Comparator.machineOutput, hout]
          simpa [q, b] using hv
      · have hf : n < q := by omega
        obtain ⟨t₁, ht₁, hr₁⟩ := one_reject_framed b n block rest hblen
          (List.replicate R true) hf
        obtain ⟨t₂, c, r, tail, ht₂, hr₂, hhalt, hout, htape,
          hwidth, hwork, hattempts, hrle⟩ := ih tape.2
        refine ⟨t₁ + t₂, c, r, tail, ?_, ?_, hhalt, ?_, htape,
          hwidth, hwork, hattempts, by omega⟩
        · dsimp [Comparator.attemptBound, b, n] at *
          nlinarith
        · have hr₁' : Comparator.run t₁
              (Comparator.cfg (some .start) (none, false)
                (BlockTransfer.flatBitTape b (R + 1) tape ++ suffix)
                (List.replicate b true) [] [] []
                (List.replicate (R + 1) true)
                (List.replicate n true) [] [] []) =
              Comparator.cfg (some .start) (none, false) rest
                (List.replicate b true) [] [] []
                (List.replicate R true) (List.replicate n true) [] [] [] := by
            simpa [BlockTransfer.flatBitTape, block, rest,
              List.append_assoc] using hr₁
          exact (cmp_run_add hr₁' t₂).trans (by simpa [rest, b, n] using hr₂)
        · have hnot : ¬ (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_neg hnot]
          exact hout


open EthInapproximability.CurrentPaper

/-- Both instruction tables are literally inlined into a fixed finite
program on one ten-stack bank. Its handoff resets finite control, not stacks. -/
def wrappedProgram := BitMachineRawSequence.program Comparator.program program
  Label.start (none, false) (none, false)

theorem wrapped_loop_drains (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R)
    (suffix : List Bool) :
    ∃ t c,
      t ≤ R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3 ∧
      ((advance wrappedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel Comparator.Label.start),
          ((none, false), (none, false)),
          Comparator.bank
            (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] [] []
            (List.replicate R true) (List.replicate (D - 1) true) [] [] []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (BitMachineRawSequence.Label Comparator.Label Label)
            (BitMachineRawSequence.Control Comparator.Control Control)) = c ∧
      c.l = none ∧ c.stk 0 = suffix ∧
      (if (c.stk 9).head? = some true then some (c.stk 9).tail.length
        else none) =
        (Paper2.CappedSampler.runBits D R tape).map Fin.val := by
  obtain ⟨ta, ca, r, tail, hta, hra, hhalt, hout, htape, hwidth, hwork,
    hattempts, hrle⟩ := loop_framed D R hD tape suffix
  let b := Nat.clog 2 D
  let S := Comparator.bank
    (BlockTransfer.flatBitTape b R tape ++ suffix)
    (List.replicate b true) [] [] []
    (List.replicate R true) (List.replicate (D - 1) true) [] [] []
  let T := Comparator.bank
    (BlockTransfer.flatBitTape b r tail ++ suffix)
    (List.replicate b true) [] (ca.stk 3) (ca.stk 4)
    (List.replicate r true) (ca.stk 6) (ca.stk 7) (ca.stk 8) (ca.stk 9)
  let U := Comparator.bank suffix (List.replicate b true) []
    (ca.stk 3) (ca.stk 4) [] (ca.stk 6) (ca.stk 7) (ca.stk 8) (ca.stk 9)
  have hT : ca.stk = T := by
    funext k
    fin_cases k <;> simp [T, b, Comparator.bank, htape, hwidth,
      hwork, hattempts]
  have hca : ca = ⟨none, ca.var, T⟩ := by
    cases ca with
    | mk l v stk =>
      cases l with
      | none =>
          exact congrArg
            (fun S => (⟨none, v, S⟩ :
              TM2.Cfg (fun _ : Fin 10 => Bool) Comparator.Label Comparator.Control)) hT
      | some l => exact (Option.some_ne_none l hhalt).elim
  have ha : Comparator.run ta
      (⟨some Comparator.Label.start, (none, false), S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Comparator.Label Comparator.Control) =
      ⟨none, ca.var, T⟩ := by
    simpa [S, b, Comparator.cfg] using hra.trans hca
  have hd := drain_bitTape b r tail suffix (ca.stk 3) (ca.stk 4)
    (ca.stk 6) (ca.stk 7) (ca.stk 8) (ca.stk 9)
  have hb : run (r * (2 * b + 3) + 1)
      (⟨some Label.start, (none, false), T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none, (none, false), U⟩ := by
    simpa [T, U, cfg] using hd
  obtain ⟨t, htb, hrun⟩ := BitMachineRawSequence.runs Comparator.program program
    Comparator.Label.start Label.start (none, false) ca.var
    (none, false) (none, false) S T U ta (r * (2 * b + 3) + 1)
    ha hb
  let c : TM2.Cfg (fun _ : Fin 10 => Bool)
      (BitMachineRawSequence.Label Comparator.Label Label)
      (BitMachineRawSequence.Control Comparator.Control Control) :=
    ⟨none, ((none, false), (none, false)), U⟩
  refine ⟨t, c, ?_, ?_, rfl, ?_, ?_⟩
  · dsimp [b, Comparator.attemptBound] at *
    nlinarith
  · simpa [wrappedProgram, S, c] using hrun
  · rfl
  · simpa [c, U, Comparator.machineOutput, hT] using hout


end Paper2.CappedLoop.Drain
