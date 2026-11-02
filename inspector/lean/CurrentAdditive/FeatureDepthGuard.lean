import EthInapproximability.CurrentPaper.BitMachine

/-!
A physical fixed-D guard for the feature enumerator.  The input is the
canonical binary count word from a V2 feature packet.  D=8192=2^13, so a
count is eligible exactly when its canonical word has at most 13 bits.
The finite program scans at most 14 input bits and writes one Boolean verdict.
Extraction of the V2 count field is a separate composition step.
-/

namespace CurrentAdditive.FeatureDepthGuard

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine

def program (l : Fin 16) :
    TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 16) (Fin 2) :=
  if h : l.val < 14 then
    pop 0 (fun _ b => if b.isSome then 1 else 0)
      (branch (fun v => v = 1)
        (if hlast : l.val < 13 then
          goto (fun _ => ⟨l.val + 1, by omega⟩)
         else goto (fun _ => 15))
        (goto (fun _ => 14)))
  else if l = 14 then push 1 (fun _ => true) halt
  else push 1 (fun _ => false) halt

def machine : Machine where
  stackCount := 2
  labelCount := 16
  controlCount := 2
  input := 0
  output := 1
  start := 0
  initial := 0
  program := program

def bank (input output : List Bool) : Fin 2 → List Bool :=
  ![input, output]

def scanCfg (k : Nat) (hk : k < 16) (v : Fin 2)
    (input : List Bool) : machine.Config :=
  ⟨some ⟨k,hk⟩, v, bank input []⟩

private theorem step_empty (k : Nat) (hk : k < 14) (v : Fin 2) :
    machine.step (scanCfg k (by omega) v []) =
      ⟨some (⟨14, by decide⟩ : Fin 16), (⟨0, by decide⟩ : Fin 2), bank [] []⟩ := by
  simp [machine, Machine.step, scanCfg, bank, program,
    TM2.step, TM2.stepAux, hk]

private theorem step_cons_early (k : Nat) (hk : k < 13)
    (v : Fin 2) (b : Bool) (tail : List Bool) :
    machine.step (scanCfg k (by omega) v (b::tail)) =
      scanCfg (k+1) (by omega) 1 tail := by
  simp [machine, Machine.step, scanCfg, bank, program,
    TM2.step, TM2.stepAux, show k < 14 by omega, hk]
  funext i
  fin_cases i <;> rfl

private theorem step_cons_last (v : Fin 2)
    (b : Bool) (tail : List Bool) :
    machine.step (scanCfg 13 (by omega) v (b::tail)) =
      ⟨some (⟨15, by decide⟩ : Fin 16), (⟨1, by decide⟩ : Fin 2), bank tail []⟩ := by
  simp [machine, Machine.step, scanCfg, bank, program,
    TM2.step, TM2.stepAux]
  funext i
  fin_cases i <;> rfl

private theorem step_good (v : Fin 2) (tail : List Bool) :
    machine.step (⟨some (⟨14, by decide⟩ : Fin 16), v, bank tail []⟩ : machine.Config) =
      ⟨none, v, bank tail [true]⟩ := by
  simp [machine, Machine.step, bank, program, TM2.step, TM2.stepAux]
  funext i
  fin_cases i <;> rfl

private theorem step_bad (v : Fin 2) (tail : List Bool) :
    machine.step (⟨some (⟨15, by decide⟩ : Fin 16), v, bank tail []⟩ : machine.Config) =
      ⟨none, v, bank tail [false]⟩ := by
  simp [machine, Machine.step, bank, program, TM2.step, TM2.stepAux]
  funext i
  fin_cases i <;> rfl

private theorem run_two (c : machine.Config) :
    machine.run 2 c = machine.step (machine.step c) := by
  rfl

private theorem run_one_then (c : machine.Config) (t : Nat) :
    machine.run (t+1) c = machine.run t (machine.step c) := by
  rw [show t+1 = 1+t by omega, run_add]
  rfl

private theorem scan_bounded (r k : Nat) (hk : k + r = 13)
    (v : Fin 2) (input : List Bool) :
    ∃ t ≤ r+2,
      (machine.run t (scanCfg k (by omega) v input)).l = none ∧
      (machine.run t (scanCfg k (by omega) v input)).stk (⟨1, by decide⟩ : Fin 2) =
        [decide (input.length ≤ r)] := by
  induction r generalizing k v input with
  | zero =>
      have hkeq : k = 13 := by omega
      subst k
      cases input with
      | nil =>
          refine ⟨2, by omega, ?_, ?_⟩ <;>
            simp only [run_two, step_empty 13 (by omega) v,
              step_good] <;> simp [bank]
      | cons b tail =>
          refine ⟨2, by omega, ?_, ?_⟩ <;>
            simp only [run_two, step_cons_last, step_bad] <;>
            simp [bank]
  | succ r ih =>
      have hk13 : k < 13 := by omega
      cases input with
      | nil =>
          refine ⟨2, by omega, ?_, ?_⟩ <;>
            simp only [run_two, step_empty k (by omega) v,
              step_good] <;> simp [bank]
      | cons b tail =>
          obtain ⟨t,ht,hh,ho⟩ := ih (k+1) (by omega) 1 tail
          refine ⟨t+1, by omega, ?_, ?_⟩
          · simpa [run_one_then, step_cons_early k hk13 v b tail] using hh
          · simpa [run_one_then, step_cons_early k hk13 v b tail]
              using ho

theorem physical_word (word : List Bool) :
    machine.OutputsWithin word [decide (word.length ≤ 13)] 15 := by
  obtain ⟨t, ht, hh, ho⟩ := scan_bounded 13 0 (by decide) 0 word
  refine ⟨t, by omega, ?_, ?_⟩
  · have hb : bank word [] =
        (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then word else []) := by
      funext k
      fin_cases k <;> rfl
    simpa [scanCfg, machine, Machine.init, hb] using hh
  · have hb : bank word [] =
        (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then word else []) := by
      funext k
      fin_cases k <;> rfl
    simpa [scanCfg, machine, Machine.init, hb] using ho

theorem physical_guard (n : Nat) :
    machine.OutputsWithin n.bits [decide (n < 8192)] 15 := by
  have h := scan_bounded 13 0 (by decide) 0 n.bits
  obtain ⟨t,ht,hh,ho⟩ := h
  refine ⟨t, by omega, ?_, ?_⟩
  · have hb : bank n.bits [] = (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then n.bits else []) := by
      funext k
      fin_cases k <;> rfl
    simpa [scanCfg, machine, Machine.init, hb] using hh
  · have hsize : decide (n.bits.length ≤ 13) = decide (n < 8192) := by
      have hp : n.bits.length ≤ 13 ↔ n < 8192 := by
        rw [Nat.size_eq_bits_len, Nat.size_le]
      simpa only [hp]
    have hb : bank n.bits [] = (fun k : Fin 2 => if k = (⟨0, by decide⟩ : Fin 2) then n.bits else []) := by
      funext k
      fin_cases k <;> rfl
    simpa [scanCfg, machine, Machine.init, hb, hsize] using ho

#print axioms physical_guard
#print axioms physical_word

end CurrentAdditive.FeatureDepthGuard
