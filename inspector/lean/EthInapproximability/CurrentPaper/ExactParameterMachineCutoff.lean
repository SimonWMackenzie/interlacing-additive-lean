import EthInapproximability.CurrentPaper.ExactParameterMachineScale
import EthInapproximability.CurrentPaper.ExactSourcePadding

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-!
# Fixed finite-control cutoff for the exact source exponent

This program computes `max (2^21) n` from a unary input of length `n`.
Its control contains only a fixed finite counter saturated at `2^21`;
it does not hold an input-sized natural number. The source is consumed
onto a scratch stack, missing cells are added, then that stack is restored
to the unary output. Every transition is charged.

Source: frozen v8 `E-exact-details.tex`, lower cutoff in the scalar formulas.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineCutoff

open Turing Turing.TM2.Stmt BitMachineEncoding

def cutoff : ℕ := 2 ^ 21

abbrev Count := Fin (cutoff + 1)
abbrev Control := Count × Bool

inductive Label where
  | scan | pad | restore
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def sat (n : ℕ) : Count := ⟨min cutoff n, by omega⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan => pop 0 (fun v b => (v.1, b.isSome))
      (branch Prod.snd
        (push 2 (fun _ => true)
          (load (fun v => (sat (v.1.val + 1), false)) (goto (fun _ => .scan))))
        (goto (fun _ => .pad)))
  | .pad => branch (fun v => v.1.val < cutoff)
      (push 2 (fun _ => true)
        (load (fun v => (sat (v.1.val + 1), false)) (goto (fun _ => .pad))))
      (goto (fun _ => .restore))
  | .restore => pop 2 (fun v b => (v.1, b.isSome))
      (branch Prod.snd
        (push 1 (fun _ => true) (goto (fun _ => .restore)))
        (load (fun v => (v.1, false)) halt))

def cfg (l : Option Label) (count : ℕ) (flag : Bool)
    (input output scratch : List Bool) : Config :=
  ⟨l, (sat count, flag), ![input, output, scratch]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add (m n : ℕ) (c : Config) : run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) n m c

private theorem scan_cons (n : ℕ) (q out scratch : List Bool) :
    advance program (cfg (some .scan) n false (true :: q) out scratch) =
      cfg (some .scan) (n + 1) false q out (true :: scratch) := by
  have hs : min cutoff (min cutoff n + 1) = min cutoff (n + 1) := by
    omega
  simp [advance, program, cfg, TM2.step, TM2.stepAux, sat, hs]
  funext k
  fin_cases k <;> rfl

private theorem scan_nil (n : ℕ) (out scratch : List Bool) :
    advance program (cfg (some .scan) n false [] out scratch) =
      cfg (some .pad) n false [] out scratch := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem replicate_commute (k : ℕ) (scratch : List Bool) :
    List.replicate k true ++ true :: scratch =
      true :: (List.replicate k true ++ scratch) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, List.append_assoc] using ih

theorem scan_run (n k : ℕ) (out scratch : List Bool) :
    run (k + 1) (cfg (some .scan) n false (List.replicate k true) out scratch) =
      cfg (some .pad) (n + k) false [] out (List.replicate k true ++ scratch) := by
  induction k generalizing n scratch with
  | zero => simp [run, scan_nil]
  | succ k ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [scan_cons]
      have hh := ih (n + 1) (true :: scratch)
      rw [replicate_commute] at hh
      simpa [run, List.replicate_succ, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh

private theorem pad_cons {n : ℕ} (hn : n < cutoff) (out scratch : List Bool) :
    advance program (cfg (some .pad) n false [] out scratch) =
      cfg (some .pad) (n + 1) false [] out (true :: scratch) := by
  have hs : (sat n).val = n := by simp [sat, Nat.min_eq_right (Nat.le_of_lt hn)]
  simp [advance, program, cfg, TM2.step, TM2.stepAux, hs, hn]
  funext k
  fin_cases k <;> rfl

private theorem pad_done {n : ℕ} (hn : cutoff ≤ n) (out scratch : List Bool) :
    advance program (cfg (some .pad) n false [] out scratch) =
      cfg (some .restore) n false [] out scratch := by
  have hs : (sat n).val = cutoff := by simp [sat, Nat.min_eq_left hn]
  simp [advance, program, cfg, TM2.step, TM2.stepAux, hs]

private theorem pad_run (n k : ℕ) (h : n + k = cutoff) (out scratch : List Bool) :
    run (k + 1) (cfg (some .pad) n false [] out scratch) =
      cfg (some .restore) cutoff false [] out (List.replicate k true ++ scratch) := by
  induction k generalizing n scratch with
  | zero =>
      have hn : n = cutoff := by omega
      subst n
      simpa [run] using pad_done (n := cutoff) (by omega) out scratch
  | succ k ih =>
      have hn : n < cutoff := by omega
      rw [run, Function.iterate_succ_apply, pad_cons hn]
      simpa [run, List.replicate_succ', List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (n+1) (by omega) (true :: scratch)

private theorem restore_cons (n : ℕ) (flag : Bool) (out scratch : List Bool) :
    advance program (cfg (some .restore) n flag [] out (true :: scratch)) =
      cfg (some .restore) n true [] (true :: out) scratch := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (n : ℕ) (flag : Bool) (out : List Bool) :
    advance program (cfg (some .restore) n flag [] out []) =
      cfg none n false [] out [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem restore_run (n k : ℕ) (out : List Bool) (flag : Bool) :
    run (k + 1) (cfg (some .restore) n flag [] out (List.replicate k true)) =
      cfg none n false [] (List.replicate k true ++ out) [] := by
  induction k generalizing out flag with
  | zero =>
      simpa [run] using restore_nil n flag out
  | succ k ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [restore_cons]
      have hh := ih (true :: out) true
      rw [replicate_commute] at hh
      simpa [run, List.replicate_succ, List.append_assoc] using hh

theorem exact_run (n : ℕ) :
    run (if n < cutoff then (n+1)+(cutoff-n+1)+(cutoff+1)
         else (n+1)+1+(n+1))
      (cfg (some .scan) 0 false (List.replicate n true) [] []) =
      cfg none cutoff false [] (List.replicate (max cutoff n) true) [] := by
  have hscan := scan_run 0 n [] []
  simp only [zero_add, List.append_nil] at hscan
  by_cases hn : n < cutoff
  · have hdiff : n + (cutoff - n) = cutoff := by omega
    have hpad := pad_run n (cutoff-n) hdiff [] (List.replicate n true)
    have hrestore := restore_run cutoff cutoff [] false
    have hs : List.replicate (cutoff-n) true ++ List.replicate n true =
        List.replicate cutoff true := by
      rw [← List.replicate_add]
      have he : cutoff - n + n = cutoff := by omega
      exact congrArg (fun k => List.replicate k true) he
    rw [hs] at hpad
    rw [if_pos hn, run_add (n+1+(cutoff-n+1)) (cutoff+1),
      run_add (n+1) (cutoff-n+1), hscan, hpad, hrestore]
    simp [Nat.max_eq_left (Nat.le_of_lt hn)]
  · have hpad := pad_done (n := n) (by omega) [] (List.replicate n true)
    have hrestore := restore_run n n [] false
    rw [if_neg hn, run_add (n+1+1) (n+1), run_add (n+1) 1, hscan]
    change run (n+1) (advance program (cfg (some .pad) n false [] []
      (List.replicate n true))) = _
    rw [hpad, hrestore]
    simp [cfg, sat, Nat.min_eq_left (by omega : cutoff ≤ n),
      Nat.max_eq_right (by omega : cutoff ≤ n)]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) (1 : Fin 3) .scan (sat 0, false) program

theorem outputs (n : ℕ) :
    machine.OutputsWithin (List.replicate n true)
      (List.replicate (max cutoff n) true) (2*n + 2*cutoff + 3) := by
  have hi : rawInit (0 : Fin 3) Label.scan (sat 0, false)
      (List.replicate n true) =
      cfg (some .scan) 0 false (List.replicate n true) [] [] := by
    simp [rawInit, cfg]
    congr 1
    funext k
    fin_cases k <;> rfl
  let t := if n < cutoff then (n+1)+(cutoff-n+1)+(cutoff+1)
           else (n+1)+1+(n+1)
  have ht : t ≤ 2*n + 2*cutoff + 3 := by
    dsimp [t]
    split_ifs <;> omega
  apply outputsWithin_of_raw_run (0 : Fin 3) (1 : Fin 3) .scan (sat 0, false)
    program (List.replicate n true) (List.replicate (max cutoff n) true)
    t (2*n + 2*cutoff + 3) ht
  · rw [hi]; exact congrArg TM2.Cfg.l (exact_run n)
  · rw [hi]; exact congrArg (fun c => c.stk 1) (exact_run n)

noncomputable def sourceExponentMachine : BitMachine.Machine :=
  BitMachineComposition.composition ExactParameterMachineScale.nestedLogMachine machine

theorem sourceExponent_outputs (edges : ℕ) :
    ∃ T, sourceExponentMachine.OutputsWithin (List.replicate edges true)
      (List.replicate (ExactSourcePadding.paddedExponent edges) true) T := by
  have h := BitMachineComposition.composition_outputsWithin
    ExactParameterMachineScale.nestedLogMachine machine
    (ExactParameterMachineScale.nestedLog_outputs edges)
    (outputs (Nat.clog 2 (Nat.clog 2 (max 1 (5*edges)))))
  have he : ExactSourcePadding.paddedExponent edges =
      max cutoff (Nat.clog 2 (Nat.clog 2 (max 1 (5*edges)))) := rfl
  rw [he]
  exact ⟨_, h⟩

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  rw [ExactParameterMachineLog.clog_eq_pred_bits_length]
  exact (UnaryBinaryEncoding.bits_length_le (n-1)).trans (Nat.sub_le n 1)

/-- The entire source exponent, including the fixed `2^21` cutoff, is
produced in a polynomial number of *physical* Boolean-stack transitions. -/
theorem sourceExponent_polynomial (edges : ℕ) :
    sourceExponentMachine.OutputsWithin (List.replicate edges true)
      (List.replicate (ExactSourcePadding.paddedExponent edges) true)
      (100*(UnaryBinaryEncoding.coefficient+cutoff+10)*(edges+1)^2) := by
  let q := max 1 (5*edges)
  let l := Nat.clog 2 q
  let k := Nat.clog 2 l
  have h := BitMachineComposition.composition_outputsWithin
    ExactParameterMachineScale.nestedLogMachine machine
    (ExactParameterMachineScale.nestedLog_outputs edges) (outputs k)
  have he : ExactSourcePadding.paddedExponent edges = max cutoff k := rfl
  rw [he]
  apply BitMachine.outputsWithin_mono _ h
  simp only [List.length_replicate]
  change edges+1 + 2*q+2 + (UnaryBinaryEncoding.coefficient+6)*(q+1)^2 +
      2*l+2+(UnaryBinaryEncoding.coefficient+6)*(l+1)^2 + 2*k+2 +
      (2*k+2*cutoff+3) ≤
      100*(UnaryBinaryEncoding.coefficient+cutoff+10)*(edges+1)^2
  have hx : 1 ≤ edges+1 := by omega
  have hq : q ≤ 5*(edges+1) := by dsimp [q]; omega
  have hl : l ≤ q := clog_le_self q
  have hk : k ≤ l := clog_le_self l
  have hq1 : q+1 ≤ 6*(edges+1) := by omega
  have hl1 : l+1 ≤ 6*(edges+1) := by omega
  have hq2 := Nat.pow_le_pow_left hq1 2
  have hl2 := Nat.pow_le_pow_left hl1 2
  have hq2' : (q+1)^2 ≤ 36*(edges+1)^2 := by nlinarith
  have hl2' : (l+1)^2 ≤ 36*(edges+1)^2 := by nlinarith
  have hx2 : edges+1 ≤ (edges+1)^2 := by nlinarith
  have hlin : q ≤ 5*(edges+1)^2 ∧ l ≤ 5*(edges+1)^2 ∧
      k ≤ 5*(edges+1)^2 := by omega
  rcases hlin with ⟨hql, hll, hkl⟩
  have hcut : cutoff ≤ cutoff*(edges+1)^2 := by
    exact Nat.le_mul_of_pos_right cutoff (by positivity)
  nlinarith [Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+6) hq2',
    Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+6) hl2']

end EthInapproximability.CurrentPaper.ExactParameterMachineCutoff
