import CurrentAdditive.DivisionRepackBridge

/-!
A single literal five-stack TM2 program for the inner polynomial-division
loop. Stack 4 holds a unary iteration count. Stacks 0 and 1 hold aligned
high-first accumulator and shifted divisor words. Stacks 2 and 3 are
scratch. Every iteration samples the accumulator top bit, conditionally
XORs the shifted monic divisor, drops the canceled top bit, and discards
the divisor's last bit before returning to the counter check.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialDividerMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | next | xorScan | xorRestore | dropAcc | scanDiv | dropTail | restoreDiv
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .next => pop 4 (fun s bit => (s.1, bit, none))
      (branch (fun s => s.2.1.isSome)
        (peek 0 (fun _ bit => (bit.getD false, none, none))
          (goto (fun _ => .xorScan)))
        halt)
  | .xorScan => pop 0 (fun s x => (s.1, x, none))
      (pop 1 (fun s y => (s.1, s.2.1, y))
        (branch (fun s => s.2.1.isSome)
          (push 2 (fun s => Bool.xor (s.2.1.getD false) (s.1 && s.2.2.getD false))
            (push 3 (fun s => s.2.2.getD false) (goto (fun _ => .xorScan))))
          (goto (fun _ => .xorRestore))))
  | .xorRestore => pop 2 (fun s x => (s.1, x, none))
      (pop 3 (fun s y => (s.1, s.2.1, y))
        (branch (fun s => s.2.1.isSome)
          (push 0 (fun s => s.2.1.getD false)
            (push 1 (fun s => s.2.2.getD false) (goto (fun _ => .xorRestore))))
          (load (fun s => (s.1, none, none)) (goto (fun _ => .dropAcc)))))
  | .dropAcc => pop 0 (fun s x => (s.1, x, none))
      (load (fun s => (s.1, none, none)) (goto (fun _ => .scanDiv)))
  | .scanDiv => pop 1 (fun s x => (s.1, x, none))
      (branch (fun s => s.2.1.isSome)
        (push 2 (fun s => s.2.1.getD false)
          (load (fun s => (s.1, none, none)) (goto (fun _ => .scanDiv))))
        (goto (fun _ => .dropTail)))
  | .dropTail => pop 2 (fun s x => (s.1, x, none))
      (load (fun s => (s.1, none, none)) (goto (fun _ => .restoreDiv)))
  | .restoreDiv => pop 2 (fun s x => (s.1, x, none))
      (branch (fun s => s.2.1.isSome)
        (push 1 (fun s => s.2.1.getD false)
          (load (fun s => (s.1, none, none)) (goto (fun _ => .restoreDiv))))
        (goto (fun _ => .next)))

def bank (acc divisor scratchAcc scratchDiv count : List Bool) : Fin 5 → List Bool :=
  fun k => if k = 0 then acc else if k = 1 then divisor else if k = 2 then
    scratchAcc else if k = 3 then scratchDiv else count

def cfg (l : Option Label) (s : Control)
    (acc divisor scratchAcc scratchDiv count : List Bool) : Config :=
  ⟨l, s, bank acc divisor scratchAcc scratchDiv count⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

open EthInapproximability.CurrentPaper.SamplerMachineAccumulate (addScaled)

private theorem step_xorScan_cons (b : Bool) (p q : Option Bool)
    (x y : Bool) (u v su sv count : List Bool) :
    TM2.step program
      (cfg (some .xorScan) (b, p, q) (x :: u) (y :: v) su sv count) =
      some (cfg (some .xorScan) (b, some x, some y) u v
        (Bool.xor x (b && y) :: su) (y :: sv) count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_xorScan_nil (b : Bool) (p q : Option Bool)
    (su sv count : List Bool) :
    TM2.step program (cfg (some .xorScan) (b, p, q) [] [] su sv count) =
      some (cfg (some .xorRestore) (b, none, none) [] [] su sv count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_xorRestore_cons (b : Bool) (p q : Option Bool)
    (x y : Bool) (u v su sv count : List Bool) :
    TM2.step program
      (cfg (some .xorRestore) (b, p, q) u v (x :: su) (y :: sv) count) =
      some (cfg (some .xorRestore) (b, some x, some y)
        (x :: u) (y :: v) su sv count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_xorRestore_nil (b : Bool) (p q : Option Bool)
    (u v count : List Bool) :
    TM2.step program (cfg (some .xorRestore) (b, p, q) u v [] [] count) =
      some (cfg (some .dropAcc) (b, none, none) u v [] [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

theorem xorScan_run (b : Bool) (p q : Option Bool)
    (u v su sv count : List Bool) (hlen : u.length = v.length) :
    run (u.length + 1) (cfg (some .xorScan) (b, p, q) u v su sv count) =
      cfg (some .xorRestore) (b, none, none) [] []
        ((addScaled b u v).reverse ++ su) (v.reverse ++ sv) count := by
  induction u generalizing v p q su sv with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    simpa [addScaled] using run_succ (step_xorScan_nil b p q su sv count) 0
  | cons x u ih =>
    cases v with
    | nil => simp at hlen
    | cons y v =>
      have hl : u.length = v.length := by simpa using hlen
      rw [List.length_cons,
        run_succ (step_xorScan_cons b p q x y u v su sv count)]
      simpa [addScaled, List.reverse_cons, List.append_assoc] using
        ih (some x) (some y) v (Bool.xor x (b && y) :: su) (y :: sv) hl

theorem xorRestore_run (b : Bool) (p q : Option Bool)
    (u v su sv count : List Bool) (hlen : su.length = sv.length) :
    run (su.length + 1)
      (cfg (some .xorRestore) (b, p, q) u v su sv count) =
      cfg (some .dropAcc) (b, none, none)
        (su.reverse ++ u) (sv.reverse ++ v) [] [] count := by
  induction su generalizing sv p q u v with
  | nil =>
    have hv : sv = [] := List.length_eq_zero_iff.mp hlen.symm
    subst sv
    simpa using run_succ (step_xorRestore_nil b p q u v count) 0
  | cons x su ih =>
    cases sv with
    | nil => simp at hlen
    | cons y sv =>
      have hl : su.length = sv.length := by simpa using hlen
      rw [List.length_cons,
        run_succ (step_xorRestore_cons b p q x y u v su sv count)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some x) (some y) (x :: u) (y :: v) sv hl

theorem xorRun (b : Bool) (u v count : List Bool)
    (hlen : u.length = v.length) :
    run (2 * u.length + 2)
      (cfg (some .xorScan) (b, none, none) u v [] [] count) =
    cfg (some .dropAcc) (b, none, none) (addScaled b u v) v [] [] count := by
  have hl : (addScaled b u v).length = u.length := by simp [addScaled, hlen]
  have hs := xorScan_run b none none u v [] [] count hlen
  simp only [List.append_nil] at hs
  have hr := xorRestore_run b none none [] []
    (addScaled b u v).reverse v.reverse count (by
      simp only [List.length_reverse, hl, hlen])
  simp only [List.length_reverse, hl, List.reverse_reverse, List.append_nil] at hr
  have h := (congrArg (run (u.length + 1)) hs).trans hr
  have ht : u.length + 1 + (u.length + 1) = 2 * u.length + 2 := by omega
  rwa [← run_add, ht] at h

private theorem step_dropAcc (b top : Bool)
    (acc divisor count : List Bool) :
    TM2.step program
      (cfg (some .dropAcc) (b, none, none)
        (top :: acc) divisor [] [] count) =
      some (cfg (some .scanDiv) (b, none, none)
        acc divisor [] [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_scanDiv_cons (b x : Bool)
    (acc divisor scratch count : List Bool) :
    TM2.step program
      (cfg (some .scanDiv) (b, none, none)
        acc (x :: divisor) scratch [] count) =
      some (cfg (some .scanDiv) (b, none, none)
        acc divisor (x :: scratch) [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_scanDiv_nil (b : Bool)
    (acc scratch count : List Bool) :
    TM2.step program
      (cfg (some .scanDiv) (b, none, none) acc [] scratch [] count) =
      some (cfg (some .dropTail) (b, none, none)
        acc [] scratch [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_dropTail (b last : Bool)
    (acc scratch count : List Bool) :
    TM2.step program
      (cfg (some .dropTail) (b, none, none)
        acc [] (last :: scratch) [] count) =
      some (cfg (some .restoreDiv) (b, none, none)
        acc [] scratch [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_restoreDiv_cons (b x : Bool)
    (acc divisor scratch count : List Bool) :
    TM2.step program
      (cfg (some .restoreDiv) (b, none, none)
        acc divisor (x :: scratch) [] count) =
      some (cfg (some .restoreDiv) (b, none, none)
        acc (x :: divisor) scratch [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_restoreDiv_nil (b : Bool)
    (acc divisor count : List Bool) :
    TM2.step program
      (cfg (some .restoreDiv) (b, none, none) acc divisor [] [] count) =
      some (cfg (some .next) (b, none, none) acc divisor [] [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem scanDiv_run (b : Bool)
    (acc divisor scratch count : List Bool) :
    run (divisor.length + 1)
      (cfg (some .scanDiv) (b, none, none)
        acc divisor scratch [] count) =
    cfg (some .dropTail) (b, none, none)
      acc [] (divisor.reverse ++ scratch) [] count := by
  induction divisor generalizing scratch with
  | nil => simpa using run_succ (step_scanDiv_nil b acc scratch count) 0
  | cons x rest ih =>
    rw [List.length_cons,
      run_succ (step_scanDiv_cons b x acc rest scratch count)]
    simpa [List.reverse_cons, List.append_assoc] using ih (x :: scratch)

theorem restoreDiv_run (b : Bool)
    (acc divisor scratch count : List Bool) :
    run (scratch.length + 1)
      (cfg (some .restoreDiv) (b, none, none)
        acc divisor scratch [] count) =
    cfg (some .next) (b, none, none)
      acc (scratch.reverse ++ divisor) [] [] count := by
  induction scratch generalizing divisor with
  | nil => simpa using run_succ (step_restoreDiv_nil b acc divisor count) 0
  | cons x rest ih =>
    rw [List.length_cons,
      run_succ (step_restoreDiv_cons b x acc divisor rest count)]
    simpa [List.reverse_cons, List.append_assoc] using ih (x :: divisor)

theorem repackRun (b top last : Bool)
    (acc pre count : List Bool) :
    run (2 * (pre.length + 1) + 3)
      (cfg (some .dropAcc) (b, none, none)
        (top :: acc) (pre ++ [last]) [] [] count) =
    cfg (some .next) (b, none, none) acc pre [] [] count := by
  have hdrop : run 1
      (cfg (some .dropAcc) (b, none, none)
        (top :: acc) (pre ++ [last]) [] [] count) =
      cfg (some .scanDiv) (b, none, none)
        acc (pre ++ [last]) [] [] count := by
    simpa using run_succ (step_dropAcc b top acc (pre ++ [last]) count) 0
  have hscan := scanDiv_run b acc (pre ++ [last]) [] count
  have htail : run 1
      (cfg (some .dropTail) (b, none, none)
        acc [] (last :: pre.reverse) [] count) =
      cfg (some .restoreDiv) (b, none, none)
        acc [] pre.reverse [] count := by
    simpa using run_succ (step_dropTail b last acc pre.reverse count) 0
  have hrestore := restoreDiv_run b acc [] pre.reverse count
  have hfirst : run (1 + ((pre ++ [last]).length + 1))
      (cfg (some .dropAcc) (b, none, none)
        (top :: acc) (pre ++ [last]) [] [] count) =
      cfg (some .dropTail) (b, none, none)
        acc [] (last :: pre.reverse) [] count := by
    rw [run_add, hdrop, hscan]
    simp
  have hsecond : run (1 + ((pre ++ [last]).length + 1) + 1)
      (cfg (some .dropAcc) (b, none, none)
        (top :: acc) (pre ++ [last]) [] [] count) =
      cfg (some .restoreDiv) (b, none, none)
        acc [] pre.reverse [] count := by
    rw [run_add, hfirst, htail]
  have hbudget : 2 * (pre.length + 1) + 3 =
      1 + ((pre ++ [last]).length + 1) +
        1 + (pre.reverse.length + 1) := by simp; omega
  rw [hbudget, run_add, hsecond, hrestore]
  simp

private theorem step_next_cons (b top marker : Bool)
    (acc divisor count : List Bool) :
    TM2.step program
      (cfg (some .next) (b, none, none)
        (top :: acc) divisor [] [] (marker :: count)) =
      some (cfg (some .xorScan) (top, none, none)
        (top :: acc) divisor [] [] count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_next_nil (b : Bool)
    (acc divisor : List Bool) :
    TM2.step program
      (cfg (some .next) (b, none, none) acc divisor [] [] []) =
      some (cfg none (b, none, none) acc divisor [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

/-- One full iteration of the single finite-control divider program. -/
theorem oneIteration (b top last : Bool)
    (accTail divisorTail pre count : List Bool)
    (hlen : accTail.length = divisorTail.length)
    (hshape : true :: divisorTail = pre ++ [last]) :
    run (4 * (pre.length + 1) + 6)
      (cfg (some .next) (b, none, none)
        (top :: accTail) (true :: divisorTail) [] [] (true :: count)) =
    cfg (some .next) (top, none, none)
      (addScaled top accTail divisorTail) pre [] [] count := by
  have hnext : run 1
      (cfg (some .next) (b, none, none)
        (top :: accTail) (true :: divisorTail) [] [] (true :: count)) =
      cfg (some .xorScan) (top, none, none)
        (top :: accTail) (true :: divisorTail) [] [] count := by
    simpa using run_succ
      (step_next_cons b top true accTail (true :: divisorTail) count) 0
  have hxor := xorRun top (top :: accTail) (true :: divisorTail) count
    (by simpa using hlen)
  rw [CurrentAdditive.FieldMachineHelper.DivisionBitStep.addScaled_monic_head] at hxor
  have hxor' : run (2 * (pre.length + 1) + 2)
      (cfg (some .xorScan) (top, none, none)
        (top :: accTail) (true :: divisorTail) [] [] count) =
      cfg (some .dropAcc) (top, none, none)
        (false :: addScaled top accTail divisorTail)
        (pre ++ [last]) [] [] count := by
    have hp : pre.length = accTail.length := by
      have hs := congrArg List.length hshape
      simp at hs
      omega
    simpa [hp, hshape] using hxor
  have hrep := repackRun top false last
    (addScaled top accTail divisorTail) pre count
  have hclock : 4 * (pre.length + 1) + 6 =
      1 + (2 * (pre.length + 1) + 2) +
        (2 * (pre.length + 1) + 3) := by omega
  rw [hclock]
  rw [run_add (1 + (2 * (pre.length + 1) + 2))
    (2 * (pre.length + 1) + 3)]
  rw [run_add 1 (2 * (pre.length + 1) + 2)]
  rw [hnext, hxor', hrep]

theorem halt_after_empty_count (b : Bool)
    (acc divisor : List Bool) :
    run 1 (cfg (some .next) (b, none, none) acc divisor [] [] []) =
      cfg none (b, none, none) acc divisor [] [] [] := by
  simpa using run_succ (step_next_nil b acc divisor) 0

open CurrentAdditive.FieldMachineHelper.DivisionBitStep
  (bitsBE bitsBE_succ bitsBE_length cancel_tail_nat_step)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
  (step monicBits_shifted_topBit)

/-- One iteration is the exact arithmetic update in the frozen remainder. -/
theorem oneTrialStep (b : Bool) (e i tail acc : Nat)
    (count : List Bool) (htail : tail < 2 ^ e) :
    run (4 * (e + i + 1) + 6)
      (cfg (some .next) (b, none, none)
        (bitsBE (e + i + 1) acc)
        (bitsBE (e + i + 1) ((monicBits e tail) <<< i))
        [] [] (true :: count)) =
    cfg (some .next) (acc.testBit (e + i), none, none)
      (bitsBE (e + i) (step e i (monicBits e tail) acc))
      (bitsBE (e + i + 1) ((monicBits e tail) <<< i)).dropLast
      [] [] count := by
  let shifted := (monicBits e tail) <<< i
  let word := bitsBE (e + i + 1) shifted
  have htop : shifted.testBit (e + i) = true :=
    monicBits_shifted_topBit e i tail htail
  have hword : word = true :: bitsBE (e + i) shifted := by
    simpa [word, shifted] using (bitsBE_succ (e + i) shifted).trans
      (by rw [htop])
  have hacc : bitsBE (e + i + 1) acc =
      acc.testBit (e + i) :: bitsBE (e + i) acc := by
    simpa [Nat.add_assoc] using bitsBE_succ (e + i) acc
  have hne : word ≠ [] := by rw [hword]; simp
  let last := word.getLast hne
  have hshape : true :: bitsBE (e + i) shifted =
      word.dropLast ++ [last] := by
    rw [← hword]
    exact (List.dropLast_concat_getLast hne).symm
  have hlen : (bitsBE (e + i) acc).length =
      (bitsBE (e + i) shifted).length := by simp [bitsBE_length]
  have h := oneIteration b (acc.testBit (e + i)) last
    (bitsBE (e + i) acc) (bitsBE (e + i) shifted)
    word.dropLast count hlen hshape
  have hp : word.dropLast.length + 1 = e + i + 1 := by
    have hw : word.length = e + i + 1 := by simp [word, bitsBE_length]
    rw [List.length_dropLast]
    omega
  have hstep : addScaled (acc.testBit (e + i))
      (bitsBE (e + i) acc) (bitsBE (e + i) shifted) =
      bitsBE (e + i) (step e i (monicBits e tail) acc) := by
    simpa [step, shifted] using cancel_tail_nat_step (e + i) acc shifted
  rw [hp] at h
  simpa [hacc, hword, hstep, hp, word, shifted] using h

#print axioms oneTrialStep

end CurrentAdditive.FieldMachineHelper.TrialDividerMachine
