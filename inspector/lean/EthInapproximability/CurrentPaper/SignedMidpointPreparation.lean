import EthInapproximability.CurrentPaper.EncodedETHTail
import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-!
# Physical preparation for the signed midpoint test

Source: frozen v8 `06-eth.tex`, proof of `thm:main`. This finite Boolean-stack
program reads a physically supplied signed integer word. On a nonnegative
word it extracts the magnitude field and leaves the bits of twice its value
on a work stack. A negative sign takes the always-accept branch, since the
comparison cap is nonnegative. The unary cap is untouched. Arbitrary malformed
words terminate; their acceptance behavior is not used for the approximation
theorem, whose output codec is canonical.

This preparation does not construct the cap, run the bounded comparator, or
constitute the full ETH decider.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointPreparation

open Turing Turing.TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where
  | sign | tag | payload | reverse
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

/-- Stacks: signed input, unary cap, reversed payload, doubled binary value,
decision output. The cap and decision stack remain untouched on the positive
branch until the caller enters the comparison routine. -/
def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .sign =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (branch (fun b => b.getD false)
            (push 4 (fun _ => true) halt)
            (goto (fun _ => .tag)))
          (push 4 (fun _ => false) halt))
  | .tag =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (branch (fun b => b.getD false)
            (goto (fun _ => .payload))
            (goto (fun _ => .reverse)))
          (push 4 (fun _ => false) halt))
  | .payload =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (push 2 (fun b => b.getD false) (goto (fun _ => .tag)))
          (push 4 (fun _ => false) halt))
  | .reverse =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun b => b.getD false) (goto (fun _ => .reverse)))
          (push 3 (fun _ => false) halt))

abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Control

def cfg (l : Option Label) (v : Control) (input cap saved value out : List Bool) : Config :=
  ⟨l, v, ![input, cap, saved, value, out]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) : run (t + 1) c = run t (advance program c) := by
  exact Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run, Nat.add_comm t u, Function.iterate_add_apply]

theorem sign_nonnegative (input cap saved value out : List Bool) :
    advance program (cfg (some .sign) none (false :: input) cap saved value out) =
      cfg (some .tag) (some false) input cap saved value out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem sign_negative (input cap saved value out : List Bool) :
    advance program (cfg (some .sign) none (true :: input) cap saved value out) =
      cfg none (some true) input cap saved value (true :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem tag_payload (b : Bool) (input cap saved value out : List Bool) (v : Control) :
    run 2 (cfg (some .tag) v (true :: b :: input) cap saved value out) =
      cfg (some .tag) (some b) input cap (b :: saved) value out := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem tag_end (input cap saved value out : List Bool) (v : Control) :
    advance program (cfg (some .tag) v (false :: input) cap saved value out) =
      cfg (some .reverse) (some false) input cap saved value out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem tag_nil (v : Control) (cap saved value out : List Bool) :
    advance program (cfg (some .tag) v [] cap saved value out) =
      cfg none none [] cap saved value (false :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem payload_nil (v : Control) (cap saved value out : List Bool) :
    run 2 (cfg (some .tag) v [true] cap saved value out) =
      cfg none none [] cap saved value (false :: out) := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem reverse_cons (b : Bool) (input cap saved value out : List Bool) (v : Control) :
    advance program (cfg (some .reverse) v input cap (b :: saved) value out) =
      cfg (some .reverse) (some b) input cap saved (b :: value) out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem reverse_nil (v : Control) (input cap value out : List Bool) :
    advance program (cfg (some .reverse) v input cap [] value out) =
      cfg none none input cap [] (false :: value) out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem reverse_run (saved input cap value out : List Bool) (v : Control) :
    run (saved.length + 1) (cfg (some .reverse) v input cap saved value out) =
      cfg none none input cap [] (false :: (saved.reverse ++ value)) out := by
  induction saved generalizing v value with
  | nil => simpa [run] using reverse_nil v input cap value out
  | cons b saved ih =>
      rw [List.length_cons, run_succ, reverse_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Every canonical magnitude field is parsed with a concrete linear number
of transitions. The doubled LSB-first bits are ready for a bounded comparison
against the unchanged unary cap. -/
theorem field_run (bs suffix cap saved value out : List Bool) (v : Control) :
    run (2 * bs.length + 1)
      (cfg (some .tag) v (field bs ++ suffix) cap saved value out) =
      cfg (some .reverse) (some false) suffix cap (bs.reverse ++ saved) value out := by
  induction bs generalizing saved v with
  | nil => simpa [field, run] using tag_end suffix cap saved value out v
  | cons b bs ih =>
      rw [show 2 * (b :: bs).length + 1 = 2 + (2 * bs.length + 1) by simp; omega,
        run_add]
      simp only [field, List.cons_append]
      rw [tag_payload b (field bs ++ suffix) cap saved value out v]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: saved) (some b)

/-- The preparation phase has a length bound even on truncated or malformed
signed words. This all-input fact is needed before wrapping it as a total
bit-machine subroutine. -/
theorem tag_total (input cap saved value out : List Bool) (v : Control) :
    ∃ t ≤ 2 * input.length + saved.length + 2,
      (run t (cfg (some .tag) v input cap saved value out)).l = none := by
  induction input using readField.induct generalizing saved v with
  | case1 =>
      refine ⟨1, by simp, ?_⟩
      rw [show 1 = 0 + 1 from rfl, run_succ, tag_nil]
      rfl
  | case2 rest =>
      refine ⟨saved.length + 2, by simp, ?_⟩
      rw [show saved.length + 2 = (saved.length + 1) + 1 by omega,
        run_succ, tag_end, reverse_run]
      rfl
  | case3 =>
      refine ⟨2, by simp, ?_⟩
      rw [payload_nil]
      rfl
  | case4 b rest ih =>
      obtain ⟨t, ht, hh⟩ := ih (b :: saved) (some b)
      refine ⟨t + 2, by simp at ht ⊢; omega, ?_⟩
      rw [show t + 2 = 2 + t by omega, run_add, tag_payload b rest cap saved value out v]
      exact hh

theorem sign_nil (cap saved value out : List Bool) :
    advance program (cfg (some .sign) none [] cap saved value out) =
      cfg none none [] cap saved value (false :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem total (input cap : List Bool) :
    ∃ t ≤ 3 * input.length + 3,
      (run t (cfg (some .sign) none input cap [] [] [])).l = none := by
  cases input with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      rw [show 1 = 0 + 1 from rfl, run_succ, sign_nil]
      rfl
  | cons sign rest =>
      cases sign with
      | true =>
          refine ⟨1, by simp, ?_⟩
          rw [show 1 = 0 + 1 from rfl, run_succ, sign_negative]
          rfl
      | false =>
          obtain ⟨t, ht, hh⟩ := tag_total rest cap [] [] [] (some false)
          refine ⟨t + 1, by simp at ht ⊢; omega, ?_⟩
          rw [show t + 1 = 1 + t by omega, run_add]
          have hs : run 1 (cfg (some .sign) none (false :: rest) cap [] [] []) =
              cfg (some .tag) (some false) rest cap [] [] [] := by
            simpa [run] using sign_nonnegative rest cap [] [] []
          rw [hs]
          exact hh

theorem nonnegative_run (bs cap : List Bool) :
    run (3 * bs.length + 3)
      (cfg (some .sign) none (false :: field bs) cap [] [] []) =
      cfg none none [] cap [] (false :: bs) [] := by
  have hs : run 1 (cfg (some .sign) none (false :: field bs) cap [] [] []) =
      cfg (some .tag) (some false) (field bs) cap [] [] [] := by
    simpa [run] using sign_nonnegative (field bs) cap [] [] []
  have hf := field_run bs [] cap [] [] [] (some false)
  have hr := reverse_run bs.reverse [] cap [] [] (some false)
  simp only [List.append_nil] at hf
  simp only [List.append_nil, List.reverse_reverse] at hr
  simp only [List.length_reverse] at hr
  calc
    run (3 * bs.length + 3)
        (cfg (some .sign) none (false :: field bs) cap [] [] []) =
      run (bs.length + 1) (run (2 * bs.length + 1)
        (run 1 (cfg (some .sign) none (false :: field bs) cap [] [] []))) := by
          rw [← run_add, ← run_add]
          congr 1
          omega
    _ = cfg none none [] cap [] (false :: bs) [] := by
      rw [hs]
      exact (congrArg (run (bs.length + 1)) hf).trans hr

theorem encoded_nonnegative_run (n : ℕ) (cap : List Bool) :
    run (3 * n.bits.length + 3)
      (cfg (some .sign) none (EncodedETHTail.encodeInteger (n : ℤ)) cap [] [] []) =
      cfg none none [] cap [] (false :: n.bits) [] := by
  have hn : ¬ ((n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
  simpa [EncodedETHTail.encodeInteger, natField, hn] using nonnegative_run n.bits cap

theorem encoded_negative_run (n : ℕ) (cap : List Bool) :
    run 1 (cfg (some .sign) none
      (EncodedETHTail.encodeInteger (Int.negSucc n)) cap [] [] []) =
      cfg none (some true) (natField (n + 1)) cap [] [] [true] := by
  have hn : Int.negSucc n < 0 := by omega
  simpa [EncodedETHTail.encodeInteger, Int.natAbs_negSucc, hn, run] using
    sign_negative (natField (n + 1)) cap [] [] []

/-- The existing four-stack bounded converter is the operational comparison
kernel. One physical cap cell implements strict inequality, and the prepared
leading false bit implements doubling of the answer magnitude. Its output
starts with the decision bit, followed by a unary counting residue. The
residue is not silently treated as an already cleaned single-bit output. -/
theorem positive_bounded_comparison (n : ℕ) (b : Bool) (cap : List Bool) :
    ∃ t c,
      t ≤ (cap.length + 1) * (4 * (false :: n.bits).length + 5) ∧
      ProtocolBoundedUnary.run t
        (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
          (false :: n.bits) cap [] []) = c ∧
      c.l = none ∧
      (c.stk 3).head? = some (decide (2 * (n : ℤ) < ((b :: cap).length : ℤ))) := by
  obtain ⟨t, c, ht, hr, hh, ho, _, _, _⟩ :=
    ProtocolBoundedUnary.bounded_run_framed (false :: n.bits) cap []
  refine ⟨t, c, ht, hr, hh, ?_⟩
  rw [ho]
  have hv : bitsValue (false :: n.bits) = 2 * n := by simp [bitsValue, Nat.bit_val]
  simp only [ProtocolBoundedUnary.result, List.head?_cons, hv]
  have heq : (2 * n ≤ cap.length) =
      (2 * (n : ℤ) < ((b :: cap).length : ℤ)) := by
    apply propext
    simp only [List.length_cons]
    omega
  simp only [← heq]

end EthInapproximability.CurrentPaper.SignedMidpointPreparation
