import EthInapproximability.CurrentPaper.SourceCSPRejectFormula
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical fixed rejecting-CNF writer

One finite machine clears its output stack and writes the fixed 19-bit
canonical contradictory ordered three-CNF. The fixed-size push chain is a
single TM2 statement, so its primitive-operation count is an absolute
constant independent of the source input.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRejectWriter

open Turing TM2.Stmt BitMachineEncoding

inductive Label where
  | clear | write
  deriving DecidableEq, Fintype

abbrev Stack := Fin 1
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def contents (output : List Bool) : Stack → List Bool := fun _ => output

def pushBits : List Bool → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | [] => .halt
  | b :: bs => .push 0 (fun _ => b) (pushBits bs)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .clear => .pop 0 (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .clear))
        (.goto (fun _ => .write)))
  | .write => pushBits SourceCSPRejectFormula.bits.reverse

def run (t : Nat) (output : List Bool) : Config :=
  ((advance program)^[t]) ⟨some .clear, none, contents output⟩

private theorem update_contents (output : List Bool) (b : Bool) :
    Function.update (contents output) (0 : Stack) (b :: output) =
      contents (b :: output) := by
  funext k
  fin_cases k
  rfl

theorem pushBits_step (bs output : List Bool) :
    TM2.stepAux (pushBits bs) none (contents output) =
      ⟨none, none, contents (bs.reverse ++ output)⟩ := by
  induction bs generalizing output with
  | nil => simp [pushBits]
  | cons b bs ih =>
      simp only [pushBits, TM2.stepAux]
      change TM2.stepAux (pushBits bs) none
        (Function.update (contents output) 0 (b :: output)) = _
      rw [update_contents, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem write_step (output : List Bool) :
    advance program
      (⟨some .write, none, contents output⟩ : Config) =
      ⟨none, none, contents (SourceCSPRejectFormula.bits ++ output)⟩ := by
  simpa only [advance, TM2.step, program, List.reverse_reverse] using
    pushBits_step SourceCSPRejectFormula.bits.reverse output

theorem clear_nonempty (v : Option Bool) (b : Bool) (tail : List Bool) :
    advance program
      (⟨some .clear, v, contents (b :: tail)⟩ : Config) =
      ⟨some .clear, some b, contents tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, contents]
  funext k
  fin_cases k
  rfl

theorem clear_empty (v : Option Bool) :
    advance program
      (⟨some .clear, v, contents []⟩ : Config) =
      ⟨some .write, none, contents []⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, contents]

theorem run_exact_from (v : Option Bool) (output : List Bool) :
    ((advance program)^[output.length + 2])
      (⟨some .clear, v, contents output⟩ : Config) =
      ⟨none, none, contents SourceCSPRejectFormula.bits⟩ := by
  induction output generalizing v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, show 2 = 1 + 1 by decide]
      rw [Function.iterate_add_apply]
      simp only [Function.iterate_one, clear_empty, write_step, List.append_nil]
  | cons b tail ih =>
      have hlength : (b :: tail).length + 2 = tail.length + 2 + 1 := by simp
      change ((advance program)^[(b :: tail).length + 2])
        (⟨some .clear, v, contents (b :: tail)⟩ : Config) = _
      rw [hlength, Function.iterate_add_apply]
      simp only [Function.iterate_one, clear_nonempty]
      exact ih (some b)

theorem run_exact (output : List Bool) :
    run (output.length + 2) output =
      ⟨none, none, contents SourceCSPRejectFormula.bits⟩ := by
  exact run_exact_from none output

end EthInapproximability.CurrentPaper.SourceCSPRejectWriter
