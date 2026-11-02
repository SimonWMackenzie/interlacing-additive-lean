import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Data.Nat.Bits

/-!
# U17 serializer bricks (lane owner:a-square-1)

Private, 26 September 2026. Two tiny two-stack programs for the header stage of the OPEN
`ASquare.SquarePost`:

* `PowBits`: from unary `e` (consumed) pushes the canonical binary word of `2^e`
  (`(2^e).bits = replicate e false ++ [true]`, `pow_bits`), i.e. the header word of the square side
  `SquarePadding.side r c = 2^exponent r c` for the admitted `MatrixInstanceEncoding` serializer;
* `Move`: transfers a word onto another stack reversed (used to turn the reversed threshold payload
  left by `ReadField` back into `thr.bits`).

Their join into the full post machine is NOT done here. Does not close a ledger row.
-/

namespace Paper2.ASquare.Bits

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- `(2^e).bits` is `e` zeros followed by a one (little-endian). -/
theorem pow_bits (e : ℕ) : (2 ^ e).bits = List.replicate e false ++ [true] := by
  induction e with
  | zero => simp
  | succ e ih =>
      have h : 2 ^ (e + 1) = Nat.bit false (2 ^ e) := by
        rw [Nat.bit_false, pow_succ]; ring
      rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (by positivity)), ih,
        List.replicate_succ, List.cons_append]

namespace PowBits

inductive Label where
  | init | loop
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Bool
  | .init => push 1 (fun _ => true) (goto (fun _ => .loop))
  | .loop => pop 0 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => false) (goto (fun _ => .loop))) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (a b : List Bool) : Config := ⟨l, s, ![a, b]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_seq {t u : ℕ} {c c' c'' : Config} (h1 : run t c = c') (h2 : run u c' = c'') :
    run (t + u) c = c'' := by rw [run_add, h1, h2]

theorem init_step (s : Bool) (a b : List Bool) :
    advance program (cfg (some .init) s a b) = cfg (some .loop) s a (true :: b) := by
  apply congrArg (fun S => (⟨some .loop, s, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem loop_cons (s x : Bool) (a b : List Bool) :
    advance program (cfg (some .loop) s (x :: a) b) = cfg (some .loop) true a (false :: b) := by
  apply congrArg (fun S => (⟨some .loop, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem loop_nil (s : Bool) (b : List Bool) :
    advance program (cfg (some .loop) s [] b) = cfg none false [] b := by
  apply congrArg (fun S => (⟨none, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem loop_run (a b : List Bool) (s : Bool) :
    run (a.length + 1) (cfg (some .loop) s a b) =
      cfg none false [] (List.replicate a.length false ++ b) := by
  induction a generalizing s b with
  | nil => exact loop_nil s b
  | cons x a ih =>
      have e1 : run 1 (cfg (some .loop) s (x :: a) b) = cfg (some .loop) true a (false :: b) :=
        loop_cons s x a b
      have h := ih (false :: b) true
      rw [show (x :: a).length + 1 = 1 + (a.length + 1) by simp only [List.length_cons]; ring,
        List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
      exact run_seq e1 h

/-- **Binary word of `2^e` from unary `e`.** -/
theorem powbits_run (e : ℕ) (b : List Bool) (s : Bool) :
    run (e + 2) (cfg (some .init) s (List.replicate e true) b) =
      cfg none false [] ((2 ^ e).bits ++ b) := by
  have e1 : run 1 (cfg (some .init) s (List.replicate e true) b) =
      cfg (some .loop) s (List.replicate e true) (true :: b) := init_step s _ b
  have h := loop_run (List.replicate e true) (true :: b) s
  rw [List.length_replicate] at h
  rw [pow_bits, List.append_assoc, List.singleton_append, show e + 2 = 1 + (e + 1) by ring]
  exact run_seq e1 h

end PowBits

namespace Move

inductive Label where
  | mv
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .mv => pop 0 (fun _ b => b)
      (branch Option.isSome (push 1 (fun v => v.getD false) (goto (fun _ => .mv))) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)

def cfg (l : Option Label) (s : Option Bool) (a b : List Bool) : Config := ⟨l, s, ![a, b]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_seq {t u : ℕ} {c c' c'' : Config} (h1 : run t c = c') (h2 : run u c' = c'') :
    run (t + u) c = c'' := by rw [run_add, h1, h2]

theorem mv_cons (s : Option Bool) (x : Bool) (a b : List Bool) :
    advance program (cfg (some .mv) s (x :: a) b) = cfg (some .mv) (some x) a (x :: b) := by
  apply congrArg (fun S => (⟨some .mv, some x, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem mv_nil (s : Option Bool) (b : List Bool) :
    advance program (cfg (some .mv) s [] b) = cfg none none [] b := by
  apply congrArg (fun S => (⟨none, none, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- **Reversing transfer.** -/
theorem move_run (a b : List Bool) (s : Option Bool) :
    run (a.length + 1) (cfg (some .mv) s a b) = cfg none none [] (a.reverse ++ b) := by
  induction a generalizing s b with
  | nil => exact mv_nil s b
  | cons x a ih =>
      have e1 : run 1 (cfg (some .mv) s (x :: a) b) = cfg (some .mv) (some x) a (x :: b) :=
        mv_cons s x a b
      have h := ih (x :: b) (some x)
      rw [show (x :: a).length + 1 = 1 + (a.length + 1) by simp only [List.length_cons]; ring,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      exact run_seq e1 h

end Move

#print axioms pow_bits
#print axioms PowBits.powbits_run
#print axioms Move.move_run

end Paper2.ASquare.Bits
