import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.MatrixBinaryAddress

/-!
# U17 parser brick: reading one self-delimiting field (lane owner:a-square-1)

Private, 26 September 2026. A two-stack program `ReadField` that consumes one field
`EncodedCommunication.field bs` (pairs `true, b`, then `false`) from the front of the input stack
and pushes the payload onto a second stack, so that stack receives `bs.reverse` (most significant
bit first for `bs = n.bits`). `valueFrom_reverse_bits` shows that this is exactly the word on which
the admitted binary-to-unary program `MatrixBinaryAddress` (`run_correct`, Horner order) produces
unary `n`. These are the first two bricks of the parser stage of the OPEN `ASquare.SquarePost`
(the join into the full parser is NOT done). Does not close a ledger row.
-/

namespace Paper2.ASquare.ReadField

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | read | bit
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Bool
  | .read => pop 0 (fun _ b => b.getD false) (branch id (goto (fun _ => .bit)) halt)
  | .bit => pop 0 (fun _ b => b.getD false) (push 1 id (goto (fun _ => .read)))

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (input out : List Bool) : Config := ⟨l, s, ![input, out]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_seq {t u : ℕ} {c c' c'' : Config} (h1 : run t c = c') (h2 : run u c' = c'') :
    run (t + u) c = c'' := by rw [run_add, h1, h2]

theorem read_true (s : Bool) (input out : List Bool) :
    advance program (cfg (some .read) s (true :: input) out) = cfg (some .bit) true input out := by
  apply congrArg (fun S => (⟨some .bit, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem read_false (s : Bool) (input out : List Bool) :
    advance program (cfg (some .read) s (false :: input) out) = cfg none false input out := by
  apply congrArg (fun S => (⟨none, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem bit_step (s b : Bool) (input out : List Bool) :
    advance program (cfg (some .bit) s (b :: input) out) = cfg (some .read) b input (b :: out) := by
  apply congrArg (fun S => (⟨some .read, b, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- **One field read.** `2|bs|+1` steps consume `field bs` and push `bs.reverse` onto the output
stack, leaving the rest of the input unchanged. -/
theorem read_field (bs rest out : List Bool) (s : Bool) :
    run (2 * bs.length + 1) (cfg (some .read) s (EncodedCommunication.field bs ++ rest) out) =
      cfg none false rest (bs.reverse ++ out) := by
  induction bs generalizing s out with
  | nil => exact read_false s rest out
  | cons b bs ih =>
      have e1 : run 1 (cfg (some .read) s (EncodedCommunication.field (b :: bs) ++ rest) out) =
          cfg (some .bit) true (b :: (EncodedCommunication.field bs ++ rest)) out :=
        read_true s _ out
      have e2 : run 1 (cfg (some .bit) true (b :: (EncodedCommunication.field bs ++ rest)) out) =
          cfg (some .read) b (EncodedCommunication.field bs ++ rest) (b :: out) :=
        bit_step true b _ out
      have h := ih (b :: out) b
      rw [show 2 * (b :: bs).length + 1 = 1 + 1 + (2 * bs.length + 1) by
        simp only [List.length_cons]; ring, List.reverse_cons, List.append_assoc]
      exact run_seq (run_seq e1 e2) h

theorem valueFrom_append (n : ℕ) (l : List Bool) (b : Bool) :
    MatrixBinaryAddress.valueFrom n (l ++ [b]) =
      2 * MatrixBinaryAddress.valueFrom n l + MatrixBinaryAddress.bitVal b := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih => exact ih _

theorem valueFrom_reverse (l : List Bool) :
    MatrixBinaryAddress.valueFrom 0 l.reverse = EncodedCommunication.bitsValue l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [List.reverse_cons, valueFrom_append, ih]
      cases b <;> simp [EncodedCommunication.bitsValue, MatrixBinaryAddress.bitVal, Nat.bit]

/-- The payload pushed by `read_field` on `natField n` is the Horner word of `n`. -/
theorem valueFrom_reverse_bits (n : ℕ) : MatrixBinaryAddress.valueFrom 0 n.bits.reverse = n := by
  rw [valueFrom_reverse, EncodedCommunication.bitsValue_bits]

#print axioms read_field
#print axioms valueFrom_reverse_bits

end Paper2.ASquare.ReadField
