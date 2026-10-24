import Paper2.ASquareSideParts

/-!
# U17 unary side, part 2: ONE fixed program producing the square writer's two counters

Lane `owner:a-square-1` (private, 26 September 2026). The admitted
`Unit4Shell.SquareWriter.square_table` (A4SquareWriter) takes the unary side
`SquarePadding.side m n = 2^clog₂(max m n)` in the writer's row and column counters as a SUPPLIED
start state ("A charged machine producing the unary side ... is NOT built"). This module builds
that stage as ONE fixed Boolean-stack program on 12 stacks, sequenced by the admitted
`BitMachineRawSequence.runs`, each stage inlined by the admitted stack embedding (the admitted
`Unit4Post.embed_run` of `U4PostExponent`):

1. `UMax` (new, `ASquareSideParts`): unary `max m n` from unary `m`, `n` (restored);
2. `ULog` (new): unary `e = clog₂ (max m n)` (the max copy consumed);
3. the admitted `MatrixUnaryPower` program (`unary_power_run`): unary `2^e`;
4. the admitted `BitMachineCopy` program (`run_correct`): a second copy of `2^e`;
5. the admitted one-stack clear `Unit4Post.ClearOne` (`clear_run`): clears `e`.

Layout `0 m, 1 n, 2 x, 3 tm, 4 tn, 5 next, 6 e, 7 rows, 8 work, 9 pscratch, 10 cols, 11 ctemp`.
At halt: `m`, `n` restored, `rows = cols = unary (SquarePadding.side m n)`, all other stacks empty;
every step charged; clock `sideBound m n ≤ 160 (m+n+1)^2`.

The join of this bank with the writer's `MatrixTableWriter.ready` configuration, the parser of the
encoded instance and the header serializer are NOT done here (see the checkpoint).
Does not close a ledger row.
-/

namespace Paper2.ASquare.Side

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post

abbrev Stack := Fin 12

/-- The ambient bank as a flat case split (as in `Unit4Post.Exponent.bank13`). -/
def bank12 (m n x tm tn nx e rows wk ps cols ct : List Bool) (j : Stack) : List Bool :=
  match j.val with
  | 0 => m | 1 => n | 2 => x | 3 => tm | 4 => tn | 5 => nx | 6 => e | 7 => rows
  | 8 => wk | 9 => ps | 10 => cols | _ => ct

def ιMax : Fin 5 ↪ Stack := ⟨![0, 1, 2, 3, 4], by decide⟩
def ιLog : Fin 3 ↪ Stack := ⟨![2, 5, 6], by decide⟩
def ιPower : MatrixUnaryPower.Stack ↪ Stack :=
  ⟨Sum.elim ![7, 8, 9] (fun _ => 6), by decide⟩
def ιCopy : Fin 3 ↪ Stack := ⟨![7, 10, 11], by decide⟩
def ιE : Fin 1 ↪ Stack := ⟨![6], by decide⟩

def sMax := fun l => BitMachineStackEmbedding.stackStmt ιMax (UMax.program l)
def sLog := fun l => BitMachineStackEmbedding.stackStmt ιLog (ULog.program l)
def sPower := fun l => BitMachineStackEmbedding.stackStmt ιPower (MatrixUnaryPower.program l)
def sCopy := fun l => BitMachineStackEmbedding.stackStmt ιCopy (BitMachineCopy.program l)
def sE := fun l => BitMachineStackEmbedding.stackStmt ιE (ClearOne.program l)

abbrev L4 := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev V4 := BitMachineRawSequence.Control (Option Bool) Bool
def seq4 := BitMachineRawSequence.program sCopy sE () none false
def start4 : L4 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def init4 : V4 := (none, false)

abbrev L3 := BitMachineRawSequence.Label MatrixUnaryPower.Label L4
abbrev V3 := BitMachineRawSequence.Control MatrixUnaryPower.Control V4
def seq3 := BitMachineRawSequence.program sPower seq4 start4 ((false, false), none) init4
def start3 : L3 := BitMachineRawSequence.leftLabel (.inr false)
def init3 : V3 := (((false, false), none), init4)

abbrev L2 := BitMachineRawSequence.Label ULog.Label L3
abbrev V2 := BitMachineRawSequence.Control Bool V3
def seq2 := BitMachineRawSequence.program sLog seq3 start3 false init3
def start2 : L2 := BitMachineRawSequence.leftLabel .check
def init2 : V2 := (false, init3)

abbrev Label := BitMachineRawSequence.Label UMax.Label L2
abbrev Control := BitMachineRawSequence.Control Bool V2
/-- The sequenced program: max, log, power, copy, clear `e`. -/
def program := BitMachineRawSequence.program sMax seq2 start2 false init2
def start : Label := BitMachineRawSequence.leftLabel .scan
def initial : Control := (false, init2)

macro "sq_embed_out" : tactic => `(tactic| (
  intro j hj
  fin_cases j <;> first
    | rfl
    | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
    | exact absurd rfl (hj 3) | exact absurd rfl (hj 4)))

theorem stage1 (m n : ℕ) :
    ∃ t ≤ 3 * (m + n) + 6, ∃ v,
      ((advance sMax)^[t])
        ⟨some .scan, false, bank12 (rp m) (rp n) [] [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, v, bank12 (rp m) (rp n) (rp (max m n)) [] [] [] [] [] [] [] [] []⟩ := by
  obtain ⟨t, ht, v, h⟩ := UMax.max_run m n
  exact ⟨t, ht, v, embed_run ιMax UMax.program .scan false v
    ![rp m, rp n, [], [], []] ![rp m, rp n, rp (max m n), [], []] _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by sq_embed_out)⟩

theorem stage2 (m n x : ℕ) :
    ∃ t ≤ (3 * x + 5) * (Nat.clog 2 x + 1), ∃ v,
      ((advance sLog)^[t])
        ⟨some .check, false, bank12 (rp m) (rp n) (rp x) [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, v, bank12 (rp m) (rp n) [] [] [] [] (rp (Nat.clog 2 x)) [] [] [] [] []⟩ := by
  obtain ⟨t, ht, v, h⟩ := ULog.log_run x 0 false
  rw [Nat.zero_add] at h
  exact ⟨t, ht, v, embed_run ιLog ULog.program .check false v
    ![rp x, [], rp 0] ![[], [], rp (Nat.clog 2 x)] _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by sq_embed_out)⟩

theorem stage3 (m n q : ℕ) :
    ∃ t ≤ 4 * 2 ^ q + 5 * q + 7,
      ((advance sPower)^[t])
        ⟨some (.inr false), ((false, false), none),
          bank12 (rp m) (rp n) [] [] [] [] (rp q) [] [] [] [] []⟩ =
        ⟨none, ((false, false), none),
          bank12 (rp m) (rp n) [] [] [] [] (rp q) (rp (2 ^ q)) [] [] [] []⟩ := by
  obtain ⟨tp, htp, hpr⟩ := MatrixUnaryPower.unary_power_run q
  refine ⟨tp, htp, ?_⟩
  exact embed_run ιPower MatrixUnaryPower.program (.inr false) ((false, false), none)
    ((false, false), none)
    (MatrixUnaryPower.contents [] [] [] (rp q))
    (MatrixUnaryPower.contents (rp (2 ^ q)) [] [] (rp q)) _ _ tp hpr
    (by intro i; cases i with | inl i => fin_cases i <;> rfl | inr u => rfl)
    (by intro i; cases i with | inl i => fin_cases i <;> rfl | inr u => rfl)
    (by
      intro j hj
      fin_cases j <;> first
        | rfl
        | exact absurd rfl (hj (.inl 0)) | exact absurd rfl (hj (.inl 1))
        | exact absurd rfl (hj (.inl 2)) | exact absurd rfl (hj (.inr ())))

theorem stage4 (m n q P : ℕ) :
    ((advance sCopy)^[2 * P + 2])
      ⟨some .scan, none, bank12 (rp m) (rp n) [] [] [] [] (rp q) (rp P) [] [] [] []⟩ =
      ⟨none, none, bank12 (rp m) (rp n) [] [] [] [] (rp q) (rp P) [] [] (rp P) []⟩ := by
  have h := BitMachineCopy.run_correct none (rp P) []
  simp only [rp, List.length_replicate, List.append_nil] at h
  exact embed_run ιCopy BitMachineCopy.program .scan none none
    (BitMachineCopy.stackContents (rp P) [] [])
    (BitMachineCopy.stackContents (rp P) (rp P) []) _ _ (2 * P + 2) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by sq_embed_out)

theorem stage5 (m n q P : ℕ) :
    ((advance sE)^[q + 1])
      ⟨some (), false, bank12 (rp m) (rp n) [] [] [] [] (rp q) (rp P) [] [] (rp P) []⟩ =
      ⟨none, false, bank12 (rp m) (rp n) [] [] [] [] [] (rp P) [] [] (rp P) []⟩ := by
  have h := ClearOne.clear_run (rp q) false
  simp only [rp, List.length_replicate] at h
  exact embed_run ιE ClearOne.program () false false ![rp q] ![[]] _ _ (q + 1) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by sq_embed_out)

/-- The explicit clock of the side program. -/
def sideBound (m n : ℕ) : ℕ :=
  3 * (m + n) + 6 + (3 * max m n + 5) * (Nat.clog 2 (max m n) + 1) +
    (4 * SquarePadding.side m n + 5 * SquarePadding.exponent m n + 7) +
    (2 * SquarePadding.side m n + 2) + (SquarePadding.exponent m n + 1) + 4

/-- **The unary side stage.** From unary `m` (stack 0) and unary `n` (stack 1), every other stack
empty, the ONE fixed program halts with `m` and `n` restored, unary `SquarePadding.side m n` on
the row counter (stack 7) and on the column counter (stack 10), and every other stack empty,
within `sideBound m n` transitions. -/
theorem side_run (m n : ℕ) :
    ∃ t ≤ sideBound m n, ∃ v,
      ((advance program)^[t])
        ⟨some start, initial, bank12 (rp m) (rp n) [] [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, v, bank12 (rp m) (rp n) [] [] [] [] [] (rp (SquarePadding.side m n)) [] []
        (rp (SquarePadding.side m n)) []⟩ := by
  obtain ⟨t1, ht1, v1, h1⟩ := stage1 m n
  obtain ⟨t2, ht2, v2, h2⟩ := stage2 m n (max m n)
  obtain ⟨t3, ht3, h3⟩ := stage3 m n (Nat.clog 2 (max m n))
  have h4 := stage4 m n (Nat.clog 2 (max m n)) (2 ^ Nat.clog 2 (max m n))
  have h5 := stage5 m n (Nat.clog 2 (max m n)) (2 ^ Nat.clog 2 (max m n))
  obtain ⟨a4, ha4, e4⟩ := BitMachineRawSequence.runs sCopy sE .scan () none none false false
    _ _ _ _ _ h4 h5
  obtain ⟨a3, ha3, e3⟩ := BitMachineRawSequence.runs sPower seq4 (.inr false) start4
    ((false, false), none) ((false, false), none) init4 (none, false) _ _ _ _ _ h3 e4
  obtain ⟨a2, ha2, e2⟩ := BitMachineRawSequence.runs sLog seq3 .check start3
    false v2 init3 (((false, false), none), (none, false)) _ _ _ _ _ h2 e3
  obtain ⟨a1, ha1, e1⟩ := BitMachineRawSequence.runs sMax seq2 .scan start2
    false v1 init2 (false, (((false, false), none), (none, false))) _ _ _ _ _ h1 e2
  refine ⟨a1, ?_, _, e1⟩
  unfold sideBound SquarePadding.side SquarePadding.exponent
  omega

theorem side_le (m n : ℕ) : SquarePadding.side m n ≤ 2 * (m + n) + 1 := by
  by_cases h : max m n = 0
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm hn
    decide
  · have := SquarePadding.side_lt_twice_max (m := m) (n := n) (by omega)
    have hmax : max m n ≤ m + n := max_le (by omega) (by omega)
    omega

/-- **Polynomial clock of the side stage.** -/
theorem sideBound_le (m n : ℕ) : sideBound m n ≤ 160 * (m + n + 1) ^ 2 := by
  have hs := side_le m n
  have he : SquarePadding.exponent m n < SquarePadding.side m n := Nat.lt_two_pow_self
  have hc : Nat.clog 2 (max m n) = SquarePadding.exponent m n := rfl
  have hmax : max m n ≤ m + n := max_le (by omega) (by omega)
  unfold sideBound
  rw [hc]
  set w := m + n with hw
  set E := SquarePadding.exponent m n
  set S := SquarePadding.side m n
  have hE : E ≤ 2 * w + 1 := by omega
  have hprod : (3 * max m n + 5) * (E + 1) ≤ (3 * w + 5) * (2 * w + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

#print axioms UMax.max_run
#print axioms ULog.log_run
#print axioms side_run
#print axioms sideBound_le

end Paper2.ASquare.Side
