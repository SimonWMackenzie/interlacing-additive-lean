import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.FinalPadding

/-!
# Unit 4 (Paper B), segment B4-S3: the padding exponent `p = n / (2 max 1 k)` and `2^p`

Lane owner:b-unit4-shell-3 (private, 26 September 2026). Source: lock v8 `06-eth.tex`
(`FinalPadding.exponent L n = n / (2 * max 1 (L n))`, `tableSize = 2^(2p)`).

ONE fixed Boolean-stack program on 13 stacks. From unary `n` (stack 0) and unary `k` (stack 1)
it computes, all in charged transitions:

1. `D = 2 * max 1 k` in unary (a new three-stack doubling program, `k` restored);
2. `n / D` and `n % D` with the admitted `MatrixUnaryDivision` program (`division_total_run`);
3. clears `n % D` and `D` (a new one-stack clear program);
4. unary `2^p` with the admitted `MatrixUnaryPower` program (`unary_power_run`);
5. a second copy of `2^p` with the admitted `BitMachineCopy` program (`run_correct`);
6. clears `p`.

At halt: stack 1 = unary `k` (unchanged), stacks 8 and 11 = unary `2^p` (the writer's row and
column counters), every other stack empty (in particular `n` is consumed). Sub-programs are
inlined by the admitted stack embedding (`BitMachineStackRun.run`) and sequenced by the admitted
`BitMachineRawSequence.runs`; no value is computed in finite control and no input is inserted.

Here `k` is H-B2's field 1 (the repetition count `L n` on actual inputs); `max 1 k` is
exactly the source's convention for all `k`, including `k = 0`.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post

open Turing Turing.TM2.Stmt BitMachineEncoding

/-! ## A generic exact-run transport through a stack embedding -/

theorem embed_run {K J L V : Type*} [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (l₀ : L) (v₀ v₁ : V) (S₀ S₁ : K → List Bool) (T₀ T₁ : J → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) ⟨some l₀, v₀, S₀⟩ = ⟨none, v₁, S₁⟩)
    (h₀ : ∀ k, S₀ k = T₀ (ι k)) (h₁ : ∀ k, S₁ k = T₁ (ι k))
    (hout : ∀ j, (∀ k, ι k ≠ j) → T₀ j = T₁ j) :
    ((advance (fun l => BitMachineStackEmbedding.stackStmt ι (P l)))^[t])
      ⟨some l₀, v₀, T₀⟩ = ⟨none, v₁, T₁⟩ := by
  have hr := BitMachineStackRun.run ι T₀ P ⟨some l₀, v₀, S₀⟩ t
  rw [h] at hr
  have hb₀ : BitMachineStackEmbedding.bank ι T₀ S₀ = T₀ :=
    BitMachineStackEmbedding.bank_eq_self ι T₀ S₀ h₀
  have hb₁ : BitMachineStackEmbedding.bank ι T₀ S₁ = T₁ := by
    funext j
    by_cases hj : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [BitMachineStackEmbedding.bank_at]
      exact h₁ k
    · rw [BitMachineStackEmbedding.bank_outside ι T₀ S₁ j hj]
      exact hout j (fun k hk => hj ⟨k, hk⟩)
  simp only [BitMachineStackEmbedding.stackCfg, hb₀, hb₁] at hr
  exact hr

/-- A halted run can be padded to any later exact time. -/
theorem halted_pad {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (v : V) (S : K → List Bool) (t u : ℕ) (htu : t ≤ u)
    (h : ((advance P)^[t]) c = ⟨none, v, S⟩) :
    ((advance P)^[u]) c = ⟨none, v, S⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  exact BitMachineSubroutine.run_halted P _ rfl d

/-! ## The doubling program `D := 2 * max 1 k` (three stacks: `0 k`, `1 D`, `2 temp`) -/

namespace Double

inductive Label where
  | scan | restore | floor
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .scan => pop 0 (fun _ b => b.isSome)
      (branch id
        (push 1 (fun _ => true) (push 1 (fun _ => true) (push 2 (fun _ => true)
          (goto (fun _ => .scan)))))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .restore)))
        (goto (fun _ => .floor)))
  | .floor => pop 1 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) halt)
        (push 1 (fun _ => true) (push 1 (fun _ => true) halt)))

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (a d t : List Bool) : Config := ⟨l, s, ![a, d, t]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem scan_cons (s : Bool) (a d t : List Bool) :
    advance program (cfg (some .scan) s (true :: a) d t) =
      cfg (some .scan) true a (true :: true :: d) (true :: t) := by
  apply congrArg (fun S => (⟨some .scan, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem scan_nil (s : Bool) (d t : List Bool) :
    advance program (cfg (some .scan) s [] d t) = cfg (some .restore) false [] d t := by
  apply congrArg (fun S => (⟨some .restore, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem restore_cons (s : Bool) (a d t : List Bool) :
    advance program (cfg (some .restore) s a d (true :: t)) =
      cfg (some .restore) true (true :: a) d t := by
  apply congrArg (fun S => (⟨some .restore, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem restore_nil (s : Bool) (a d : List Bool) :
    advance program (cfg (some .restore) s a d []) = cfg (some .floor) false a d [] := by
  apply congrArg (fun S => (⟨some .floor, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem floor_cons (s : Bool) (a d t : List Bool) :
    advance program (cfg (some .floor) s a (true :: d) t) = cfg none true a (true :: d) t := by
  apply congrArg (fun S => (⟨none, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem floor_nil (s : Bool) (a t : List Bool) :
    advance program (cfg (some .floor) s a [] t) = cfg none false a [true, true] t := by
  apply congrArg (fun S => (⟨none, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem scan_run (j i : ℕ) (s : Bool) :
    run (j + 1) (cfg (some .scan) s (List.replicate j true) (List.replicate (2 * i) true)
      (List.replicate i true)) =
      cfg (some .restore) false [] (List.replicate (2 * (i + j)) true)
        (List.replicate (i + j) true) := by
  induction j generalizing i s with
  | zero => simpa [run] using scan_nil s (List.replicate (2 * i) true) (List.replicate i true)
  | succ j ih =>
      have hd : true :: true :: List.replicate (2 * i) true = List.replicate (2 * (i + 1)) true := by
        rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
        simp [List.replicate_succ]
      have ht : true :: List.replicate i true = List.replicate (i + 1) true := by
        simp [List.replicate_succ]
      rw [run, Function.iterate_succ_apply, List.replicate_succ, scan_cons, hd, ht]
      have h := ih (i + 1) true
      rw [show i + 1 + j = i + (j + 1) by ring] at h
      exact h

theorem restore_run (j i : ℕ) (s : Bool) (d : List Bool) :
    run (j + 1) (cfg (some .restore) s (List.replicate i true) d (List.replicate j true)) =
      cfg (some .floor) false (List.replicate (i + j) true) d [] := by
  induction j generalizing i s with
  | zero => simpa [run] using restore_nil s (List.replicate i true) d
  | succ j ih =>
      have ha : true :: List.replicate i true = List.replicate (i + 1) true := by
        simp [List.replicate_succ]
      rw [run, Function.iterate_succ_apply, List.replicate_succ, restore_cons, ha]
      have h := ih (i + 1) true
      rw [show i + 1 + j = i + (j + 1) by ring] at h
      exact h

theorem floor_run (k : ℕ) (s : Bool) :
    run 1 (cfg (some .floor) s (List.replicate k true) (List.replicate (2 * k) true) []) =
      cfg none (decide (0 < k)) (List.replicate k true)
        (List.replicate (2 * max 1 k) true) [] := by
  cases k with
  | zero => simpa [run] using floor_nil s [] []
  | succ k =>
      have h := floor_cons s (List.replicate (k + 1) true) (List.replicate (2 * k + 1) true) []
      have hm : max 1 (k + 1) = k + 1 := by omega
      have hd : List.replicate (2 * (k + 1)) true = true :: List.replicate (2 * k + 1) true := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
        rfl
      have hz : decide (0 < k + 1) = true := by simp
      rw [hm, hd, hz]
      exact h

/-- `D = 2 * max 1 k`, with `k` restored and the temporary stack empty, in `2k+3` steps. -/
theorem double_run (k : ℕ) :
    run (2 * k + 3) (cfg (some .scan) false (List.replicate k true) [] []) =
      cfg none (decide (0 < k)) (List.replicate k true)
        (List.replicate (2 * max 1 k) true) [] := by
  have h1 := scan_run k 0 false
  simp only [Nat.mul_zero, List.replicate_zero, Nat.zero_add] at h1
  have h2 := restore_run k 0 false (List.replicate (2 * k) true)
  simp only [List.replicate_zero, Nat.zero_add] at h2
  have h3 := floor_run k false
  rw [show 2 * k + 3 = 1 + ((k + 1) + (k + 1)) by ring, run, Function.iterate_add_apply,
    Function.iterate_add_apply]
  change run 1 (run (k + 1) (run (k + 1) _)) = _
  rw [h1, h2, h3]

end Double

/-! ## A one-stack clear program -/

namespace ClearOne

def program : Unit → TM2.Stmt (fun _ : Fin 1 => Bool) Unit Bool
  | () => pop 0 (fun _ b => b.isSome) (branch id (goto (fun _ => ())) halt)

theorem clear_run (w : List Bool) (s : Bool) :
    ((advance program)^[w.length + 1])
      (⟨some (), s, ![w]⟩ : TM2.Cfg (fun _ : Fin 1 => Bool) Unit Bool) =
      ⟨none, false, ![[]]⟩ := by
  induction w generalizing s with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
      apply congrArg (fun S => (⟨none, false, S⟩ : TM2.Cfg (fun _ : Fin 1 => Bool) Unit Bool))
      funext k
      fin_cases k
      rfl
  | cons b w ih =>
      have hs : advance program
          (⟨some (), s, ![b :: w]⟩ : TM2.Cfg (fun _ : Fin 1 => Bool) Unit Bool) =
          ⟨some (), true, ![w]⟩ := by
        apply congrArg (fun S => (⟨some (), true, S⟩ : TM2.Cfg (fun _ : Fin 1 => Bool) Unit Bool))
        funext k
        fin_cases k
        rfl
      rw [List.length_cons, Function.iterate_succ_apply, hs]
      exact ih true

end ClearOne

/-! ## The exponent program on 13 stacks

Layout: `0 n, 1 k, 2 D, 3 dtemp, 4 count, 5 rem, 6 p, 7 saved, 8 rows, 9 work, 10 pscratch,
11 cols, 12 ctemp`. -/

namespace Exponent

abbrev Stack := Fin 13

/-- The ambient bank, as a flat case split on the stack index (no nested vector tails, so
that definitional unfolding of two banks at one index is linear). -/
def bank13 (n k D dt cnt rem p sv rows wk ps cols ct : List Bool) (j : Stack) : List Bool :=
  match j.val with
  | 0 => n | 1 => k | 2 => D | 3 => dt | 4 => cnt | 5 => rem | 6 => p | 7 => sv
  | 8 => rows | 9 => wk | 10 => ps | 11 => cols | _ => ct

def ιDouble : Fin 3 ↪ Stack := ⟨![1, 2, 3], by decide⟩
def ιDivision : Fin 6 ↪ Stack := ⟨![0, 2, 4, 5, 6, 7], by decide⟩
def ιRem : Fin 1 ↪ Stack := ⟨![5], by decide⟩
def ιD : Fin 1 ↪ Stack := ⟨![2], by decide⟩
def ιPower : MatrixUnaryPower.Stack ↪ Stack :=
  ⟨Sum.elim ![8, 9, 10] (fun _ => 6), by decide⟩
def ιCopy : Fin 3 ↪ Stack := ⟨![8, 11, 12], by decide⟩
def ιP : Fin 1 ↪ Stack := ⟨![6], by decide⟩

def sDouble := fun l => BitMachineStackEmbedding.stackStmt ιDouble (Double.program l)
def sDivision := fun l =>
  BitMachineStackEmbedding.stackStmt ιDivision (MatrixUnaryDivision.program l)
def sRem := fun l => BitMachineStackEmbedding.stackStmt ιRem (ClearOne.program l)
def sD := fun l => BitMachineStackEmbedding.stackStmt ιD (ClearOne.program l)
def sPower := fun l => BitMachineStackEmbedding.stackStmt ιPower (MatrixUnaryPower.program l)
def sCopy := fun l => BitMachineStackEmbedding.stackStmt ιCopy (BitMachineCopy.program l)
def sP := fun l => BitMachineStackEmbedding.stackStmt ιP (ClearOne.program l)

/-! Sequencing (innermost first). -/

abbrev L6 := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev V6 := BitMachineRawSequence.Control (Option Bool) Bool
def seq6 := BitMachineRawSequence.program sCopy sP () none false
def start6 : L6 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def init6 : V6 := (none, false)

abbrev L5 := BitMachineRawSequence.Label MatrixUnaryPower.Label L6
abbrev V5 := BitMachineRawSequence.Control MatrixUnaryPower.Control V6
def seq5 := BitMachineRawSequence.program sPower seq6 start6 ((false, false), none) init6
def start5 : L5 := BitMachineRawSequence.leftLabel (.inr false)
def init5 : V5 := (((false, false), none), init6)

abbrev L4 := BitMachineRawSequence.Label Unit L5
abbrev V4 := BitMachineRawSequence.Control Bool V5
def seq4 := BitMachineRawSequence.program sD seq5 start5 false init5
def start4 : L4 := BitMachineRawSequence.leftLabel ()
def init4 : V4 := (false, init5)

abbrev L3 := BitMachineRawSequence.Label Unit L4
abbrev V3 := BitMachineRawSequence.Control Bool V4
def seq3 := BitMachineRawSequence.program sRem seq4 start4 false init4
def start3 : L3 := BitMachineRawSequence.leftLabel ()
def init3 : V3 := (false, init4)

abbrev L2 := BitMachineRawSequence.Label MatrixUnaryDivision.Label L3
abbrev V2 := BitMachineRawSequence.Control Bool V3
def seq2 := BitMachineRawSequence.program sDivision seq3 start3 false init3
def start2 : L2 := BitMachineRawSequence.leftLabel .start
def init2 : V2 := (false, init3)

abbrev Label := BitMachineRawSequence.Label Double.Label L2
abbrev Control := BitMachineRawSequence.Control Bool V2
/-- The sequenced program: double, divide, clear rem, clear D, power, copy, clear p. -/
def program := BitMachineRawSequence.program sDouble seq2 start2 false init2
def start : Label := BitMachineRawSequence.leftLabel .scan
def initial : Control := (false, init2)

/-- The exponent `p` in the source's convention. -/
def pexp (n k : ℕ) : ℕ := n / (2 * max 1 k)

def bound (n k : ℕ) : ℕ := 15 * (n + k + 2 ^ pexp n k + 3)

macro "embed_out" : tactic => `(tactic| (
  intro j hj
  fin_cases j <;> first
    | rfl
    | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
    | exact absurd rfl (hj 3) | exact absurd rfl (hj 4) | exact absurd rfl (hj 5)))

abbrev rp (n : ℕ) : List Bool := List.replicate n true

theorem stage1 (n k : ℕ) :
    ((advance sDouble)^[2 * k + 3])
      ⟨some .scan, false, bank13 (rp n) (rp k) [] [] [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, decide (0 < k),
        bank13 (rp n) (rp k) (rp (2 * max 1 k)) [] [] [] [] [] [] [] [] [] []⟩ :=
  embed_run ιDouble Double.program .scan false (decide (0 < k))
    ![rp k, [], []] ![rp k, rp (2 * max 1 k), []] _ _
    (2 * k + 3) (Double.double_run k) (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by embed_out)

theorem stage2 (n k dv : ℕ) :
    ((advance sDivision)^[MatrixUnaryDivision.totalTime n dv])
      ⟨some .start, false, bank13 (rp n) (rp k) (rp dv) [] [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, false,
        bank13 [] (rp k) (rp dv) [] [] (rp (n % dv)) (rp (n / dv)) [] [] [] [] [] []⟩ :=
  embed_run ιDivision MatrixUnaryDivision.program .start false false
    ![rp n, rp dv, [], [], [], []] ![[], rp dv, [], rp (n % dv), rp (n / dv), []] _ _
    (MatrixUnaryDivision.totalTime n dv) (MatrixUnaryDivision.division_total_run n dv)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by embed_out)

theorem stage3 (k dv r q : ℕ) :
    ((advance sRem)^[r + 1])
      ⟨some (), false, bank13 [] (rp k) (rp dv) [] [] (rp r) (rp q) [] [] [] [] [] []⟩ =
      ⟨none, false, bank13 [] (rp k) (rp dv) [] [] [] (rp q) [] [] [] [] [] []⟩ := by
  have h := ClearOne.clear_run (rp r) false
  simp only [rp, List.length_replicate] at h
  exact embed_run ιRem ClearOne.program () false false ![rp r] ![[]] _ _ (r + 1) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by embed_out)

theorem stage4 (k dv q : ℕ) :
    ((advance sD)^[dv + 1])
      ⟨some (), false, bank13 [] (rp k) (rp dv) [] [] [] (rp q) [] [] [] [] [] []⟩ =
      ⟨none, false, bank13 [] (rp k) [] [] [] [] (rp q) [] [] [] [] [] []⟩ := by
  have h := ClearOne.clear_run (rp dv) false
  simp only [rp, List.length_replicate] at h
  exact embed_run ιD ClearOne.program () false false ![rp dv] ![[]] _ _ (dv + 1) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by embed_out)

theorem stage5 (k q : ℕ) :
    ∃ t ≤ 4 * 2 ^ q + 5 * q + 7,
      ((advance sPower)^[t])
        ⟨some (.inr false), ((false, false), none),
          bank13 [] (rp k) [] [] [] [] (rp q) [] [] [] [] [] []⟩ =
        ⟨none, ((false, false), none),
          bank13 [] (rp k) [] [] [] [] (rp q) [] (rp (2 ^ q)) [] [] [] []⟩ := by
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

theorem stage6 (k q P : ℕ) :
    ((advance sCopy)^[2 * P + 2])
      ⟨some .scan, none, bank13 [] (rp k) [] [] [] [] (rp q) [] (rp P) [] [] [] []⟩ =
      ⟨none, none, bank13 [] (rp k) [] [] [] [] (rp q) [] (rp P) [] [] (rp P) []⟩ := by
  have h := BitMachineCopy.run_correct none (rp P) []
  simp only [rp, List.length_replicate, List.append_nil] at h
  exact embed_run ιCopy BitMachineCopy.program .scan none none
    (BitMachineCopy.stackContents (rp P) [] [])
    (BitMachineCopy.stackContents (rp P) (rp P) []) _ _ (2 * P + 2) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by embed_out)

theorem stage7 (k q P : ℕ) :
    ((advance sP)^[q + 1])
      ⟨some (), false, bank13 [] (rp k) [] [] [] [] (rp q) [] (rp P) [] [] (rp P) []⟩ =
      ⟨none, false, bank13 [] (rp k) [] [] [] [] [] [] (rp P) [] [] (rp P) []⟩ := by
  have h := ClearOne.clear_run (rp q) false
  simp only [rp, List.length_replicate] at h
  exact embed_run ιP ClearOne.program () false false ![rp q] ![[]] _ _ (q + 1) h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by embed_out)

/-- **B4-S3.** The ONE fixed exponent program, from unary `n` and unary `k`, halts with unary
`k` restored, unary `2^p` on the row and column counter stacks (`p = n / (2 max 1 k)`), and every
other stack empty, within `15 (n + k + 2^p + 3)` transitions. -/
theorem exponent_run (n k : ℕ) :
    ∃ t ≤ bound n k, ∃ v,
      ((advance program)^[t])
        ⟨some start, initial, bank13 (rp n) (rp k) [] [] [] [] [] [] [] [] [] [] []⟩ =
      ⟨none, v, bank13 [] (rp k) [] [] [] [] [] [] (rp (2 ^ pexp n k)) [] []
          (rp (2 ^ pexp n k)) []⟩ := by
  have h1 := stage1 n k
  have h2 := stage2 n k (2 * max 1 k)
  have h3 := stage3 k (2 * max 1 k) (n % (2 * max 1 k)) (n / (2 * max 1 k))
  have h4 := stage4 k (2 * max 1 k) (n / (2 * max 1 k))
  obtain ⟨tp, htp, h5⟩ := stage5 k (n / (2 * max 1 k))
  have h6 := stage6 k (n / (2 * max 1 k)) (2 ^ (n / (2 * max 1 k)))
  have h7 := stage7 k (n / (2 * max 1 k)) (2 ^ (n / (2 * max 1 k)))
  obtain ⟨a6, ha6, e6⟩ := BitMachineRawSequence.runs sCopy sP .scan () none none false false
    _ _ _ _ _ h6 h7
  obtain ⟨a5, ha5, e5⟩ := BitMachineRawSequence.runs sPower seq6 (.inr false) start6
    ((false, false), none) ((false, false), none) init6 (none, false) _ _ _ _ _ h5 e6
  obtain ⟨a4, ha4, e4⟩ := BitMachineRawSequence.runs sD seq5 () start5
    false false init5 (((false, false), none), (none, false)) _ _ _ _ _ h4 e5
  obtain ⟨a3, ha3, e3⟩ := BitMachineRawSequence.runs sRem seq4 () start4
    false false init4 (false, (((false, false), none), (none, false))) _ _ _ _ _ h3 e4
  obtain ⟨a2, ha2, e2⟩ := BitMachineRawSequence.runs sDivision seq3 .start start3
    false false init3 (false, (false, (((false, false), none), (none, false)))) _ _ _ _ _ h2 e3
  obtain ⟨a1, ha1, e1⟩ := BitMachineRawSequence.runs sDouble seq2 .scan start2
    false (decide (0 < k)) init2
    (false, (false, (false, (((false, false), none), (none, false))))) _ _ _ _ _ h1 e2
  refine ⟨a1, ?_, _, e1⟩
  have hdiv := MatrixUnaryDivision.totalTime_bound n (2 * max 1 k)
  have hmod : n % (2 * max 1 k) ≤ n := Nat.mod_le n _
  have hqn : n / (2 * max 1 k) ≤ n := Nat.div_le_self n _
  have hdvk : 2 * max 1 k ≤ 2 * k + 2 := by
    have : max 1 k ≤ k + 1 := max_le (by omega) (by omega)
    omega
  unfold bound pexp
  clear e1 e2 e3 e4 e5 e6 h1 h2 h3 h4 h5 h6 h7
  generalize 2 ^ (n / (2 * max 1 k)) = P at *
  generalize n / (2 * max 1 k) = q at *
  generalize n % (2 * max 1 k) = r at *
  generalize 2 * max 1 k = dv at *
  omega

end Exponent

end EthInapproximability.CurrentPaper.Unit4Post
