import Paper2.CodeExtract
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Physical navigation inside serialized `GeneratorCode` syntax.

Bank: the admitted `CodeExtract` bank (source, scanned, scanner work,
pending, scratch) beside `inp` (retained node word) and `outp`.
Building blocks (each one fixed program with an exact theorem):
* `dropAppend`: remove the three header bits of an `.append` node;
* `dropBranch`: remove the header of a `.branch3` node (three bits and three
  terminated unary fields);
* `dropChild`: remove the first serialized code from the source word;
* `takeChild`: move the first serialized code to `outp` and clear the rest.
All use the admitted `CodeExtract.fullProgram` for code boundaries. -/

namespace Paper2.ChildNav

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev CE := CodeExtract.Stack
abbrev Stack := CE ⊕ Fin 2

/-- The bank at phase boundaries. -/
def nb (src scanned pend inp outp : List Bool) : Stack → List Bool :=
  Sum.elim (CodeExtract.contents src scanned [] pend)
    (fun i => if i = 0 then inp else outp)

def srcC : Stack := .inl (.inr 0)
def scannedC : Stack := .inl (.inl (.inl 0))
def scratchC : Stack := .inl (.inr 1)
def pendC : Stack := .inl (.inl (.inr 0))
def inpC : Stack := .inr 0
def outpC : Stack := .inr 1

section BankLemmas
variable (src scanned pend inp outp x : List Bool)

@[simp] theorem nb_src : nb src scanned pend inp outp srcC = src := rfl
@[simp] theorem nb_scanned : nb src scanned pend inp outp scannedC = scanned := rfl
@[simp] theorem nb_scratch : nb src scanned pend inp outp scratchC = [] := rfl
@[simp] theorem nb_pend : nb src scanned pend inp outp pendC = pend := rfl
@[simp] theorem nb_inp : nb src scanned pend inp outp inpC = inp := rfl
@[simp] theorem nb_outp : nb src scanned pend inp outp outpC = outp := rfl

theorem up_src : Function.update (nb src scanned pend inp outp) srcC x =
    nb x scanned pend inp outp := by
  funext j; rcases j with ((j | j) | j) | j
  · fin_cases j <;> rfl
  · fin_cases j; rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
theorem up_scanned : Function.update (nb src scanned pend inp outp) scannedC x =
    nb src x pend inp outp := by
  funext j; rcases j with ((j | j) | j) | j
  · fin_cases j <;> rfl
  · fin_cases j; rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
theorem up_pend : Function.update (nb src scanned pend inp outp) pendC x =
    nb src scanned x inp outp := by
  funext j; rcases j with ((j | j) | j) | j
  · fin_cases j <;> rfl
  · fin_cases j; rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
theorem up_outp : Function.update (nb src scanned pend inp outp) outpC x =
    nb src scanned pend inp x := by
  funext j; rcases j with ((j | j) | j) | j
  · fin_cases j <;> rfl
  · fin_cases j; rfl
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl

end BankLemmas

/-! ### Primitive single-cell programs -/

/-- Pop exactly `k` bits (fixed `k`) from the source cell. -/
def dropK (k : Nat) : Fin (k + 1) → TM2.Stmt (fun _ : Stack => Bool) (Fin (k + 1)) Unit :=
  fun i => if h : i.val < k then pop srcC (fun _ _ => ()) (goto (fun _ => ⟨i.val + 1, by omega⟩))
    else halt

theorem dropK_run (k : Nat) : ∀ (m : Nat) (hm : m ≤ k) (pre : List Bool),
    pre.length = k - m → ∀ (w scanned pend inp outp : List Bool),
    ((advance (dropK k))^[(k - m) + 1]) (⟨some ⟨m, by omega⟩, (),
      nb (pre ++ w) scanned pend inp outp⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (), nb w scanned pend inp outp⟩ := by
  intro m hm
  induction h : k - m generalizing m with
  | zero =>
    intro pre hpre w scanned pend inp outp
    have hmk : m = k := by omega
    subst hmk
    have hp : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, dropK]
  | succ d ih =>
    intro pre hpre w scanned pend inp outp
    obtain ⟨b, pre', rfl⟩ : ∃ b pre', pre = b :: pre' := by
      cases pre with
      | nil => simp at hpre
      | cons b pre' => exact ⟨b, pre', rfl⟩
    have hlt : m < k := by omega
    rw [Function.iterate_succ_apply]
    have e : advance (dropK k) (⟨some ⟨m, by omega⟩, (),
        nb (b :: pre' ++ w) scanned pend inp outp⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨some ⟨m + 1, by omega⟩, (), nb (pre' ++ w) scanned pend inp outp⟩ := by
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, dropK, hlt, up_src]
    rw [e]
    exact ih (m + 1) (by omega) (by omega) pre' (by simp at hpre; omega) w scanned pend inp
      outp

/-- Pop a terminated unary field `true^n false` from the source cell. -/
def dropUnary : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  fun _ => pop srcC (fun _ b => b)
    (branch (fun v => decide (v = some true)) (goto (fun _ => ())) halt)

theorem dropUnary_run : ∀ (n : Nat) (w scanned pend inp outp : List Bool) (v : Option Bool),
    ((advance dropUnary)^[n + 1]) (⟨some (), v,
      nb (unary n ++ w) scanned pend inp outp⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, some false, nb w scanned pend inp outp⟩
  | 0, w, scanned, pend, inp, outp, v => by
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, dropUnary, unary, up_src]
  | n + 1, w, scanned, pend, inp, outp, v => by
      rw [Function.iterate_succ_apply]
      have e : advance dropUnary (⟨some (), v, nb (unary (n + 1) ++ w) scanned pend inp outp⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨some (), some true, nb (unary n ++ w) scanned pend inp outp⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, dropUnary, unary,
          List.replicate_succ, up_src]
      rw [e]
      exact dropUnary_run n w scanned pend inp outp (some true)

/-- Clear one cell. -/
def clearCell (k : Stack) : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  fun _ => pop k (fun _ b => b) (branch Option.isSome (goto (fun _ => ())) halt)

theorem clearCell_run (k : Stack) : ∀ (xs : List Bool) (S : Stack → List Bool)
    (v : Option Bool), S k = xs →
    ((advance (clearCell k))^[xs.length + 1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S k []⟩
  | [], S, v, hS => by
      have hS' : Function.update S k [] = S := by rw [← hS]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clearCell, hS, hS']
  | b :: xs, S, v, hS => by
      rw [show (b :: xs).length + 1 = (xs.length + 1) + 1 by simp, Function.iterate_add_apply]
      have e : ((advance (clearCell k))^[1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
          ⟨some (), some b, Function.update S k xs⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clearCell, hS]
      rw [e, clearCell_run k xs (Function.update S k xs) (some b) (by simp)]
      simp

/-- Push one pending marker. -/
def pushPend : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit :=
  fun _ => push pendC (fun _ => true) halt

theorem pushPend_run (src scanned inp outp : List Bool) :
    advance pushPend (⟨some (), (), nb src scanned [] inp outp⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), nb src scanned [true] inp outp⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, pushPend, up_pend]

/-! ### Extraction, embedded -/

def ceSlots : CE ↪ Stack := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

def extractP := fun l => stackStmt ceSlots (CodeExtract.fullProgram l)

theorem contents_eq_fbank (a b : List Bool) :
    CodeExtract.contents a b [] [] = CodeExtract.fbank a b [] [] := by
  funext k; rcases k with (k | k) | k
  · fin_cases k <;> rfl
  · fin_cases k; rfl
  · fin_cases k <;> rfl

theorem extract_run (c : Code) (rest inp outp : List Bool) :
    ∃ t ≤ 12 * (encodeCode c ++ rest).length + 12,
      ((advance extractP)^[t])
        (⟨(CodeExtract.fullInitial (encodeCode c ++ rest)).l,
          (CodeExtract.fullInitial (encodeCode c ++ rest)).var,
          nb (encodeCode c ++ rest) [] [true] inp outp⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (CodeExtract.fullOutput (encodeCode c) rest).var,
          nb (encodeCode c) rest [] inp outp⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeExtract.extract_one_code c rest
  refine ⟨t, ht, ?_⟩
  have hs := BitMachineStackRun.run ceSlots (nb (encodeCode c ++ rest) [] [true] inp outp)
    CodeExtract.fullProgram (CodeExtract.fullInitial (encodeCode c ++ rest)) t
  rw [hr] at hs
  have hb1 : bank ceSlots (nb (encodeCode c ++ rest) [] [true] inp outp)
      (CodeExtract.fullInitial (encodeCode c ++ rest)).stk =
      nb (encodeCode c ++ rest) [] [true] inp outp := by
    apply bank_eq_self
    intro k
    rcases k with (k | k) | k
    · fin_cases k <;> rfl
    · fin_cases k; rfl
    · fin_cases k <;> rfl
  have hb2 : bank ceSlots (nb (encodeCode c ++ rest) [] [true] inp outp)
      (CodeExtract.fullOutput (encodeCode c) rest).stk =
      nb (encodeCode c) rest [] inp outp := by
    funext j
    rcases j with j | j
    · rw [show (Sum.inl j : Stack) = ceSlots j from rfl, bank_at]
      rcases j with (k | k) | k
      · fin_cases k <;> rfl
      · fin_cases k; rfl
      · fin_cases k <;> rfl
    · exact bank_outside ceSlots _ _ (.inr j) (by rintro ⟨k, hk⟩; cases hk)
  simp only [stackCfg] at hs
  rw [hb1, hb2] at hs
  exact hs

#print axioms dropK_run
#print axioms dropUnary_run
#print axioms clearCell_run
#print axioms extract_run

end Paper2.ChildNav
