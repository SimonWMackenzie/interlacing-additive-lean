import CurrentAdditive.V22UnaryExpression
import EthInapproximability.CurrentPaper.MatrixUnaryDivision

/-! Literal separated-unary pair parsing, followed by the existing counted
divider. This is arithmetic support for the deterministic GeneratedTests;
the original formula size is not a predicate input. -/
namespace D22UnaryDivision
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

inductive PL where | first | second deriving DecidableEq, Fintype
def parse : PL → TM2.Stmt (fun _ : Fin 7 => Bool) PL Bool
  | .first => .pop 6 (fun _ b => b.getD false)
      (.branch id (.push 0 (fun _ => true) (.goto fun _ => .first))
        (.goto fun _ => .second))
  | .second => .pop 6 (fun _ b => b.isSome)
      (.branch id (.push 1 (fun _ => true) (.goto fun _ => .second)) .halt)
def cfg (l : Option PL) (v : Bool) (input a b : List Bool) :
    TM2.Cfg (fun _ : Fin 7 => Bool) PL Bool :=
  ⟨l,v,![a,b,[],[],[],[],input]⟩
def parsed (a b : ℕ) : Fin 7 → List Bool :=
  ![List.replicate a true,List.replicate b true,[],[],[],[],[]]

theorem first_run (a : ℕ) (rest : List Bool) (c b : ℕ) (v : Bool) :
    ((advance parse)^[a+1])
      (cfg (some .first) v (List.replicate a true++false::rest)
        (List.replicate c true) (List.replicate b true)) =
      cfg (some .second) false rest (List.replicate (a+c) true) (List.replicate b true) := by
  induction a generalizing c v with
  | zero =>
    simp [advance,parse,cfg,TM2.step,TM2.stepAux]
    funext j; fin_cases j <;> rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    have he : advance parse
        (cfg (some .first) v (List.replicate (a+1) true++false::rest)
          (List.replicate c true) (List.replicate b true)) =
        cfg (some .first) true (List.replicate a true++false::rest)
          (List.replicate (c+1) true) (List.replicate b true) := by
      simp [advance,parse,cfg,TM2.step,TM2.stepAux,List.replicate_succ]
      funext j; fin_cases j <;> rfl
    rw [he,ih]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem second_run (b c a : ℕ) (v : Bool) :
    ((advance parse)^[b+1])
      (cfg (some .second) v (List.replicate b true)
        (List.replicate a true) (List.replicate c true)) =
      cfg none false [] (List.replicate a true) (List.replicate (b+c) true) := by
  induction b generalizing c v with
  | zero =>
    simp [advance,parse,cfg,TM2.step,TM2.stepAux]
  | succ b ih =>
    rw [Function.iterate_succ_apply]
    have he : advance parse
        (cfg (some .second) v (List.replicate (b+1) true)
          (List.replicate a true) (List.replicate c true)) =
        cfg (some .second) true (List.replicate b true)
          (List.replicate a true) (List.replicate (c+1) true) := by
      simp [advance,parse,cfg,TM2.step,TM2.stepAux,List.replicate_succ]
      funext j; fin_cases j <;> rfl
    rw [he,ih]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem parse_run (a b : ℕ) :
    ((advance parse)^[a+b+2])
      (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []) =
      ⟨none,false,parsed a b⟩ := by
  have ha := first_run a (List.replicate b true) 0 0 false
  have hb := second_run b 0 a false
  have ht : a+b+2=(b+1)+(a+1) := by omega
  rw [ht,Function.iterate_add_apply]
  simpa only [MatrixUnaryArithmetic.encodeInput,List.replicate_zero,Nat.add_zero,cfg,parsed]
    using (congrArg ((advance parse)^[b+1]) ha).trans hb

def divSlots : Fin 6 ↪ Fin 7 :=
  ⟨fun j => ⟨j.val,by omega⟩,by intro a b h; exact Fin.ext (congrArg (fun j : Fin 7 => j.val) h)⟩
def divide (l : MatrixUnaryDivision.Label) :
    TM2.Stmt (fun _ : Fin 7 => Bool) MatrixUnaryDivision.Label Bool :=
  BitMachineStackEmbedding.stmt divSlots id id id none (MatrixUnaryDivision.program l)
def divided (a b : ℕ) : Fin 7 → List Bool :=
  bank divSlots (parsed a b)
    (MatrixUnaryDivision.cfg none false [] (List.replicate b true) []
      (List.replicate (a%b) true) (List.replicate (a/b) true) []).stk

theorem divide_run (a b : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime a b,
      ((advance divide)^[t])
        (⟨some .start,false,parsed a b⟩ : TM2.Cfg (fun _ : Fin 7 => Bool) _ _) =
        ⟨none,false,divided a b⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate a true) (List.replicate b true) [] [] [] []
  have hlocal := MatrixUnaryDivision.division_total_run a b
  change ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime a b]) c =
    MatrixUnaryDivision.cfg none false [] (List.replicate b true) []
      (List.replicate (a%b) true) (List.replicate (a/b) true) [] at hlocal
  have hhalt : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime a b]) c).l=none := by
    rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime a b]) c = _ from hlocal]
    rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs divSlots (parsed a b)
    id id id (by intro v; rfl) none MatrixUnaryDivision.program divide (by intro l; rfl)
    c (MatrixUnaryDivision.totalTime a b) hhalt
  have hbank : bank divSlots (parsed a b) c.stk=parsed a b := by
    apply bank_eq_self
    intro j
    fin_cases j <;> rfl
  rw [hlocal] at he
  change ((advance divide)^[t]) ⟨some .start,false,bank divSlots (parsed a b) c.stk⟩ =
    ⟨none,false,divided a b⟩ at he
  exact ⟨t,ht,by simpa only [hbank] using he⟩

def program := BitMachineRawSequence.program parse divide .start false false
def start : BitMachineRawSequence.Label PL MatrixUnaryDivision.Label :=
  BitMachineRawSequence.leftLabel PL.first
noncomputable def machine : BitMachine.Machine :=
  ofFinite (6 : Fin 7) 4 start (false,false) program

theorem outputs (a b : ℕ) :
    machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (a/b) true) (9*a+4*b+7) := by
  obtain ⟨t,ht,he⟩ := divide_run a b
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs parse divide .first .start
    false false false false
    (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk
    (parsed a b) (divided a b) (a+b+2) t (parse_run a b) he
  change ((advance program)^[u])
    (⟨some start,(false,false),
      (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
      TM2.Cfg (fun _ : Fin 7 => Bool) _ _) = ⟨none,(false,false),divided a b⟩ at hr
  have hi : rawInit (6 : Fin 7) start (false,false) (MatrixUnaryArithmetic.encodeInput a b) =
      (⟨some start,(false,false),
        (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 7 => Bool) _ _) := by
    unfold rawInit cfg
    congr 1
    funext j; fin_cases j <;> simp
  apply outputsWithin_of_raw_run (6 : Fin 7) 4 start (false,false) program
    (MatrixUnaryArithmetic.encodeInput a b) (List.replicate (a/b) true) u _
    (by have htime := MatrixUnaryDivision.totalTime_bound a b; omega)
  · rw [hi]
    exact congrArg (fun c => c.l) hr
  · rw [hi,hr]
    change divided a b (divSlots 4)=_
    rw [divided,bank_at]
    rfl

#print axioms outputs
end
end D22UnaryDivision
