import CurrentAdditive.D22UnaryDivision
import EthInapproximability.CurrentPaper.EntryUnaryCompare

/-! An actual unary comparison returning unary zero or one. The later
one-bit adapter is also literal: it tests physical stack non-emptiness. -/
namespace D22UnaryLe
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open D22UnaryDivision
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384

def compare := EntryUnaryCompare.program (0 : Fin 7) 1 4 true true false
def finish : Fin 1 → TM2.Stmt (fun _ : Fin 7 => Bool) (Fin 1) Bool
  | _ => .pop 4 (fun _ b => b.getD false)
      (.branch id (.push 5 (fun _ => true) .halt) .halt)
def compProgram := BitMachineRawSequence.program compare finish 0
  ((none,none) : EntryUnaryCompare.CV) false
def compStart : BitMachineRawSequence.Label EntryUnaryCompare.CL (Fin 1) :=
  BitMachineRawSequence.leftLabel .loop
def compControl := (((none,none) : EntryUnaryCompare.CV),false)
def compFinal (a b : ℕ) : Fin 7 → List Bool :=
  let F := Function.update (Function.update (Function.update (parsed a b) 0 []) 1 [])
    4 [EntryUnaryCompare.verdict true true false a b]
  Function.update (Function.update F 4 []) 5
    (List.replicate (if a≤b then 1 else 0) true)

theorem verdict_eq (a b : ℕ) :
    EntryUnaryCompare.verdict true true false a b=decide (a≤b) := by
  unfold EntryUnaryCompare.verdict
  split_ifs <;> simp_all <;> omega

theorem comp_run (a b : ℕ) :
    ∃ t ≤ max a b+4, ∃ v,
      ((advance compProgram)^[t])
        (⟨some compStart,compControl,parsed a b⟩ : TM2.Cfg (fun _ : Fin 7 => Bool) _ _) =
        ⟨none,v,compFinal a b⟩ := by
  obtain ⟨t,ht,v,he⟩ := EntryUnaryCompare.compare_run (0 : Fin 7) 1 4
    (by decide) (by decide) (by decide) true true false (parsed a b) (none,none) a b rfl rfl
  let F := Function.update (Function.update (Function.update (parsed a b) 0 []) 1 [])
    4 [EntryUnaryCompare.verdict true true false a b]
  change ((advance compare)^[t])
    (⟨some .loop,(none,none),parsed a b⟩ : TM2.Cfg (fun _ : Fin 7 => Bool) _ _) =
    ⟨none,v,F⟩ at he
  have hf : ((advance finish)^[1])
      (⟨some 0,false,F⟩ : TM2.Cfg (fun _ : Fin 7 => Bool) (Fin 1) Bool) =
      ⟨none,decide (a≤b),compFinal a b⟩ := by
    by_cases hab : a≤b <;>
      simp [advance,finish,TM2.step,TM2.stepAux,F,compFinal,verdict_eq,hab,parsed]
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs compare finish .loop 0
    (none,none) v false (decide (a≤b)) (parsed a b) F (compFinal a b) t 1 he hf
  exact ⟨u,by omega,((none,none),decide (a≤b)),hr⟩

def program := BitMachineRawSequence.program parse compProgram compStart false compControl
def start : BitMachineRawSequence.Label PL (BitMachineRawSequence.Label EntryUnaryCompare.CL (Fin 1)) :=
  BitMachineRawSequence.leftLabel PL.first
def control := (false,compControl)
noncomputable def machine : BitMachine.Machine := ofFinite (6 : Fin 7) 5 start control program

theorem outputs (a b : ℕ) :
    machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (if a≤b then 1 else 0) true) (3*(a+b+3)) := by
  obtain ⟨t,ht,v,he⟩ := comp_run a b
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs parse compProgram .first compStart
    false false compControl v
    (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk
    (parsed a b) (compFinal a b) (a+b+2) t (parse_run a b) he
  change ((advance program)^[u])
    (⟨some start,control,(cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
      TM2.Cfg (fun _ : Fin 7 => Bool) _ _) = ⟨none,(false,v),compFinal a b⟩ at hr
  have hi : rawInit (6 : Fin 7) start control (MatrixUnaryArithmetic.encodeInput a b) =
      (⟨some start,control,(cfg (some .first) false (MatrixUnaryArithmetic.encodeInput a b) [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 7 => Bool) _ _) := by
    unfold rawInit cfg
    congr 1
    funext j; fin_cases j <;> simp
  apply outputsWithin_of_raw_run (6 : Fin 7) 5 start control program
    (MatrixUnaryArithmetic.encodeInput a b) (List.replicate (if a≤b then 1 else 0) true) u _
    (by have hmax : max a b≤a+b := max_le (by omega) (by omega); omega)
  · rw [hi]; exact congrArg (fun c => c.l) hr
  · rw [hi,hr]
    simp [compFinal]

def bitProgram : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Bool
  | _ => .pop 0 (fun _ b => b.isSome) (.push 1 id .halt)
noncomputable def bitMachine : BitMachine.Machine := ofFinite (0 : Fin 2) 1 () false bitProgram
theorem bit_outputs (b : Bool) :
    bitMachine.OutputsWithin (List.replicate (if b then 1 else 0) true) [b] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () false bitProgram
    (List.replicate (if b then 1 else 0) true) [b] 1 1 (by omega)
  · cases b <;> simp [advance,rawInit,bitProgram,TM2.step,TM2.stepAux]
  · cases b <;> simp [advance,rawInit,bitProgram,TM2.step,TM2.stepAux]

#print axioms outputs
#print axioms bit_outputs
end
end D22UnaryLe
