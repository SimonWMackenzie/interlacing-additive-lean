import EthInapproximability.CurrentPaper.GraphCountBridge
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import Mathlib.Data.Fin.VecNotation

/-! The two physical multiplications and a fixed twelve-bit seed produce
the exact unary argument of `Nat.clog 2` for the v8 q₂ parameter. -/

namespace EthInapproximability.CurrentPaper.QProduct

open Turing BitMachineEncoding
noncomputable section

abbrev LogStack := ETHParameterScaleMachineLogCopy.Stack
abbrev Stack := GraphCountBridge.Stack ⊕ (Fin 10 ⊕ LogStack)

def parserWriterSlots : GraphCountBridge.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def temp (j : Fin 10) : Stack := .inr (.inl j)
def log (j : LogStack) : Stack := .inr (.inr j)
def edge : Stack := .inl (.inl (.inr 1))
def s : Stack := .inl (.inr 28)
def q : Stack := .inl (.inr 56)

def firstSlots : Fin 6 ↪ Stack :=
  ⟨![s,edge,temp 0,temp 1,temp 2,temp 3], by decide⟩
def secondSlots : Fin 6 ↪ Stack :=
  ⟨![temp 3,temp 4,temp 0,temp 1,temp 2,temp 5], by decide⟩

def firstProgram := MatrixStage4ScalarPreparationOps.multiplyProgram firstSlots
def secondProgram := MatrixStage4ScalarPreparationOps.multiplyProgram secondSlots

def seeded (S : Stack → List Bool) : Stack → List Bool :=
  Function.update S (temp 4) (List.replicate 12 true)

def seedStmt : ℕ → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | 0 => .halt
  | n+1 => .push (temp 4) (fun _ => true) (seedStmt n)

def seedProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit :=
  fun _ => seedStmt 12

theorem seed_run (S : Stack → List Bool) (h : S (temp 4) = []) :
    advance seedProgram (⟨some (),(),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none,(),seeded S⟩ := by
  simp [seedProgram, seedStmt, advance, TM2.step, TM2.stepAux,
    seeded, h]

def firstBank (S : Stack → List Bool) (bins edges : ℕ) :
    Stack → List Bool :=
  Function.update S (temp 3) (List.replicate (bins * edges) true)

def secondBank (S : Stack → List Bool) (bins edges : ℕ) :
    Stack → List Bool :=
  Function.update (seeded (firstBank S bins edges)) (temp 5)
    (List.replicate (12 * bins * edges) true)

theorem first_run (S : Stack → List Bool) (bins edges : ℕ)
    (hs : S s = List.replicate bins true)
    (he : S edge = List.replicate edges true)
    (h0 : S (temp 0) = []) (h1 : S (temp 1) = [])
    (h2 : S (temp 2) = []) (h3 : S (temp 3) = []) :
    ((advance firstProgram)^[MatrixAddressMachine.exactTime bins edges 0])
      (⟨some .outer,false,S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none,false,firstBank S bins edges⟩ := by
  simpa [firstProgram,firstBank,firstSlots,hs,he,h3] using
    MatrixStage4ScalarPreparationOps.multiply_run firstSlots S bins edges
      hs he h0 h1 h2

theorem second_run (S : Stack → List Bool) (bins edges : ℕ)
    (h0 : S (temp 0) = []) (h1 : S (temp 1) = [])
    (h2 : S (temp 2) = [])
    (h5 : S (temp 5) = []) :
    ((advance secondProgram)^[MatrixAddressMachine.exactTime (bins*edges) 12 0])
      (⟨some .outer,false,seeded (firstBank S bins edges)⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          MatrixAddressMachine.Label Bool) =
      ⟨none,false,secondBank S bins edges⟩ := by
  let T := seeded (firstBank S bins edges)
  have hp : T (secondSlots 0) = List.replicate (bins*edges) true := by
    simp [T,seeded,firstBank,secondSlots,temp]
  have hc : T (secondSlots 1) = List.replicate 12 true := by
    simp [T,seeded,firstBank,secondSlots,temp]
  have h0' : T (secondSlots 2) = [] := by
    simpa [T,seeded,firstBank,secondSlots,temp] using h0
  have h1' : T (secondSlots 3) = [] := by
    simpa [T,seeded,firstBank,secondSlots,temp] using h1
  have h2' : T (secondSlots 4) = [] := by
    simpa [T,seeded,firstBank,secondSlots,temp] using h2
  have hr := MatrixStage4ScalarPreparationOps.multiply_run secondSlots T
    (bins*edges) 12 hp hc h0' h1' h2'
  have hT5 : T (temp 5) = [] := by
    simpa [T,seeded,firstBank,temp] using h5
  have hnum : (bins * edges) * 12 = 12 * bins * edges := by ring
  simpa [secondProgram,secondBank,T,hnum,secondSlots,hT5] using hr

#print axioms seed_run
#print axioms first_run
#print axioms second_run

end
end EthInapproximability.CurrentPaper.QProduct
