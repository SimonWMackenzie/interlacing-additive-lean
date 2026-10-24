import Paper2.YaoFramedParameterBanks
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! For fixed `t`, the two literal unary constants required by the Yao
coordinate arithmetic are written by finite control, not supplied in the
initial bank. Each push, termination, and the inter-phase handoff is charged.
-/

namespace Paper2.YaoParameterBank

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

def fixedQ (t : ℕ) : ℕ := 2 ^ (t - 1)
def fixedPayloadK (t : ℕ) : ℕ := 2 ^ t * 2 ^ t
-- Historical local name: this is the *stride* K+1, not the payload cell width K.
def fixedK (t : ℕ) : ℕ := 2 ^ t * 2 ^ t + 1

theorem fixedK_eq_stride (t : ℕ) : fixedK t = fixedPayloadK t + 1 := rfl

abbrev ConstantStack := Fin 2
abbrev ConstantLabel (t : ℕ) :=
  BitMachineRawSequence.Label
    (SourceClauseFixedUnary.Label (fixedQ t))
    (SourceClauseFixedUnary.Label (fixedK t))
abbrev ConstantControl := Unit × Unit
abbrev ConstantCfg (t : ℕ) :=
  TM2.Cfg (fun _ : ConstantStack => Bool)
    (ConstantLabel t) ConstantControl

def constantProgram (t : ℕ) : ConstantLabel t →
    TM2.Stmt (fun _ : ConstantStack => Bool)
      (ConstantLabel t) ConstantControl :=
  BitMachineRawSequence.program
    (SourceClauseFixedUnary.program (0 : ConstantStack) (fixedQ t))
    (SourceClauseFixedUnary.program (1 : ConstantStack) (fixedK t))
    (0 : SourceClauseFixedUnary.Label (fixedK t)) () ()

def constantInitial (t : ℕ) : ConstantCfg t :=
  ⟨some (.inl 0), ((),()), fun _ => []⟩

def constantFinal (t : ℕ) : ConstantCfg t :=
  ⟨none, ((),()), ![List.replicate (fixedQ t) true,
    List.replicate (fixedK t) true]⟩

theorem fixed_Q_K_physical (t : ℕ) :
    ∃ steps ≤ fixedQ t + fixedK t + 3,
      ((advance (constantProgram t))^[steps]) (constantInitial t) =
        constantFinal t := by
  let S : ConstantStack → List Bool := fun _ => []
  let T := Function.update S (0 : ConstantStack)
    (List.replicate (fixedQ t) true)
  let U := Function.update T (1 : ConstantStack)
    (List.replicate (fixedK t) true)
  have hA : ((advance
      (SourceClauseFixedUnary.program (0 : ConstantStack) (fixedQ t)))^[fixedQ t + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label (fixedQ t)), (), S⟩ :
        TM2.Cfg (fun _ : ConstantStack => Bool)
          (SourceClauseFixedUnary.Label (fixedQ t)) Unit) =
      ⟨none, (), T⟩ :=
    SourceClauseFixedUnary.run 0 S (fixedQ t) rfl
  have hB : ((advance
      (SourceClauseFixedUnary.program (1 : ConstantStack) (fixedK t)))^[fixedK t + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label (fixedK t)), (), T⟩ :
        TM2.Cfg (fun _ : ConstantStack => Bool)
          (SourceClauseFixedUnary.Label (fixedK t)) Unit) =
      ⟨none, (), U⟩ :=
    SourceClauseFixedUnary.run 1 T (fixedK t) (by simp [T, S])
  obtain ⟨steps,hsteps,hrun⟩ :=
    BitMachineRawSequence.runs
      (SourceClauseFixedUnary.program (0 : ConstantStack) (fixedQ t))
      (SourceClauseFixedUnary.program (1 : ConstantStack) (fixedK t))
      (0 : SourceClauseFixedUnary.Label (fixedQ t))
      (0 : SourceClauseFixedUnary.Label (fixedK t))
      () () () () S T U (fixedQ t + 1) (fixedK t + 1) hA hB
  refine ⟨steps, by omega, ?_⟩
  have hU : U = (![List.replicate (fixedQ t) true,
      List.replicate (fixedK t) true] : ConstantStack → List Bool) := by
    funext j
    fin_cases j <;> simp [U, T, S, Function.update]
  rw [hU] at hrun
  simpa only [constantProgram, constantInitial, constantFinal,
    BitMachineRawSequence.leftLabel, S] using hrun

#print axioms fixed_Q_K_physical

/-- The same two physical writers operate on any pair of distinct ambient
stacks. Every other stack is retained exactly, which allows a later direct
join with the edge-count/label frame rather than a semantic bank rewrite. -/
theorem fixed_Q_K_ambient {K : Type*} [DecidableEq K]
    (t : ℕ) (qSlot kSlot : K) (hne : qSlot ≠ kSlot)
    (S : K → List Bool) (hq : S qSlot = []) (hk : S kSlot = []) :
    ∃ steps ≤ fixedQ t + fixedK t + 3,
      ((advance
        (BitMachineRawSequence.program
          (SourceClauseFixedUnary.program qSlot (fixedQ t))
          (SourceClauseFixedUnary.program kSlot (fixedK t))
          (0 : SourceClauseFixedUnary.Label (fixedK t)) () ()))^[steps])
        (⟨some (.inl (0 : SourceClauseFixedUnary.Label (fixedQ t))),
          ((),()), S⟩ : TM2.Cfg (fun _ : K => Bool)
            (ConstantLabel t) ConstantControl) =
      ⟨none, ((),()),
        Function.update (Function.update S qSlot
          (List.replicate (fixedQ t) true)) kSlot
          (List.replicate (fixedK t) true)⟩ := by
  let T := Function.update S qSlot (List.replicate (fixedQ t) true)
  let U := Function.update T kSlot (List.replicate (fixedK t) true)
  have hA := SourceClauseFixedUnary.run qSlot S (fixedQ t) hq
  have hT : T kSlot = [] := by simp [T, hne.symm, hk]
  have hB := SourceClauseFixedUnary.run kSlot T (fixedK t) hT
  obtain ⟨steps,hsteps,hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program qSlot (fixedQ t))
    (SourceClauseFixedUnary.program kSlot (fixedK t))
    (0 : SourceClauseFixedUnary.Label (fixedQ t))
    (0 : SourceClauseFixedUnary.Label (fixedK t))
    () () () () S T U (fixedQ t + 1) (fixedK t + 1) hA hB
  exact ⟨steps, by omega, hrun⟩

#print axioms fixed_Q_K_ambient

end Paper2.YaoParameterBank
