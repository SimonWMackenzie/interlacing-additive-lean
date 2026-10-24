import CurrentAdditive.GenericParameterBranch
import EthInapproximability.CurrentPaper.ExactParameterMachinePair

/-! Run two fixed scalar programs on physical copies of the same input,
then physically pack their unary answers as a separated pair. -/
namespace V22UnaryFork
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
abbrev Work (M : BitMachine.Machine) := Fin M.stackCount ⊕ Fin 3
abbrev Stack (M N : BitMachine.Machine) := Fin 4 ⊕ (Work M ⊕ Work N)

def slotsA (M N : BitMachine.Machine) : CurrentAdditive.GenericParameterBranch.Stack M (Fin 4) ↪ Stack M N where
  toFun | .inl j => .inl j | .inr j => .inr (.inl j)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def slotsB (M N : BitMachine.Machine) : CurrentAdditive.GenericParameterBranch.Stack N (Fin 4) ↪ Stack M N where
  toFun | .inl j => .inl j | .inr j => .inr (.inr j)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def pairSlots (M N : BitMachine.Machine) : Fin 3 ↪ Stack M N :=
  ⟨![.inl 1,.inl 2,.inl 3], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def progA (M N : BitMachine.Machine) :=
  CurrentAdditive.GenericParameterBranch.framedProgram M (0 : Fin 4) 1 (slotsA M N)
def progB (M N : BitMachine.Machine) :=
  CurrentAdditive.GenericParameterBranch.framedProgram N (0 : Fin 4) 2 (slotsB M N)
def pairProgram (M N : BitMachine.Machine) := fun l =>
  stackStmt (pairSlots M N) (ExactParameterMachinePair.program l)
def abProgram (M N : BitMachine.Machine) :=
  BitMachineRawSequence.program (progA M N) (progB M N)
    (CurrentAdditive.GenericParameterBranch.startLabel N)
    (CurrentAdditive.GenericParameterBranch.startControl M) (CurrentAdditive.GenericParameterBranch.startControl N)
def program (M N : BitMachine.Machine) :=
  BitMachineRawSequence.program (abProgram M N) (pairProgram M N)
    ExactParameterMachinePair.Label.right
    (CurrentAdditive.GenericParameterBranch.startControl M,CurrentAdditive.GenericParameterBranch.startControl N) false
def start (M N : BitMachine.Machine) : BitMachineRawSequence.Label (BitMachineRawSequence.Label (CurrentAdditive.GenericParameterBranch.Label M) (CurrentAdditive.GenericParameterBranch.Label N)) ExactParameterMachinePair.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (CurrentAdditive.GenericParameterBranch.startLabel M))
def control (M N : BitMachine.Machine) :=
  ((CurrentAdditive.GenericParameterBranch.startControl M,CurrentAdditive.GenericParameterBranch.startControl N),false)
noncomputable def machine (M N : BitMachine.Machine) : BitMachine.Machine :=
  ofFinite (.inl (0 : Fin 4)) (.inl (3 : Fin 4)) (start M N) (control M N)
    (program M N)

private theorem ambient_base (M : BitMachine.Machine) {J : Type*} [DecidableEq J]
    (ι : CurrentAdditive.GenericParameterBranch.Stack M (Fin 4) ↪ J) (S : J → List Bool)
    (target j : Fin 4) (bits result : List Bool) (T : ℕ) :
    bank ι S (CurrentAdditive.GenericParameterBranch.terminal M
      (fun k => S (ι (.inl k))) target bits result T) (ι (.inl j)) =
      if j=target then result else S (ι (.inl j)) := by
  by_cases h : j=target
  · subst j; simp [CurrentAdditive.GenericParameterBranch.ambient_target]
  · rw [CurrentAdditive.GenericParameterBranch.ambient_base_other M target j h]
    simp [h]

theorem outputs (M N : BitMachine.Machine) (input : List Bool)
    (a b ta tb : ℕ)
    (ha : M.OutputsWithin input (List.replicate a true) ta)
    (hb : N.OutputsWithin input (List.replicate b true) tb) :
    (machine M N).OutputsWithin input (MatrixUnaryArithmetic.encodeInput a b)
      (4*input.length+ta+tb+3*a+3*b+17) := by
  let S : Stack M N → List Bool := fun j => if j = .inl 0 then input else []
  let A := bank (slotsA M N) S (CurrentAdditive.GenericParameterBranch.terminal M
    (fun j => S (.inl j)) 1 input (List.replicate a true) ta)
  let B := bank (slotsB M N) A (CurrentAdditive.GenericParameterBranch.terminal N
    (fun j => A (.inl j)) 2 input (List.replicate b true) tb)
  have hA (j : Fin 4) : A (.inl j) = if j=1 then List.replicate a true else S (.inl j) :=
    ambient_base M (slotsA M N) S 1 j input (List.replicate a true) ta
  have hB (j : Fin 4) : B (.inl j) = if j=2 then List.replicate b true else A (.inl j) :=
    ambient_base N (slotsB M N) A 2 j input (List.replicate b true) tb
  obtain ⟨tA,htA,hrA⟩ := CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient
    M (0 : Fin 4) 1 input (List.replicate a true) ta (slotsA M N) S
    (by simp [S,slotsA]) (by simp [S,slotsA])
    (by intro j; simp [S,slotsA]) ha
  obtain ⟨tB,htB,hrB⟩ := CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient
    N (0 : Fin 4) 2 input (List.replicate b true) tb (slotsB M N) A
    (by simpa [slotsB,S] using hA 0) (by simpa [slotsB,S] using hA 2)
    (by
      intro j
      change A (.inr (.inr j)) = []
      dsimp only [A]
      rw [bank_outside]
      · simp [S]
      · rintro ⟨k,hk⟩; cases k <;> simp [slotsA] at hk) hb
  let C := bank (pairSlots M N) B
    (ExactParameterMachinePair.cfg none false [] []
      (MatrixUnaryArithmetic.encodeInput a b)).stk
  have hpairBank : bank (pairSlots M N) B
      (ExactParameterMachinePair.cfg (some .right) false
        (List.replicate a true) (List.replicate b true) []).stk = B := by
    apply bank_eq_self
    intro j; fin_cases j <;>
      simp [pairSlots,ExactParameterMachinePair.cfg,hB,hA,S]
  have hp := BitMachineStackRun.run (pairSlots M N) B
    ExactParameterMachinePair.program
    (ExactParameterMachinePair.cfg (some .right) false
      (List.replicate a true) (List.replicate b true) []) (a+b+3)
  rw [← ExactParameterMachinePair.run,ExactParameterMachinePair.exact_run] at hp
  have hrp : ((advance (pairProgram M N))^[a+b+3])
      (⟨some ExactParameterMachinePair.Label.right,false,B⟩ :
        TM2.Cfg (fun _ : Stack M N => Bool) _ _) = ⟨none,false,C⟩ := by
    simpa only [pairProgram,stackCfg,hpairBank,C] using hp
  obtain ⟨tAB,htAB,hrAB⟩ := BitMachineRawSequence.runs
    (progA M N) (progB M N)
    (CurrentAdditive.GenericParameterBranch.startLabel M) (CurrentAdditive.GenericParameterBranch.startLabel N)
    (CurrentAdditive.GenericParameterBranch.startControl M) (CurrentAdditive.GenericParameterBranch.startControl M)
    (CurrentAdditive.GenericParameterBranch.startControl N) (CurrentAdditive.GenericParameterBranch.startControl N)
    S A B tA tB (by simpa only [progA,A,slotsA] using hrA)
    (by simpa only [progB,B,slotsB] using hrB)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (abProgram M N) (pairProgram M N)
    (BitMachineRawSequence.leftLabel (CurrentAdditive.GenericParameterBranch.startLabel M))
    ExactParameterMachinePair.Label.right
    (CurrentAdditive.GenericParameterBranch.startControl M,CurrentAdditive.GenericParameterBranch.startControl N)
    (CurrentAdditive.GenericParameterBranch.startControl M,CurrentAdditive.GenericParameterBranch.startControl N)
    false false S B C tAB (a+b+3)
    (by simpa only [abProgram] using hrAB) hrp
  have hi : rawInit (.inl (0 : Fin 4)) (start M N) (control M N) input =
      (⟨some (start M N),control M N,S⟩ : TM2.Cfg (fun _ : Stack M N => Bool) _ _) := rfl
  apply outputsWithin_of_raw_run (.inl (0 : Fin 4)) (.inl (3 : Fin 4))
    (start M N) (control M N) (program M N) input
    (MatrixUnaryArithmetic.encodeInput a b) t _ (by
      simp only [List.length_replicate] at htA htB
      omega)
  · rw [hi]
    change (((advance _)^[t]) _).l = none
    change ((advance (program M N))^[t]) _ = _ at hr
    change ((advance (program M N))^[t]) _ = _ at hr
    simpa only [program,start,control] using congrArg TM2.Cfg.l hr
  · rw [hi]
    have hr' : ((advance (program M N))^[t])
        (⟨some (start M N),control M N,S⟩ : TM2.Cfg (fun _ : Stack M N => Bool) _ _) =
        ⟨none,control M N,C⟩ := by simpa only [program,start,control] using hr
    rw [hr']
    exact bank_at (pairSlots M N) B _ 2

#print axioms outputs
end V22UnaryFork
