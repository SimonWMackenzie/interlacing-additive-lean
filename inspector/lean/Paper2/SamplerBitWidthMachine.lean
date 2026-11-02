import Paper2.SamplerAlphabetMachine
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun

set_option maxHeartbeats 8000000

namespace Paper2.SamplerBitWidthMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

abbrev Stack := SamplerAlphabetMachine.Stack ⊕ ETHParameterScaleMachineLogCopy.Stack

def alphabetEmbed : SamplerAlphabetMachine.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro a b h; exact Sum.inl.inj h

def logEmbed : ETHParameterScaleMachineLogCopy.Stack ↪ Stack where
  toFun := Sum.inr
  inj' := by intro a b h; exact Sum.inr.inj h

def logSource : Stack := .inr (.inl 0)
noncomputable def logOutput : Stack := .inr (ETHParameterScaleMachineLogCopy.logStack ETHParameterScaleMachineLogCopy.logMachine.output)

def bridge : Fin 3 ↪ Stack where
  toFun := ![.inl 7, logSource, .inl 8]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [logSource, Fin.ext_iff] at h ⊢

noncomputable def initial (q₁ q₂ s w Q n p : Nat) : Stack → List Bool :=
  Sum.elim (SamplerAlphabetMachine.input q₁ q₂ s w Q n p) (fun _ => [])

def M (q₁ q₂ s w Q n p : Nat) : Nat :=
  RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p

noncomputable def afterAlphabet (q₁ q₂ s w Q n p : Nat) :
    Stack → List Bool :=
  Function.update (initial q₁ q₂ s w Q n p) (.inl 7)
    (List.replicate (M q₁ q₂ s w Q n p) true)

noncomputable def afterBridge (q₁ q₂ s w Q n p : Nat) :
    Stack → List Bool :=
  Function.update (afterAlphabet q₁ q₂ s w Q n p) logSource
    (List.replicate (M q₁ q₂ s w Q n p) true)

def alphabetProgram := fun l => stackStmt alphabetEmbed (SamplerAlphabetMachine.program SamplerAlphabetMachine.slots l)
def bridgeProgram := MatrixStage4ScalarPreparationOps.copyProgram bridge
noncomputable def logProgram := fun l => stackStmt logEmbed (ETHParameterScaleMachineLogCopy.program l)

abbrev FirstLabel := BitMachineRawSequence.Label (SamplerAlphabetMachine.Label SamplerAlphabetMachine.slots) BitMachineCopy.Label
abbrev FirstControl := SamplerAlphabetMachine.Control SamplerAlphabetMachine.slots × Option Bool
abbrev Label := BitMachineRawSequence.Label FirstLabel ETHParameterScaleMachineLogCopy.Label
abbrev Control := FirstControl × ETHParameterScaleMachineLogCopy.Control

noncomputable def firstProgram := BitMachineRawSequence.program
  alphabetProgram bridgeProgram BitMachineCopy.Label.scan
  (SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots) none

noncomputable def program := BitMachineRawSequence.program
  firstProgram logProgram (Sum.inl BitMachineCopy.Label.scan)
  ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none) (ETHParameterScaleMachineLogCopy.copyControl none)

theorem log_start_word (m : Nat) (k : ETHParameterScaleMachineLogCopy.Stack) :
    (ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k =
      if k = .inl 0 then List.replicate m true else [] := by
  change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate m true) [] []).stk k = _
  by_cases hk : ∃ j : Fin 3, ETHParameterScaleMachineLogCopy.copyStack j = k
  · obtain ⟨j,rfl⟩ := hk
    rw [bank_at]
    fin_cases j <;> simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg,
      BitMachineCopy.stackContents]
  · rw [bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl 0 : ETHParameterScaleMachineLogCopy.Stack) := by
      intro h
      apply hk
      exact ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using h.symm⟩
    simp [hne]

theorem afterBridge_log_start (q₁ q₂ s w Q n p : Nat) :
    ∀ k : ETHParameterScaleMachineLogCopy.Stack,
      (ETHParameterScaleMachineLogCopy.start (List.replicate (M q₁ q₂ s w Q n p) true)).stk k =
        afterBridge q₁ q₂ s w Q n p (.inr k) := by
  intro k
  rw [log_start_word]
  by_cases hk : k = .inl 0
  · subst k
    simp only [ite_true, afterBridge, logSource,
      Function.update_self]
  · have hne : (Sum.inr k : Stack) ≠ logSource := by
      intro h
      exact hk (Sum.inr.inj (show (Sum.inr k : Stack) = Sum.inr (.inl 0) from h))
    have hleft : (Sum.inr k : Stack) ≠ Sum.inl (7 : Fin 9) := by simp
    simp only [if_neg hk, afterBridge, Function.update_of_ne hne,
      afterAlphabet, Function.update_of_ne hleft]
    rfl

theorem exact_bit_width (q₁ q₂ s w Q n p : Nat) :
    ∃ (t : Nat) (F : Stack → List Bool)
      (v : ETHParameterScaleMachineLogCopy.Control),
      t ≤ (515 + 30 + 2 * (q₁ + q₂ + 4*s + w + Q + n + p)) +
        (2 * M q₁ q₂ s w Q n p + 2) +
        (2 * M q₁ q₂ s w Q n p + 2 +
          (UnaryBinaryEncoding.coefficient + 6) *
            (M q₁ q₂ s w Q n p + 1)^2) + 2 ∧
      ((advance program)^[t])
        (⟨some (.inl (.inl (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots))),
          (((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none), ETHParameterScaleMachineLogCopy.copyControl none),
          initial q₁ q₂ s w Q n p⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, (((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none), v), F⟩ ∧
      F (.inl 7) = List.replicate (M q₁ q₂ s w Q n p) true ∧
      F logOutput = List.replicate
        (Nat.clog 2 (M q₁ q₂ s w Q n p)) true ∧
      (∀ i : SamplerAlphabetMachine.Source, F (.inl ⟨i.val, by omega⟩) =
        List.replicate (SamplerAlphabetMachine.count q₁ q₂ s w Q n p i) true) := by
  let m := M q₁ q₂ s w Q n p
  let S := initial q₁ q₂ s w Q n p
  let T := afterAlphabet q₁ q₂ s w Q n p
  let U := afterBridge q₁ q₂ s w Q n p
  obtain ⟨ta, hta, ha⟩ := SamplerAlphabetMachine.exact_alphabet q₁ q₂ s w Q n p
  have ha' :
      ((advance alphabetProgram)^[ta])
        (⟨some (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots), SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (SamplerAlphabetMachine.Label SamplerAlphabetMachine.slots) (SamplerAlphabetMachine.Control SamplerAlphabetMachine.slots)) =
        ⟨none, SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots, T⟩ := by
    have h := BitMachineStackRun.run alphabetEmbed S (SamplerAlphabetMachine.program SamplerAlphabetMachine.slots)
      (⟨some (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots), SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots,
        SamplerAlphabetMachine.input q₁ q₂ s w Q n p⟩) ta
    rw [ha] at h
    have hs : bank alphabetEmbed S (SamplerAlphabetMachine.input q₁ q₂ s w Q n p) = S := by
      apply bank_eq_self
      intro k
      rfl
    have ht : bank alphabetEmbed S
        (Function.update (SamplerAlphabetMachine.input q₁ q₂ s w Q n p) 7
          (List.replicate
            (RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p) true)) = T := by
      rw [bank_update, hs]
      rfl
    simp only [stackCfg] at h
    rw [hs, ht] at h
    simpa only [alphabetProgram, S, T] using h
  have hscratch : T (bridge 2) = [] := by
    change (Function.update S (.inl 7) (List.replicate m true)) (.inl 8) = []
    rw [Function.update_of_ne (by decide)]
    rfl
  have hsource : T (bridge 0) = List.replicate m true := by
    exact Function.update_self ..
  have htarget : T (bridge 1) = [] := by
    change (Function.update S (.inl 7) (List.replicate m true)) logSource = []
    rw [Function.update_of_ne (by simp [logSource])]
    rfl
  have hb := MatrixStage4ScalarPreparationOps.copy_run bridge T hscratch
  have hb' :
      ((advance bridgeProgram)^[2*m+2])
        (⟨some BitMachineCopy.Label.scan, none, T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, U⟩ := by
    rw [hsource, List.length_replicate] at hb
    have hU : Function.update T (bridge 1)
        (List.replicate m true ++ T (bridge 1)) = U := by
      rw [htarget, List.append_nil]
      rfl
    rw [hU] at hb
    exact hb
  obtain ⟨tfirst, htfirst, hfirst⟩ := BitMachineRawSequence.runs
    alphabetProgram bridgeProgram
    (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots) BitMachineCopy.Label.scan
    (SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots) (SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots) none none
    S T U ta (2*m+2) ha' hb'
  obtain ⟨tc, c, htc, hlog, hc, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run m
  have hlogstart : bank logEmbed U
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk = U :=
    bank_eq_self logEmbed U _ (by
      intro k
      exact afterBridge_log_start q₁ q₂ s w Q n p k)
  let F := bank logEmbed U (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk
  have hlog' :
      ((advance logProgram)^[tc])
        (⟨some (.inl BitMachineCopy.Label.scan), ETHParameterScaleMachineLogCopy.copyControl none, U⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ETHParameterScaleMachineLogCopy.Label ETHParameterScaleMachineLogCopy.Control) =
        ⟨none, (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).var, F⟩ := by
    have h := BitMachineStackRun.run logEmbed U ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) tc
    change ((advance ETHParameterScaleMachineLogCopy.program)^[tc])
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) = _ at hlog
    rw [hlog] at h
    have hlabel : (ETHParameterScaleMachineLogCopy.afterLog
        (List.replicate m true) c).l = none := by
      simp [ETHParameterScaleMachineLogCopy.afterLog,
        BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hc]
    simp only [stackCfg, hlogstart, hlabel] at h
    simpa only [logProgram, F] using h
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    firstProgram logProgram
    (.inl (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots)) (.inl BitMachineCopy.Label.scan)
    ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none)
    ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none)
    (ETHParameterScaleMachineLogCopy.copyControl none)
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).var
    S U F tfirst tc hfirst hlog'
  refine ⟨t, F, (ETHParameterScaleMachineLogCopy.afterLog
    (List.replicate m true) c).var, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [m] at *
    omega
  · simpa only [program, firstProgram] using hr
  · have houtside : ¬ ∃ k : ETHParameterScaleMachineLogCopy.Stack, logEmbed k = (.inl 7 : Stack) := by
      rintro ⟨k,hk⟩; cases hk
    rw [show F (.inl 7) = U (.inl 7) from bank_outside logEmbed U _ _ houtside]
    change (Function.update T logSource (List.replicate m true)) (.inl 7) = _
    rw [Function.update_of_ne (by simp [logSource])]
    exact Function.update_self ..
  · change bank logEmbed U _ (logEmbed (ETHParameterScaleMachineLogCopy.logStack ETHParameterScaleMachineLogCopy.logMachine.output)) = _
    rw [bank_at, ETHParameterScaleMachineLogCopy.afterLog_output]
    exact ho
  · intro i
    have houtside : ¬ ∃ k : ETHParameterScaleMachineLogCopy.Stack,
        logEmbed k = (.inl ⟨i.val, by omega⟩ : Stack) := by
      rintro ⟨k,hk⟩; cases hk
    rw [show F (.inl ⟨i.val, by omega⟩) =
      U (.inl ⟨i.val, by omega⟩) from
        bank_outside logEmbed U _ _ houtside]
    have hraw : U (.inl ⟨i.val, by omega⟩) =
        S (.inl ⟨i.val, by omega⟩) := by
      change (Function.update T logSource (List.replicate m true))
        (.inl ⟨i.val, by omega⟩) = _
      rw [Function.update_of_ne (by simp [logSource])]
      have hne : (.inl ⟨i.val, by omega⟩ : Stack) ≠ .inl 7 := by
        intro h
        have hv := congrArg (fun j : Stack => j) h
        have hi := i.isLt
        have hn := congrArg Fin.val (Sum.inl.inj hv)
        simp at hn
        omega
      change (Function.update S (.inl 7) (List.replicate m true))
        (.inl ⟨i.val, by omega⟩) = _
      simp only [Function.update_of_ne hne]
    rw [hraw]
    fin_cases i <;> rfl

#print axioms exact_bit_width

end Paper2.SamplerBitWidthMachine
