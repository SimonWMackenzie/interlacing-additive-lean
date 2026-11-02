import EthInapproximability.CurrentPaper.QProduct
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Copy the computed product into the checked source-preserving unary-log
controller and run that controller on a disjoint embedded stack bank. -/

namespace EthInapproximability.CurrentPaper.QLog

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := QProduct.Stack
abbrev Local := ETHParameterScaleMachineLogCopy.Stack

def logSlots : Local ↪ Stack :=
  ⟨QProduct.log, by intro a b h; exact Sum.inr_injective (Sum.inr_injective h)⟩

def source : Stack := QProduct.log (.inl 0)
def answer : Stack :=
  QProduct.log (ETHParameterScaleMachineLogCopy.logStack
    ETHParameterScaleMachineLogCopy.logMachine.output)

def copySlots : Fin 3 ↪ Stack :=
  ⟨![QProduct.temp 5,source,QProduct.temp 6], by decide⟩

def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def logProgram := fun l => stackStmt logSlots
  (ETHParameterScaleMachineLogCopy.program l)

def copied (S : Stack → List Bool) (n : ℕ) : Stack → List Bool :=
  Function.update S source (List.replicate n true)

theorem copy_run (S : Stack → List Bool) (n : ℕ)
    (hn : S (QProduct.temp 5) = List.replicate n true)
    (hs : S source = []) (ht : S (QProduct.temp 6) = []) :
    ((advance copyProgram)^[2*n+2])
      (⟨some .scan,none,S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,copied S n⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run copySlots S ht
  simpa [copyProgram,copySlots,hn,hs,copied] using hr

theorem local_start_word (n : ℕ) (k : Local) :
    (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk k =
      if k = (.inl (0 : Fin 1)) then List.replicate n true else [] := by
  change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate n true) [] []).stk k = _
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p,rfl⟩ := hk
    rw [bank_at]
    fin_cases p <;> simp [ETHParameterScaleMachineLogCopy.copyStack,
      BitMachineCopy.cfg,BitMachineCopy.stackContents]
  · rw [bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : Local) := by
      intro he
      exact hk ⟨0,by simpa [ETHParameterScaleMachineLogCopy.copyStack]
        using he.symm⟩
    simp [hne]

theorem start_embedded (S : Stack → List Bool) (n : ℕ)
    (hlocal : ∀ k : Local, S (logSlots k) = []) :
    stackCfg logSlots S
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)) =
      ⟨some (.inl BitMachineCopy.Label.scan),
        ETHParameterScaleMachineLogCopy.copyControl none,copied S n⟩ := by
  have hb : bank logSlots S
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk =
      copied S n := by
    funext j
    by_cases hj : ∃ k : Local, logSlots k = j
    · obtain ⟨k,rfl⟩ := hj
      rw [bank_at,local_start_word]
      by_cases hk : k = (.inl (0 : Fin 1))
      · subst k; simp [copied,source,logSlots]
      · have hne : logSlots k ≠ source := by
          intro he; exact hk (logSlots.injective he)
        simp only [copied,Function.update_of_ne hne,if_neg hk,hlocal k]
    · have hn : j ≠ source := by
        intro he; exact hj ⟨.inl 0,by simpa [source] using he.symm⟩
      rw [bank_outside logSlots S _ j hj]
      simp only [copied,Function.update_of_ne hn]
  unfold stackCfg
  rw [hb]
  rfl

theorem log_run (S : Stack → List Bool) (n : ℕ)
    (hlocal : ∀ k : Local, S (logSlots k) = []) :
    ∃ t ≤ 2*n+2 +
      (UnaryBinaryEncoding.coefficient+6)*(n+1)^2,
      ∃ v : ETHParameterScaleMachineLogCopy.Control,
      ∃ F : Stack → List Bool,
        ((advance logProgram)^[t])
          (⟨some (.inl BitMachineCopy.Label.scan),
            ETHParameterScaleMachineLogCopy.copyControl none,
            copied S n⟩ : TM2.Cfg (fun _ : Stack => Bool)
              ETHParameterScaleMachineLogCopy.Label
              ETHParameterScaleMachineLogCopy.Control) =
          ⟨none,v,F⟩ ∧
        F answer = List.replicate (Nat.clog 2 n) true ∧
        (∀ j : GraphCountBridge.Stack, F (.inl j) = S (.inl j)) ∧
        (∀ j : Fin 10, F (QProduct.temp j) = S (QProduct.temp j)) := by
  obtain ⟨t,c,ht,hr,hh,ho⟩ :=
    ETHParameterScaleMachineLogCopy.copied_log_run n
  let foreign := S
  let D := ETHParameterScaleMachineLogCopy.afterLog
    (List.replicate n true) c
  let F := bank logSlots foreign D.stk
  have he := BitMachineStackRun.run logSlots foreign
    ETHParameterScaleMachineLogCopy.program
    (ETHParameterScaleMachineLogCopy.start (List.replicate n true)) t
  unfold ETHParameterScaleMachineLogCopy.run at hr
  rw [hr] at he
  refine ⟨t,ht,ETHParameterScaleMachineLogCopy.logControl c.var,F,?_,?_,?_,?_⟩
  · rw [← start_embedded S n hlocal]
    simpa [logProgram,F,D,ETHParameterScaleMachineLogCopy.afterLog,
      BitMachineStackEmbedding.stackCfg,BitMachineStackEmbedding.cfg,
      BitMachineInline.cfg,hh] using he
  · change F (logSlots (ETHParameterScaleMachineLogCopy.logStack
      ETHParameterScaleMachineLogCopy.logMachine.output)) = _
    dsimp only [F]
    rw [bank_at]
    exact (ETHParameterScaleMachineLogCopy.afterLog_output n c).trans ho
  · intro j
    have hj : ¬ ∃ k : Local, logSlots k = (.inl j : Stack) := by
      rintro ⟨k,h⟩; cases h
    exact bank_outside logSlots S D.stk (.inl j) hj
  · intro j
    have hj : ¬ ∃ k : Local, logSlots k = QProduct.temp j := by
      rintro ⟨k,h⟩; cases h
    exact bank_outside logSlots S D.stk (QProduct.temp j) hj

#print axioms copy_run
#print axioms log_run

end
end EthInapproximability.CurrentPaper.QLog
