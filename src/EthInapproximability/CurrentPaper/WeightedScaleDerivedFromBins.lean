import EthInapproximability.CurrentPaper.WeightedBinsGraphQ
import EthInapproximability.CurrentPaper.FirstExponentArithmetic
import EthInapproximability.CurrentPaper.FirstExponentWriterTransfer
import EthInapproximability.CurrentPaper.BalanceOrderCleanup
import EthInapproximability.CurrentPaper.BalanceOrderActualScale
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! Reuse the *same* scale word retained by the raw-six bins producer to
derive firstExponent and balanceOrder. No second copy of the six raw inputs
is placed in the initial bank and no scale producer is rerun. -/

namespace EthInapproximability.CurrentPaper.WeightedScaleDerivedFromBins

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedBinsGraphQ.Stack ⊕
  (Fin 2 ⊕ BalanceOrderArithmetic.Stack)
def upstreamSlots : WeightedBinsGraphQ.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def source : Stack :=
  .inl (.inl (.inl (.inr ScaleFinalScratch.answerKey)))
def writer (k : Fin 64) : Stack :=
  .inl (WeightedBinsGraphQ.writer k)
def aWork (k : Fin 2) : Stack := .inr (.inl k)
def balance (k : BalanceOrderArithmetic.Stack) : Stack := .inr (.inr k)
def aSlots : Fin 4 ↪ Stack :=
  ⟨![source,aWork 0,writer 54,aWork 1],by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [source,aWork,writer,WeightedBinsGraphQ.writer,
        WeightedGraphQJoined.writer] at h ⊢⟩
def copySlots : Fin 3 ↪ Stack :=
  ⟨![source,balance 0,balance 2],by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [source,balance] at h ⊢⟩
def balanceSlots : BalanceOrderArithmetic.Stack ↪ Stack :=
  ⟨balance,by intro a b h; exact Sum.inr_injective (Sum.inr_injective h)⟩
def initialBank (S : WeightedBinsGraphQ.Stack → List Bool) :
    Stack → List Bool := Sum.elim S (fun _ => [])
def afterA (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input) : Stack → List Bool :=
  Function.update (initialBank S) (writer 54)
    (List.replicate (Parameters.firstExponent i) true)
def afterCopy (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input) : Stack → List Bool :=
  Function.update (afterA S i) (balance 0)
    (List.replicate (Parameters.scale i) true)
def finalBank (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input) : Stack → List Bool :=
  Function.update (afterCopy S i) (balance 1)
    (List.replicate (Parameters.balanceOrder i) true)
def aProgram := fun l => stackStmt aSlots (FirstExponentArithmetic.program l)
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def balanceProgram := fun l => stackStmt balanceSlots
  (BalanceOrderCleanup.fullProgram l)
def aStart := FirstExponentWriterTransfer.arithmeticStart
def aControl : FirstExponentArithmetic.Control := (none,false)
def bControl := BalanceOrderActualScale.arithmeticControl
def phaseProgram := BitMachineRawSequence.program aProgram copyProgram
  BitMachineCopy.Label.scan aControl (none : Option Bool)
def program := BitMachineRawSequence.program phaseProgram balanceProgram
  BalanceOrderCleanup.start (aControl,(none : Option Bool)) bControl
def initialControl := ((aControl,(none : Option Bool)),bControl)
def bound (i : Parameters.Input) : ℕ :=
  FirstExponentArithmetic.bound (Parameters.scale i) +
  (2*Parameters.scale i+2) +
  BalanceOrderCleanup.fullTime (Parameters.scale i) + 2

theorem a_run (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input)
    (hs : S (.inl (.inl (.inr ScaleFinalScratch.answerKey))) =
      List.replicate (Parameters.scale i) true)
    (h54 : S (WeightedBinsGraphQ.writer 54) = []) :
    ∃ u ≤ FirstExponentArithmetic.bound (Parameters.scale i),
      ((advance aProgram)^[u])
        (⟨some aStart,aControl,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,aControl,afterA S i⟩ := by
  obtain ⟨u,hu,hr⟩ :=
    FirstExponentArithmetic.exact_run (Parameters.scale i)
  have hlocal : (fun k : Fin 4 => (initialBank S) (aSlots k)) =
      FirstExponentArithmetic.initialBank (Parameters.scale i) := by
    funext k
    fin_cases k <;>
      simp [initialBank,aSlots,source,aWork,writer,
        FirstExponentArithmetic.initialBank,hs,h54]
  have hi : bank aSlots (initialBank S)
      (FirstExponentArithmetic.initialBank (Parameters.scale i)) =
      initialBank S :=
    bank_eq_self aSlots _ _ (fun k => (congrFun hlocal k).symm)
  have ho : bank aSlots (initialBank S)
      (FirstExponentArithmetic.finalBank (Parameters.scale i)) =
      afterA S i := by
    have hfinal : FirstExponentArithmetic.finalBank (Parameters.scale i) =
        Function.update
          (fun k => (initialBank S) (aSlots k)) 2
          (List.replicate (Parameters.firstExponent i) true) := by
      rw [hlocal]
      funext k
      fin_cases k <;>
        simp [FirstExponentArithmetic.finalBank,
          FirstExponentArithmetic.initialBank,Parameters.firstExponent]
    rw [hfinal,bank_update,bank_restrict]
    rfl
  have he := BitMachineStackRun.run aSlots (initialBank S)
    FirstExponentArithmetic.program
    (⟨some aStart,aControl,
      FirstExponentArithmetic.initialBank (Parameters.scale i)⟩ :
      TM2.Cfg (fun _ : Fin 4 => Bool) _ _) u
  have hr0 :
      ((advance FirstExponentArithmetic.program)^[u])
        (⟨some aStart,aControl,
          FirstExponentArithmetic.initialBank (Parameters.scale i)⟩ :
          TM2.Cfg (fun _ : Fin 4 => Bool) _ _) =
        ⟨none,aControl,
          FirstExponentArithmetic.finalBank (Parameters.scale i)⟩ := by
    simpa only [aStart,aControl,
      FirstExponentWriterTransfer.arithmeticStart] using hr
  rw [hr0] at he
  refine ⟨u,hu,?_⟩
  simpa only [aProgram,stackCfg,hi,ho] using he

theorem copy_run (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input)
    (hs : S (.inl (.inl (.inr ScaleFinalScratch.answerKey))) =
      List.replicate (Parameters.scale i) true) :
    ((advance copyProgram)^[2*Parameters.scale i+2])
      (⟨some BitMachineCopy.Label.scan,none,afterA S i⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterCopy S i⟩ := by
  have hsrc : (afterA S i) (copySlots 0) =
      List.replicate (Parameters.scale i) true := by
    have hn : source ≠ writer 54 := by
      simp [source,writer,WeightedBinsGraphQ.writer,
        WeightedGraphQJoined.writer]
    change (Function.update (initialBank S) (writer 54)
      (List.replicate (Parameters.firstExponent i) true)) source = _
    rw [Function.update_of_ne hn]
    exact hs
  have hdst : (afterA S i) (copySlots 1) = [] := by
    simp [afterA,initialBank,copySlots,balance,writer]
  have hscr : (afterA S i) (copySlots 2) = [] := by
    simp [afterA,initialBank,copySlots,balance,writer]
  have hr := MatrixStage4ScalarPreparationOps.copy_run copySlots
    (afterA S i) hscr
  rw [hsrc,hdst] at hr
  simpa only [copyProgram,copySlots,List.length_replicate,
    List.append_nil,afterCopy] using hr

theorem balance_run (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input) :
    ∃ u ≤ BalanceOrderCleanup.fullTime (Parameters.scale i),
      ((advance balanceProgram)^[u])
        (⟨some BalanceOrderCleanup.start,bControl,afterCopy S i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,bControl,finalBank S i⟩ := by
  obtain ⟨u,hu,hr⟩ :=
    BalanceOrderCleanup.balance_order_run (Parameters.scale i)
  have hlocal : (fun k : BalanceOrderArithmetic.Stack =>
      (afterCopy S i) (balanceSlots k)) =
      BalanceOrderArithmetic.initial (Parameters.scale i) := by
    funext k
    by_cases hk : k = 0
    · subst k
      change (afterCopy S i) (balance 0) = _
      rw [afterCopy,Function.update_self]
      rfl
    · have hn0 : balanceSlots k ≠ balance 0 := by
        simpa [balanceSlots,balance] using hk
      have hnA : balanceSlots k ≠ writer 54 := by
        simp [balanceSlots,balance,writer]
      change (Function.update
        (Function.update (initialBank S) (writer 54)
          (List.replicate (Parameters.firstExponent i) true))
        (balance 0) (List.replicate (Parameters.scale i) true))
          (balanceSlots k) = _
      rw [Function.update_of_ne hn0,Function.update_of_ne hnA]
      have hblank : (initialBank S) (balanceSlots k) = [] := by
        simp [initialBank,balanceSlots,balance]
      rw [hblank]
      fin_cases k <;> simp_all [BalanceOrderArithmetic.initial]
  have hi : bank balanceSlots (afterCopy S i)
      (BalanceOrderArithmetic.initial (Parameters.scale i)) =
      afterCopy S i :=
    bank_eq_self balanceSlots _ _ (fun k => (congrFun hlocal k).symm)
  have ho : bank balanceSlots (afterCopy S i)
      (BalanceOrderCleanup.finalBank (Parameters.scale i)) =
      finalBank S i := by
    have hf : BalanceOrderCleanup.finalBank (Parameters.scale i) =
        Function.update
          (BalanceOrderArithmetic.initial (Parameters.scale i)) 1
          (List.replicate (Parameters.balanceOrder i) true) := by
      funext k
      fin_cases k <;>
        simp [BalanceOrderCleanup.finalBank,
          BalanceOrderArithmetic.initial,
          Parameters.balanceOrder,Parameters.balanceExponent,
          BalanceOrderArithmetic.exponent]
    rw [hf,← hlocal,bank_update,bank_restrict]
    rfl
  have he := BitMachineStackRun.run balanceSlots (afterCopy S i)
    BalanceOrderCleanup.fullProgram
    (⟨some BalanceOrderCleanup.start,bControl,
      BalanceOrderArithmetic.initial (Parameters.scale i)⟩ :
      TM2.Cfg (fun _ : BalanceOrderArithmetic.Stack => Bool) _ _) u
  have hr0 :
      ((advance BalanceOrderCleanup.fullProgram)^[u])
        (⟨some BalanceOrderCleanup.start,bControl,
          BalanceOrderArithmetic.initial (Parameters.scale i)⟩ :
          TM2.Cfg (fun _ : BalanceOrderArithmetic.Stack => Bool) _ _) =
        ⟨none,bControl,
          BalanceOrderCleanup.finalBank (Parameters.scale i)⟩ := by
    simpa only [bControl,BalanceOrderActualScale.arithmeticControl]
      using hr
  rw [hr0] at he
  refine ⟨u,hu,?_⟩
  simpa only [balanceProgram,stackCfg,hi,ho] using he

theorem run (S : WeightedBinsGraphQ.Stack → List Bool)
    (i : Parameters.Input)
    (hs : S (.inl (.inl (.inr ScaleFinalScratch.answerKey))) =
      List.replicate (Parameters.scale i) true)
    (h54 : S (WeightedBinsGraphQ.writer 54) = []) :
    ∃ u ≤ bound i,
      ((advance program)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel aStart)),
          initialControl,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,initialControl,finalBank S i⟩ ∧
      (finalBank S i) (writer 54) =
        List.replicate (Parameters.firstExponent i) true ∧
      (finalBank S i) (balance 1) =
        List.replicate (Parameters.balanceOrder i) true ∧
      (∀ k : Fin 64, k ≠ 54 →
        (finalBank S i) (writer k) =
          S (WeightedBinsGraphQ.writer k)) := by
  obtain ⟨ua,hua,ha⟩ := a_run S i hs h54
  have hc := copy_run S i hs
  obtain ⟨ub,hub,hb⟩ := balance_run S i
  obtain ⟨u1,hu1,h1⟩ := BitMachineRawSequence.runs
    aProgram copyProgram aStart BitMachineCopy.Label.scan
    aControl aControl (none : Option Bool) none
    (initialBank S) (afterA S i) (afterCopy S i)
    ua (2*Parameters.scale i+2) ha hc
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    phaseProgram balanceProgram
    (BitMachineRawSequence.leftLabel aStart)
    BalanceOrderCleanup.start
    (aControl,(none : Option Bool)) (aControl,(none : Option Bool))
    bControl bControl
    (initialBank S) (afterCopy S i) (finalBank S i)
    u1 ub (by simpa only [phaseProgram] using h1) hb
  refine ⟨u,by dsimp [bound]; omega,?_,?_,?_,?_⟩
  · simpa only [program,initialControl] using hr
  · simp [finalBank,afterCopy,afterA,writer,balance]
  · simp [finalBank,balance]
  · intro k hk
    have hn1 : writer k ≠ balance 1 := by
      simp [writer,balance]
    have hn0 : writer k ≠ balance 0 := by
      simp [writer,balance]
    have hn54 : writer k ≠ writer 54 := by
      simpa [writer,WeightedBinsGraphQ.writer,
        WeightedGraphQJoined.writer] using hk
    rw [finalBank,Function.update_of_ne hn1,
      afterCopy,Function.update_of_ne hn0,
      afterA,Function.update_of_ne hn54]
    rfl

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedScaleDerivedFromBins
