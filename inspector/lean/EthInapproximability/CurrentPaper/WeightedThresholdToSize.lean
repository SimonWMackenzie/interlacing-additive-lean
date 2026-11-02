import EthInapproximability.CurrentPaper.WeightedThresholdInputJoin
import EthInapproximability.CurrentPaper.ChosenSizeArbitraryWriter
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! Actual threshold arithmetic and prime/size producer on a shared writer
bank, with q/t/m supplied only as reached words from the preceding machine. -/

namespace EthInapproximability.CurrentPaper.WeightedThresholdToSize

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedThresholdInputJoin.Stack ⊕
  (ChosenPrimeRaw.Stack ⊕ Fin 8)

def upstreamSlots : WeightedThresholdInputJoin.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def thresholdSlots : Fin 15 ↪ Stack :=
  ⟨fun j => .inl (WeightedThresholdInputJoin.scalar j),by
    intro a b h
    cases h
    rfl⟩
def suffixSlots : ChosenSizeArbitraryWriter.Stack ↪ Stack where
  toFun
    | .inl j => .inr (.inl j)
    | .inr (.inl k) => .inl (WeightedThresholdInputJoin.writer k)
    | .inr (.inr j) => .inr (.inr j)
  inj' := by
    intro a b h
    rcases a with a | (a | a) <;>
      rcases b with b | (b | b) <;>
      simp [WeightedThresholdInputJoin.writer] at h ⊢ <;> assumption

def writer (k : Fin 64) : Stack :=
  .inl (WeightedThresholdInputJoin.writer k)
def scalar (j : Fin 15) : Stack :=
  .inl (WeightedThresholdInputJoin.scalar j)
def searchInput : Stack := .inr (.inl (.inr 0))
def extraT : Stack := .inr (.inr 0)
def scratch : Stack := scalar 14
def xCopySlots : Fin 3 ↪ Stack :=
  ⟨![scalar 8,searchInput,scratch],by decide⟩
def tCopySlots : Fin 3 ↪ Stack :=
  ⟨![scalar 1,extraT,scratch],by decide⟩

def initialBank (S : WeightedThresholdInputJoin.Stack → List Bool) :
    Stack → List Bool := Sum.elim S (fun _ => [])
def afterThreshold (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ) : Stack → List Bool :=
  bank thresholdSlots (initialBank S)
    (Paper2.WeightedThresholdArithmetic.finalBank q t m)
def afterXCopy (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ) : Stack → List Bool :=
  Function.update (afterThreshold S q t m) searchInput
    (List.replicate (PrimeSampler.threshold q t m) true)
def afterTCopy (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ) : Stack → List Bool :=
  Function.update (afterXCopy S q t m) extraT (List.replicate t true)

def thresholdProgram := fun l => stackStmt thresholdSlots
  (Paper2.WeightedThresholdArithmetic.program l)
def xCopyProgram := MatrixStage4ScalarPreparationOps.copyProgram xCopySlots
def tCopyProgram := MatrixStage4ScalarPreparationOps.copyProgram tCopySlots
def suffixProgram := fun l => stackStmt suffixSlots
  (ChosenSizeArbitraryWriter.program l)

theorem threshold_run (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ)
    (hinit : (fun j : Fin 15 => S (WeightedThresholdInputJoin.scalar j)) =
      Paper2.WeightedThresholdArithmetic.initial q t m) :
    ∃ u ≤ 20000*(Paper2.WeightedThresholdArithmetic.size q t m)^3 +
      100*Paper2.WeightedThresholdArithmetic.size q t m+20000,
      ((advance thresholdProgram)^[u])
        (⟨some Paper2.WeightedThresholdArithmetic.start,
          Paper2.WeightedThresholdArithmetic.controlFinal,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,Paper2.WeightedThresholdArithmetic.controlFinal,
          afterThreshold S q t m⟩ := by
  obtain ⟨u,hu,hr⟩ := Paper2.WeightedThresholdArithmetic.threshold_run_polynomial q t m
  let B := initialBank S
  have he := BitMachineStackRun.run thresholdSlots B
    Paper2.WeightedThresholdArithmetic.program
    (⟨some Paper2.WeightedThresholdArithmetic.start,
      Paper2.WeightedThresholdArithmetic.controlFinal,
      Paper2.WeightedThresholdArithmetic.initial q t m⟩ :
      TM2.Cfg (fun _ : Fin 15 => Bool) _ _) u
  rw [hr] at he
  have hi : bank thresholdSlots B
      (Paper2.WeightedThresholdArithmetic.initial q t m) = B := by
    apply bank_eq_self
    intro j
    exact (congrFun hinit j).symm
  refine ⟨u,hu,?_⟩
  simpa only [thresholdProgram,stackCfg,hi,afterThreshold,B] using he

theorem x_copy_run (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ) :
    ((advance xCopyProgram)^[2*PrimeSampler.threshold q t m+2])
      (⟨some .scan,none,afterThreshold S q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterXCopy S q t m⟩ := by
  have hs : (afterThreshold S q t m) (scalar 8) =
      List.replicate (PrimeSampler.threshold q t m) true := by
    change bank thresholdSlots (initialBank S) _ (thresholdSlots 8) = _
    rw [bank_at]
    simp [Paper2.WeightedThresholdArithmetic.finalBank,
      Paper2.WeightedThresholdArithmetic.unary]
  have hb : (afterThreshold S q t m) scratch = [] := by
    change bank thresholdSlots (initialBank S) _ (thresholdSlots 14) = []
    rw [bank_at]
    simp [Paper2.WeightedThresholdArithmetic.finalBank]
  have hd : (afterThreshold S q t m) searchInput = [] := by
    have hout : ¬ ∃ j : Fin 15, thresholdSlots j = searchInput := by
      rintro ⟨j,h⟩; cases h
    rw [afterThreshold,bank_outside _ _ _ _ hout]
    rfl
  have hr := MatrixStage4ScalarPreparationOps.copy_run xCopySlots
    (afterThreshold S q t m) (by simpa [xCopySlots] using hb)
  simpa [xCopyProgram,xCopySlots,afterXCopy,hs,hd] using hr

theorem t_copy_run (S : WeightedThresholdInputJoin.Stack → List Bool)
    (q t m : ℕ) :
    ((advance tCopyProgram)^[2*t+2])
      (⟨some .scan,none,afterXCopy S q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterTCopy S q t m⟩ := by
  have hs : (afterXCopy S q t m) (scalar 1) = List.replicate t true := by
    rw [afterXCopy,Function.update_of_ne (by decide : scalar 1 ≠ searchInput)]
    change bank thresholdSlots (initialBank S) _ (thresholdSlots 1) = _
    rw [bank_at]
    simp [Paper2.WeightedThresholdArithmetic.finalBank,
      Paper2.WeightedThresholdArithmetic.unary]
  have hb : (afterXCopy S q t m) scratch = [] := by
    rw [afterXCopy,Function.update_of_ne (by decide : scratch ≠ searchInput)]
    change bank thresholdSlots (initialBank S) _ (thresholdSlots 14) = []
    rw [bank_at]
    simp [Paper2.WeightedThresholdArithmetic.finalBank]
  have hd : (afterXCopy S q t m) extraT = [] := by
    rw [afterXCopy,Function.update_of_ne (by decide : extraT ≠ searchInput)]
    have hout : ¬ ∃ j : Fin 15, thresholdSlots j = extraT := by
      rintro ⟨j,h⟩; cases h
    rw [afterThreshold,bank_outside _ _ _ _ hout]
    rfl
  have hr := MatrixStage4ScalarPreparationOps.copy_run tCopySlots
    (afterXCopy S q t m) (by simpa [tCopySlots] using hb)
  simpa [tCopyProgram,tCopySlots,afterTCopy,hs,hd] using hr

private theorem search_initial_cells (X : ℕ)
    (j : ChosenPrimeRaw.Stack) :
    (ChosenPrimeRaw.initial X).stk j =
      if j = (.inr 0 : ChosenPrimeRaw.Stack) then
        List.replicate X true else [] := by
  cases j with
  | inl j =>
      simp [ChosenPrimeRaw.initial,PrimeSamplerSearch.adminCfg,
        PrimeSamplerSearch.cfg]
  | inr j =>
      fin_cases j <;>
        simp [ChosenPrimeRaw.initial,PrimeSamplerSearch.adminCfg,
          PrimeSamplerSearch.cfg,PrimeSamplerSearch.foreign]

private theorem afterTCopy_suffix_ready
    (S : WeightedThresholdInputJoin.Stack → List Bool)
    (W : Fin 64 → List Bool) (q t m : ℕ)
    (hW : ∀ k : Fin 64, S (WeightedThresholdInputJoin.writer k) = W k) :
    (fun j : ChosenSizeArbitraryWriter.Stack =>
      (afterTCopy S q t m) (suffixSlots j)) =
      ChosenSizeArbitraryWriter.initialBank W q t m := by
  funext j
  cases j with
  | inl j =>
      cases j with
      | inl tester =>
          have hout : ¬ ∃ l : Fin 15,
              thresholdSlots l = suffixSlots (.inl (.inl tester)) := by
            rintro ⟨l,h⟩; cases h
          have hnT : suffixSlots (.inl (.inl tester)) ≠ extraT := by
            simp [suffixSlots,extraT]
          have hnX : suffixSlots (.inl (.inl tester)) ≠ searchInput := by
            simp [suffixSlots,searchInput]
          change (afterTCopy S q t m) (suffixSlots (.inl (.inl tester))) =
            (ChosenSizeArbitraryWriter.initialBank W q t m)
              (ChosenSizeArbitraryWriter.searchSlots (.inl tester))
          rw [afterTCopy,Function.update_of_ne hnT,afterXCopy,
            Function.update_of_ne hnX,afterThreshold,
            bank_outside _ _ _ _ hout,
            ChosenSizeArbitraryWriter.initialBank,bank_at,
            search_initial_cells]
          simp [initialBank,suffixSlots]
      | inr k =>
          by_cases hk : k = 0
          · subst k
            change (afterTCopy S q t m) searchInput =
              (ChosenSizeArbitraryWriter.initialBank W q t m)
                (ChosenSizeArbitraryWriter.searchSlots (.inr 0))
            simp [afterTCopy,afterXCopy,extraT,searchInput,
              ChosenSizeArbitraryWriter.initialBank,bank_at,
              search_initial_cells]
          ·
              have hout : ¬ ∃ l : Fin 15,
                  thresholdSlots l = suffixSlots (.inl (.inr k)) := by
                rintro ⟨l,h⟩; cases h
              have hnT : suffixSlots (.inl (.inr k)) ≠ extraT := by
                simp [suffixSlots,extraT]
              have hnX : suffixSlots (.inl (.inr k)) ≠ searchInput := by
                simpa [suffixSlots,searchInput] using hk
              change (afterTCopy S q t m) (suffixSlots (.inl (.inr k))) =
                (ChosenSizeArbitraryWriter.initialBank W q t m)
                  (ChosenSizeArbitraryWriter.searchSlots (.inr k))
              rw [afterTCopy,Function.update_of_ne hnT,afterXCopy,
                Function.update_of_ne hnX,afterThreshold,
                bank_outside _ _ _ _ hout,
                ChosenSizeArbitraryWriter.initialBank,bank_at,
                search_initial_cells]
              simp [hk,initialBank,suffixSlots]
  | inr j =>
      cases j with
      | inl k =>
          have hout : ¬ ∃ l : Fin 15, thresholdSlots l = writer k := by
            rintro ⟨l,h⟩; cases h
          have hout' : ¬ ∃ l : ChosenPrimeRaw.Stack,
              ChosenSizeArbitraryWriter.searchSlots l =
                ChosenSizeArbitraryWriter.writer k := by
            rintro ⟨l,h⟩; cases h
          have hnT : writer k ≠ extraT := by simp [writer,extraT]
          have hnX : writer k ≠ searchInput := by simp [writer,searchInput]
          change (afterTCopy S q t m) (writer k) =
            (ChosenSizeArbitraryWriter.initialBank W q t m)
              (ChosenSizeArbitraryWriter.writer k)
          rw [afterTCopy,Function.update_of_ne hnT,afterXCopy,
            Function.update_of_ne hnX,afterThreshold,
            bank_outside _ _ _ _ hout,
            ChosenSizeArbitraryWriter.initialBank,
            bank_outside _ _ _ _ hout']
          simpa [initialBank,ChosenSizeArbitraryWriter.foreignBank,writer]
            using hW k
      | inr k =>
          by_cases hk : k = 0
          · subst k
            change (afterTCopy S q t m) extraT =
              (ChosenSizeArbitraryWriter.initialBank W q t m)
                (.inr (.inr 0))
            simp only [afterTCopy,Function.update_self]
            have hout' : ¬ ∃ l : ChosenPrimeRaw.Stack,
                ChosenSizeArbitraryWriter.searchSlots l = (.inr (.inr 0)) := by
              rintro ⟨l,h⟩; cases h
            rw [ChosenSizeArbitraryWriter.initialBank,
              bank_outside _ _ _ _ hout']
            rfl
          ·
              have hout : ¬ ∃ l : Fin 15,
                  thresholdSlots l = suffixSlots (.inr (.inr k)) := by
                rintro ⟨l,h⟩; cases h
              have hout' : ¬ ∃ l : ChosenPrimeRaw.Stack,
                  ChosenSizeArbitraryWriter.searchSlots l = (.inr (.inr k)) := by
                rintro ⟨l,h⟩; cases h
              have hnT : suffixSlots (.inr (.inr k)) ≠ extraT := by
                simpa [suffixSlots,extraT] using hk
              have hnX : suffixSlots (.inr (.inr k)) ≠ searchInput := by
                simp [suffixSlots,searchInput]
              change (afterTCopy S q t m) (suffixSlots (.inr (.inr k))) =
                (ChosenSizeArbitraryWriter.initialBank W q t m)
                  (.inr (.inr k))
              rw [afterTCopy,Function.update_of_ne hnT,afterXCopy,
                Function.update_of_ne hnX,afterThreshold,
                bank_outside _ _ _ _ hout,
                ChosenSizeArbitraryWriter.initialBank,
                bank_outside _ _ _ _ hout']
              simp [initialBank,suffixSlots,
                ChosenSizeArbitraryWriter.foreignBank,hk]

def finalBank (S : WeightedThresholdInputJoin.Stack → List Bool)
    (W : Fin 64 → List Bool) (q t m : ℕ)
    (F : ChosenPrimeRaw.Stack → List Bool) :
    Stack → List Bool :=
  bank suffixSlots (afterTCopy S q t m)
    (Function.update
      (bank ChosenSizeArbitraryWriter.searchSlots
        (ChosenSizeArbitraryWriter.foreignBank W t) F)
      ChosenSizeSuffix.writerL
      (List.replicate (PrimeSampler.size q t m) true))

theorem suffix_run (S : WeightedThresholdInputJoin.Stack → List Bool)
    (W : Fin 64 → List Bool) (q t m : ℕ)
    (hW : ∀ k : Fin 64, S (WeightedThresholdInputJoin.writer k) = W k)
    (h57 : W 57 = []) :
    ∃ u ≤ ChosenSizeArbitraryWriter.bound q t m,
      ∃ F : ChosenPrimeRaw.Stack → List Bool,
        ((advance suffixProgram)^[u])
          (⟨some ChosenSizeArbitraryWriter.start,
            ChosenSizeArbitraryWriter.initialControl,
            afterTCopy S q t m⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,ChosenSizeArbitraryWriter.initialControl,
            finalBank S W q t m F⟩ ∧
        (∀ k : Fin 64,
          (finalBank S W q t m F) (writer k) =
            Function.update W 57
              (List.replicate (PrimeSampler.size q t m) true) k) := by
  obtain ⟨u,hu,F,hr,_,hwriter⟩ :=
    ChosenSizeArbitraryWriter.run W q t m h57
  let B := afterTCopy S q t m
  have he := BitMachineStackRun.run suffixSlots B
    ChosenSizeArbitraryWriter.program
    (⟨some ChosenSizeArbitraryWriter.start,
      ChosenSizeArbitraryWriter.initialControl,
      ChosenSizeArbitraryWriter.initialBank W q t m⟩ :
      TM2.Cfg (fun _ : ChosenSizeArbitraryWriter.Stack => Bool) _ _) u
  rw [hr] at he
  have hi : bank suffixSlots B
      (ChosenSizeArbitraryWriter.initialBank W q t m) = B := by
    apply bank_eq_self
    intro j
    exact (congrFun (afterTCopy_suffix_ready S W q t m hW) j).symm
  refine ⟨u,hu,F,?_,?_⟩
  · simpa only [suffixProgram,stackCfg,hi,finalBank,B] using he
  · intro k
    change (bank suffixSlots B _) (suffixSlots
      (ChosenSizeArbitraryWriter.writer k)) = _
    rw [bank_at]
    exact congrFun hwriter k

def thresholdStart := Paper2.WeightedThresholdArithmetic.start
def thresholdControl := Paper2.WeightedThresholdArithmetic.controlFinal
def prefixProgram := BitMachineRawSequence.program
  thresholdProgram xCopyProgram BitMachineCopy.Label.scan
  thresholdControl (none : Option Bool)
def copyProgram := BitMachineRawSequence.program
  prefixProgram tCopyProgram BitMachineCopy.Label.scan
  (thresholdControl,(none : Option Bool)) (none : Option Bool)
def program := BitMachineRawSequence.program
  copyProgram suffixProgram ChosenSizeArbitraryWriter.start
  ((thresholdControl,(none : Option Bool)),(none : Option Bool))
  ChosenSizeArbitraryWriter.initialControl
def initialControl :=
  (((thresholdControl,(none : Option Bool)),(none : Option Bool)),
    ChosenSizeArbitraryWriter.initialControl)
def bound (q t m : ℕ) : ℕ :=
  20000*(Paper2.WeightedThresholdArithmetic.size q t m)^3 +
  100*Paper2.WeightedThresholdArithmetic.size q t m+20000 +
  (2*PrimeSampler.threshold q t m+2) + (2*t+2) +
  ChosenSizeArbitraryWriter.bound q t m + 3

/-- One fixed controller from already staged q/t/m to chosen size at writer57.
The arbitrary writer is retained, except for that one output cell. -/
theorem run (S : WeightedThresholdInputJoin.Stack → List Bool)
    (W : Fin 64 → List Bool) (q t m : ℕ)
    (hinit : (fun j : Fin 15 => S (WeightedThresholdInputJoin.scalar j)) =
      Paper2.WeightedThresholdArithmetic.initial q t m)
    (hW : ∀ k : Fin 64, S (WeightedThresholdInputJoin.writer k) = W k)
    (h57 : W 57 = []) :
    ∃ u ≤ bound q t m,
      ∃ F : ChosenPrimeRaw.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel thresholdStart))),
            initialControl,initialBank S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,finalBank S W q t m F⟩ ∧
        (∀ k : Fin 64,
          (finalBank S W q t m F) (writer k) =
            Function.update W 57
              (List.replicate (PrimeSampler.size q t m) true) k) := by
  obtain ⟨ut,hut,ht⟩ := threshold_run S q t m hinit
  have hx := x_copy_run S q t m
  have hc := t_copy_run S q t m
  obtain ⟨us,hus,F,hs,hw⟩ := suffix_run S W q t m hW h57
  obtain ⟨u1,hu1,h1⟩ := BitMachineRawSequence.runs
    thresholdProgram xCopyProgram thresholdStart BitMachineCopy.Label.scan
    thresholdControl thresholdControl (none : Option Bool) none
    (initialBank S) (afterThreshold S q t m) (afterXCopy S q t m)
    ut (2*PrimeSampler.threshold q t m+2)
    (by simpa only [thresholdStart,thresholdControl] using ht) hx
  obtain ⟨u2,hu2,h2⟩ := BitMachineRawSequence.runs
    prefixProgram tCopyProgram
    (BitMachineRawSequence.leftLabel thresholdStart)
    BitMachineCopy.Label.scan
    (thresholdControl,(none : Option Bool))
    (thresholdControl,(none : Option Bool)) (none : Option Bool) none
    (initialBank S) (afterXCopy S q t m) (afterTCopy S q t m)
    u1 (2*t+2)
    (by simpa only [prefixProgram] using h1) hc
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    copyProgram suffixProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel thresholdStart))
    ChosenSizeArbitraryWriter.start
    ((thresholdControl,(none : Option Bool)),(none : Option Bool))
    ((thresholdControl,(none : Option Bool)),(none : Option Bool))
    ChosenSizeArbitraryWriter.initialControl
    ChosenSizeArbitraryWriter.initialControl
    (initialBank S) (afterTCopy S q t m) (finalBank S W q t m F)
    u2 us (by simpa only [copyProgram] using h2)
    (by simpa only [suffixProgram] using hs)
  refine ⟨u,by dsimp [bound]; omega,F,?_,hw⟩
  simpa only [program,initialControl] using hr

#print axioms threshold_run
#print axioms x_copy_run
#print axioms t_copy_run
#print axioms suffix_run
#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedThresholdToSize
