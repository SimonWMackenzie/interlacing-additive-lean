import EthInapproximability.CurrentPaper.WeightedMQJoin
import EthInapproximability.CurrentPaper.BalanceOrderWriterFrame
import EthInapproximability.CurrentPaper.WeightedThresholdArithmetic
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! The same physical bank produces t from raw scale words, m from a and rx,
and stages q,t,m as the threshold machine's three input words. -/

namespace EthInapproximability.CurrentPaper.WeightedThresholdInputJoin

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := BalanceOrderWriterFrame.Stack ⊕ Fin 15
def balanceSlots : BalanceOrderWriterFrame.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def mqSlots : WeightedMWidth.Stack ↪ Stack where
  toFun
    | .inl k => .inl (.inr k)
    | .inr k => .inr k
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · change Sum.inl (Sum.inr a) = Sum.inl (Sum.inr b) at h
      cases h
      rfl
    · cases h
    · cases h
    · change Sum.inr a = Sum.inr b at h
      cases h
      rfl

def writer (k : Fin 64) : Stack := .inl (.inr k)
def scalar (k : Fin 15) : Stack := .inr k
def tSource : Stack := .inl (.inl (.inr 1))
def tScratch : Stack := scalar 11
def tSlots : Fin 3 ↪ Stack :=
  ⟨![tSource,scalar 1,tScratch],by decide⟩

def initialBank (i : Parameters.Input) (W : Fin 64 → List Bool) :
    Stack → List Bool := Sum.elim (BalanceOrderWriterFrame.initialBank i W) (fun _ => [])

def balanceOutcome (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) :
    BalanceOrderWriterFrame.Stack → List Bool :=
  bank BalanceOrderWriterFrame.slots (BalanceOrderWriterFrame.foreign W)
    (Function.update
      (Function.update
        (bank BalanceOrderActualScale.scaleSlots
          BalanceOrderActualScale.foreignBank F)
        (.inr 0) (BalanceOrderArithmetic.unary (Parameters.scale i)))
      (.inr 1) (BalanceOrderArithmetic.unary (Parameters.balanceOrder i)))

def afterBalance (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) : Stack → List Bool :=
  Sum.elim (balanceOutcome i W F) (fun _ => [])

def afterMQ (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (a rx q : ℕ) :
    Stack → List Bool :=
  Function.update
    (Function.update (afterBalance i W F) (scalar 2)
      (List.replicate (Construction.qOne a * rx) true))
    (scalar 0) (List.replicate q true)

def afterT (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (a rx q : ℕ) :
    Stack → List Bool :=
  Function.update (afterMQ i W F a rx q) (scalar 1)
    (List.replicate (Parameters.balanceOrder i) true)

def balanceProgram := fun l => stackStmt balanceSlots (BalanceOrderWriterFrame.program l)
def mqProgram := fun l => stackStmt mqSlots (WeightedMQJoin.program l)
def tProgram := MatrixStage4ScalarPreparationOps.copyProgram tSlots

theorem balance_run (i : Parameters.Input) (W : Fin 64 → List Bool) :
    ∃ u ≤ BalanceOrderActualScale.totalBound i,
      ∃ F : ETHScaleActualComplete.Stack → List Bool,
        ((advance balanceProgram)^[u])
          (⟨some BalanceOrderActualScale.start,
            ((BalanceOrderActualScale.scaleControl,none),
              BalanceOrderActualScale.arithmeticControl),
            initialBank i W⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,
            ((BalanceOrderActualScale.scaleControl,none),
              BalanceOrderActualScale.arithmeticControl),
            afterBalance i W F⟩ ∧
        (∀ k : Fin 64, (afterBalance i W F) (writer k) = W k) ∧
        (afterBalance i W F) tSource =
          List.replicate (Parameters.balanceOrder i) true := by
  obtain ⟨u,hu,F,hr,_,_,hwriter⟩ := BalanceOrderWriterFrame.writer_framed_run i W
  let B := initialBank i W
  have he := BitMachineStackRun.run balanceSlots B
    BalanceOrderWriterFrame.program
    (⟨some BalanceOrderActualScale.start,
      ((BalanceOrderActualScale.scaleControl,none),
        BalanceOrderActualScale.arithmeticControl),
      BalanceOrderWriterFrame.initialBank i W⟩ :
      TM2.Cfg (fun _ : BalanceOrderWriterFrame.Stack => Bool) _ _) u
  rw [hr] at he
  have hi : bank balanceSlots B (BalanceOrderWriterFrame.initialBank i W) = B := by
    apply bank_eq_self
    intro k
    rfl
  have ho : bank balanceSlots B (balanceOutcome i W F) =
      afterBalance i W F := by
    funext k
    cases k with
    | inl k => exact bank_at balanceSlots B (balanceOutcome i W F) k
    | inr k =>
        rw [bank_outside]
        · rfl
        · rintro ⟨j,h⟩; cases h
  refine ⟨u,hu,F,?_,?_,?_⟩
  · dsimp only [stackCfg] at he
    rw [hi] at he
    change ((advance balanceProgram)^[u]) _ =
      ⟨none,((BalanceOrderActualScale.scaleControl,none),
        BalanceOrderActualScale.arithmeticControl),
        bank balanceSlots B (balanceOutcome i W F)⟩ at he
    rw [ho] at he
    exact he
  · intro k
    exact hwriter k
  · change (balanceOutcome i W F) (.inl (.inr 1)) = _
    unfold balanceOutcome
    change bank BalanceOrderWriterFrame.slots (BalanceOrderWriterFrame.foreign W) _
      (BalanceOrderWriterFrame.slots (.inr (1 : Fin 13))) = _
    rw [bank_at]
    simp

theorem afterBalance_blank (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (j : Fin 15) :
    afterBalance i W F (scalar j) = [] := rfl

theorem mq_run (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (a rx q : ℕ)
    (ha : W 54 = List.replicate a true)
    (hrx : W 17 = List.replicate rx true)
    (hq : W 56 = List.replicate q true) :
    ∃ u ≤ WeightedMQJoin.cost a rx q,
      ((advance mqProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel (Sum.inr false))))),
          WeightedMQJoin.initial,afterBalance i W F⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedMQJoin.initial,afterMQ i W F a rx q⟩ := by
  let B := afterBalance i W F
  let S : WeightedMWidth.Stack → List Bool := fun j => B (mqSlots j)
  have hw (k : Fin 64) : S (WeightedMWidth.writer k) = W k := by
    change B (writer k) = W k
    simp [B,afterBalance,balanceOutcome,writer,
      BalanceOrderWriterFrame.slots,bank_outside,
      BalanceOrderWriterFrame.foreign]
  obtain ⟨u,hu,hr⟩ := WeightedMQJoin.run S a rx q
    (by simpa [hw] using ha)
    (by simpa [hw] using hrx)
    (by simpa [hw] using hq)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have he := BitMachineStackRun.run mqSlots B WeightedMQJoin.program
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (Sum.inr false))))),
      WeightedMQJoin.initial,S⟩ :
      TM2.Cfg (fun _ : WeightedMWidth.Stack => Bool) _ _) u
  rw [hr] at he
  have hi : bank mqSlots B S = B := by
    apply bank_eq_self
    intro k
    rfl
  have ho : bank mqSlots B
      (Function.update
        (Function.update S (WeightedMWidth.scalar 2)
          (List.replicate (Construction.qOne a * rx) true))
        (WeightedMWidth.scalar 0) (List.replicate q true)) =
      afterMQ i W F a rx q := by
    rw [bank_update,bank_update,hi]
    rfl
  refine ⟨u,hu,?_⟩
  simpa only [mqProgram,stackCfg,hi,ho,B] using he

theorem t_run (i : Parameters.Input) (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (a rx q : ℕ) :
    ((advance tProgram)^[2*Parameters.balanceOrder i+2])
      (⟨some .scan,none,afterMQ i W F a rx q⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,afterT i W F a rx q⟩ := by
  have hs : (afterMQ i W F a rx q) tSource =
      List.replicate (Parameters.balanceOrder i) true := by
    have ht : (afterBalance i W F) tSource =
        List.replicate (Parameters.balanceOrder i) true := by
      change (balanceOutcome i W F) (.inl (.inr 1)) = _
      unfold balanceOutcome
      change bank BalanceOrderWriterFrame.slots (BalanceOrderWriterFrame.foreign W) _
        (BalanceOrderWriterFrame.slots (.inr (1 : Fin 13))) = _
      rw [bank_at]
      simp
    simpa only [afterMQ,Function.update_apply] using ht
  have h1 : (afterMQ i W F a rx q) (scalar 1) = [] := by
    simp only [afterMQ,Function.update_apply]
    exact afterBalance_blank i W F 1
  have h11 : (afterMQ i W F a rx q) tScratch = [] := by
    simp only [afterMQ,Function.update_apply]
    exact afterBalance_blank i W F 11
  have hr := MatrixStage4ScalarPreparationOps.copy_run tSlots
    (afterMQ i W F a rx q) h11
  simpa [tProgram,tSlots,hs,h1,afterT] using hr

/-- Exact whole Fin15 handoff, not merely the three displayed cells. -/
theorem threshold_input_bank (i : Parameters.Input)
    (W : Fin 64 → List Bool)
    (F : ETHScaleActualComplete.Stack → List Bool) (a rx q : ℕ) :
    (fun j : Fin 15 => (afterT i W F a rx q) (scalar j)) =
      Paper2.WeightedThresholdArithmetic.initial q (Parameters.balanceOrder i)
        (Construction.qOne a * rx) := by
  funext j
  fin_cases j <;>
    simp [afterT,afterMQ,scalar,
      Paper2.WeightedThresholdArithmetic.initial,
      Paper2.WeightedThresholdArithmetic.unary] <;> rfl

def balanceStart := BalanceOrderActualScale.start
def balanceControl :
    (ETHScaleActualComplete.Control × Option Bool) ×
      BalanceOrderActualScale.ArithmeticControl :=
  ((BalanceOrderActualScale.scaleControl,none),
    BalanceOrderActualScale.arithmeticControl)
def mqStart := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label)
  (BitMachineRawSequence.leftLabel (LB := WeightedMMultiply.ClearLabel)
    (BitMachineRawSequence.leftLabel (LB := MatrixAddressMachine.Label)
      (BitMachineRawSequence.leftLabel (LB := Unit)
        (Sum.inr false : MatrixUnaryPower.Label))))
def phaseProgram := BitMachineRawSequence.program
  balanceProgram mqProgram mqStart balanceControl WeightedMQJoin.initial
def program := BitMachineRawSequence.program
  phaseProgram tProgram BitMachineCopy.Label.scan
  (balanceControl,WeightedMQJoin.initial) (none : Option Bool)
def initialControl := ((balanceControl,WeightedMQJoin.initial),(none : Option Bool))
def cost (i : Parameters.Input) (a rx q : ℕ) : ℕ :=
  BalanceOrderActualScale.totalBound i + WeightedMQJoin.cost a rx q +
    (2*Parameters.balanceOrder i+2) + 2

/-- One fixed physical controller: raw-six balance-order production, exact
qOne*rx multiplication and q transfer, then source-preserving t transfer. -/
theorem run (i : Parameters.Input) (W : Fin 64 → List Bool)
    (a rx q : ℕ)
    (ha : W 54 = List.replicate a true)
    (hrx : W 17 = List.replicate rx true)
    (hq : W 56 = List.replicate q true) :
    ∃ u ≤ cost i a rx q,
      ∃ F : ETHScaleActualComplete.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel balanceStart)),
            initialControl,initialBank i W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,afterT i W F a rx q⟩ ∧
        (afterT i W F a rx q) (scalar 0) = List.replicate q true ∧
        (afterT i W F a rx q) (scalar 1) =
          List.replicate (Parameters.balanceOrder i) true ∧
        (afterT i W F a rx q) (scalar 2) =
          List.replicate (Construction.qOne a * rx) true ∧
        (∀ k : Fin 64, (afterT i W F a rx q) (writer k) = W k) := by
  obtain ⟨tb,htb,F,hb,hw,ht⟩ := balance_run i W
  obtain ⟨tm,htm,hm⟩ := mq_run i W F a rx q ha hrx hq
  have hc := t_run i W F a rx q
  obtain ⟨t12,h12,h12r⟩ := BitMachineRawSequence.runs
    balanceProgram mqProgram balanceStart mqStart
    balanceControl balanceControl WeightedMQJoin.initial WeightedMQJoin.initial
    (initialBank i W) (afterBalance i W F) (afterMQ i W F a rx q)
    tb tm
    (by simpa only [balanceStart,balanceControl] using hb)
    (by simpa only [mqStart] using hm)
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    phaseProgram tProgram (BitMachineRawSequence.leftLabel balanceStart)
    BitMachineCopy.Label.scan
    (balanceControl,WeightedMQJoin.initial)
    (balanceControl,WeightedMQJoin.initial)
    (none : Option Bool) none
    (initialBank i W) (afterMQ i W F a rx q) (afterT i W F a rx q)
    t12 (2*Parameters.balanceOrder i+2)
    (by simpa only [phaseProgram] using h12r) hc
  refine ⟨u,by dsimp [cost]; omega,F,?_,?_,?_,?_,?_⟩
  · simpa only [program,initialControl] using hr
  · simp [afterT,afterMQ,scalar]
  · simp [afterT,scalar]
  · simp [afterT,afterMQ,scalar]
  · intro k
    simpa [afterT,afterMQ,writer,scalar] using hw k

#print axioms balance_run
#print axioms mq_run
#print axioms t_run
#print axioms threshold_input_bank
#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedThresholdInputJoin
