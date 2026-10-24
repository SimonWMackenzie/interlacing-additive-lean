import EthInapproximability.CurrentPaper.WeightedPrefixAT
import EthInapproximability.CurrentPaper.WeightedMQJoin
import EthInapproximability.CurrentPaper.WeightedThresholdArithmetic
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! The reached a/q writer words and balance-order t word are physically
staged as the exact q/t/m threshold input; m is computed from a and rx. -/

namespace EthInapproximability.CurrentPaper.WeightedMTPrefix

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedPrefixAT.Stack ⊕ Fin 15
noncomputable instance : DecidableEq Stack := Classical.decEq _
def prefixSlots : WeightedPrefixAT.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def writer (k : Fin 64) : Stack := .inl (WeightedPrefixAT.writer k)
def tSource : Stack :=
  .inl (WeightedScaleDerivedFromBins.balance 1)
def scalar (j : Fin 15) : Stack := .inr j
def mqSlots : WeightedMWidth.Stack ↪ Stack where
  toFun
    | .inl k => writer k
    | .inr j => scalar j
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · simp [writer,WeightedPrefixAT.writer,
        WeightedScaleDerivedFromBins.writer,
        WeightedBinsGraphQ.writer,WeightedGraphQJoined.writer] at h
      cases h
      rfl
    · cases h
    · cases h
    · cases h; rfl
def tSlots : Fin 3 ↪ Stack :=
  ⟨![tSource,scalar 1,scalar 11],by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [tSource,scalar] at h ⊢⟩
def initialBank (S : WeightedPrefixAT.Stack → List Bool) :
    Stack → List Bool := Sum.elim S (fun _ => [])
def afterMQ (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q : ℕ) : Stack → List Bool :=
  Function.update
    (Function.update (initialBank S) (scalar 2)
      (List.replicate (Construction.qOne a * rx) true))
    (scalar 0) (List.replicate q true)
def finalBank (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ) : Stack → List Bool :=
  Function.update (afterMQ S a rx q) (scalar 1)
    (List.replicate t true)
def mqProgram := fun l => stackStmt mqSlots (WeightedMQJoin.program l)
def tProgram := MatrixStage4ScalarPreparationOps.copyProgram tSlots
def program := BitMachineRawSequence.program mqProgram tProgram
  BitMachineCopy.Label.scan WeightedMQJoin.initial (none : Option Bool)
def initialControl := (WeightedMQJoin.initial,(none : Option Bool))
def bound (a rx q t : ℕ) : ℕ :=
  WeightedMQJoin.cost a rx q + (2*t+2) + 1

theorem mq_run (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q : ℕ)
    (ha : S (WeightedPrefixAT.writer 54) = List.replicate a true)
    (hrx : S (WeightedPrefixAT.writer 17) = List.replicate rx true)
    (hq : S (WeightedPrefixAT.writer 56) = List.replicate q true) :
    ∃ u ≤ WeightedMQJoin.cost a rx q,
      ((advance mqProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (Sum.inr false))))),
          WeightedMQJoin.initial,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedMQJoin.initial,afterMQ S a rx q⟩ := by
  let B := initialBank S
  let T : WeightedMWidth.Stack → List Bool := fun j => B (mqSlots j)
  have hwriter (k : Fin 64) : T (WeightedMWidth.writer k) =
      S (WeightedPrefixAT.writer k) := rfl
  obtain ⟨u,hu,hr⟩ := WeightedMQJoin.run T a rx q
    (by simpa [hwriter] using ha)
    (by simpa [hwriter] using hrx)
    (by simpa [hwriter] using hq)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl)
  have he := BitMachineStackRun.run mqSlots B
    WeightedMQJoin.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (Sum.inr false))))),
      WeightedMQJoin.initial,T⟩ :
      TM2.Cfg (fun _ : WeightedMWidth.Stack => Bool) _ _) u
  rw [hr] at he
  have hi : bank mqSlots B T = B :=
    bank_eq_self mqSlots B T (fun _ => rfl)
  have ho : bank mqSlots B
      (Function.update
        (Function.update T (WeightedMWidth.scalar 2)
          (List.replicate (Construction.qOne a * rx) true))
        (WeightedMWidth.scalar 0) (List.replicate q true)) =
      afterMQ S a rx q := by
    rw [bank_update,bank_update,hi]
    rfl
  refine ⟨u,hu,?_⟩
  simpa only [mqProgram,stackCfg,hi,ho,B] using he

theorem t_run (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ)
    (ht : S (WeightedScaleDerivedFromBins.balance 1) =
      List.replicate t true) :
    ((advance tProgram)^[2*t+2])
      (⟨some BitMachineCopy.Label.scan,none,afterMQ S a rx q⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,finalBank S a rx q t⟩ := by
  have hs : (afterMQ S a rx q) tSource = List.replicate t true := by
    have hn0 : tSource ≠ scalar 0 := by simp [tSource,scalar]
    have hn2 : tSource ≠ scalar 2 := by simp [tSource,scalar]
    rw [afterMQ,Function.update_of_ne hn0,
      Function.update_of_ne hn2]
    exact ht
  have hd : (afterMQ S a rx q) (scalar 1) = [] := by
    have hn0 : scalar 1 ≠ scalar 0 := by simp [scalar]
    have hn2 : scalar 1 ≠ scalar 2 := by simp [scalar]
    rw [afterMQ,Function.update_of_ne hn0,
      Function.update_of_ne hn2]
    rfl
  have hc : (afterMQ S a rx q) (scalar 11) = [] := by
    have hn0 : scalar 11 ≠ scalar 0 := by simp [scalar]
    have hn2 : scalar 11 ≠ scalar 2 := by simp [scalar]
    rw [afterMQ,Function.update_of_ne hn0,
      Function.update_of_ne hn2]
    rfl
  have hr := MatrixStage4ScalarPreparationOps.copy_run tSlots
    (afterMQ S a rx q) hc
  change (afterMQ S a rx q) (tSlots 0) = _ at hs
  change (afterMQ S a rx q) (tSlots 1) = _ at hd
  rw [hs,hd] at hr
  simpa only [tProgram,tSlots,List.length_replicate,
    List.append_nil,finalBank] using hr

theorem threshold_input (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ) :
    (fun j : Fin 15 => (finalBank S a rx q t) (scalar j)) =
      Paper2.WeightedThresholdArithmetic.initial q t
        (Construction.qOne a * rx) := by
  funext j
  fin_cases j <;>
    simp [finalBank,afterMQ,scalar,
      Paper2.WeightedThresholdArithmetic.initial,
      Paper2.WeightedThresholdArithmetic.unary] <;> rfl

theorem writer_frame (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ) (k : Fin 64) :
    (finalBank S a rx q t) (writer k) =
      S (WeightedPrefixAT.writer k) := by
  have hn1 : writer k ≠ scalar 1 := by simp [writer,scalar]
  have hn0 : writer k ≠ scalar 0 := by simp [writer,scalar]
  have hn2 : writer k ≠ scalar 2 := by simp [writer,scalar]
  rw [finalBank,Function.update_of_ne hn1,
    afterMQ,Function.update_of_ne hn0,
    Function.update_of_ne hn2]
  rfl

theorem run (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ)
    (ha : S (WeightedPrefixAT.writer 54) = List.replicate a true)
    (hrx : S (WeightedPrefixAT.writer 17) = List.replicate rx true)
    (hq : S (WeightedPrefixAT.writer 56) = List.replicate q true)
    (ht : S (WeightedScaleDerivedFromBins.balance 1) =
      List.replicate t true) :
    ∃ u ≤ bound a rx q t,
      ((advance program)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel (Sum.inr false)))))),
          initialControl,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,initialControl,finalBank S a rx q t⟩ ∧
      (fun j : Fin 15 => (finalBank S a rx q t) (scalar j)) =
        Paper2.WeightedThresholdArithmetic.initial q t
          (Construction.qOne a * rx) ∧
      (∀ k : Fin 64,
        (finalBank S a rx q t) (writer k) =
          S (WeightedPrefixAT.writer k)) := by
  obtain ⟨um,hum,hm⟩ := mq_run S a rx q ha hrx hq
  have htRun := t_run S a rx q t ht
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    mqProgram tProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (Sum.inr false)))))
    BitMachineCopy.Label.scan
    WeightedMQJoin.initial WeightedMQJoin.initial
    (none : Option Bool) none
    (initialBank S) (afterMQ S a rx q) (finalBank S a rx q t)
    um (2*t+2) hm htRun
  refine ⟨u,by dsimp [bound]; omega,?_,threshold_input S a rx q t,?_⟩
  · simpa only [program,initialControl] using hr
  · intro k
    exact writer_frame S a rx q t k

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedMTPrefix
