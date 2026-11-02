import EthInapproximability.CurrentPaper.WeightedMTPrefix
import EthInapproximability.CurrentPaper.WeightedThresholdToSize
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! The reached a/q/t words feed m, threshold, prime search and chosen size
without reloading raw parameter words or prescribing derived runtime values. -/

namespace EthInapproximability.CurrentPaper.WeightedActualSizeSuffix

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedMTPrefix.Stack ⊕
  (ChosenPrimeRaw.Stack ⊕ Fin 8)
def mtSlots : WeightedMTPrefix.Stack ↪ Stack :=
  ⟨Sum.inl,by intro a b h; exact Sum.inl_injective h⟩
def scaleKey (j : ETHScaleActualComplete.Stack) : Stack :=
  .inl (.inl (.inl (.inl (.inl j))))
def balanceKey (j : BalanceOrderArithmetic.Stack) : Stack :=
  .inl (.inl (WeightedScaleDerivedFromBins.balance j))
def writer (k : Fin 64) : Stack :=
  .inl (WeightedMTPrefix.writer k)
def scalar (j : Fin 15) : Stack :=
  .inl (WeightedMTPrefix.scalar j)
def thresholdSlots : WeightedThresholdToSize.Stack ↪ Stack where
  toFun
    | .inl (.inl (.inl (.inl j))) => scaleKey j
    | .inl (.inl (.inl (.inr j))) => balanceKey j
    | .inl (.inl (.inr k)) => writer k
    | .inl (.inr j) => scalar j
    | .inr j => .inr j
  inj' := by
    intro a b h
    rcases a with (((j | j) | k) | j) | j <;>
      rcases b with (((l | l) | z) | l) | l <;>
      simp [scaleKey,balanceKey,writer,scalar,
        WeightedMTPrefix.writer,WeightedMTPrefix.scalar,
        WeightedPrefixAT.writer,WeightedScaleDerivedFromBins.balance,
        WeightedScaleDerivedFromBins.writer,
        WeightedBinsGraphQ.writer,WeightedGraphQJoined.writer] at h ⊢ <;>
      assumption
def initialBank (S : WeightedPrefixAT.Stack → List Bool) :
    Stack → List Bool :=
  Sum.elim (WeightedMTPrefix.initialBank S) (fun _ => [])
def afterMT (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ) : Stack → List Bool :=
  Sum.elim (WeightedMTPrefix.finalBank S a rx q t) (fun _ => [])
def finalBank (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ) (P : ChosenPrimeRaw.Stack → List Bool) :
    Stack → List Bool :=
  let T := WeightedMTPrefix.finalBank S a rx q t
  let W := fun k : Fin 64 => T (WeightedMTPrefix.writer k)
  bank thresholdSlots (afterMT S a rx q t)
    (WeightedThresholdToSize.finalBank
      (fun j => (afterMT S a rx q t) (thresholdSlots (.inl j)))
      W q t (Construction.qOne a * rx) P)
def mtProgram := fun l => stackStmt mtSlots (WeightedMTPrefix.program l)
def thresholdProgram := fun l => stackStmt thresholdSlots
  (WeightedThresholdToSize.program l)
def program := BitMachineRawSequence.program mtProgram thresholdProgram
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        WeightedThresholdToSize.thresholdStart)))
  WeightedMTPrefix.initialControl WeightedThresholdToSize.initialControl
def initialControl :=
  (WeightedMTPrefix.initialControl,WeightedThresholdToSize.initialControl)
def bound (a rx q t : ℕ) :=
  WeightedMTPrefix.bound a rx q t +
  WeightedThresholdToSize.bound q t (Construction.qOne a * rx) + 1

private theorem threshold_input_projection
    (S : WeightedPrefixAT.Stack → List Bool) (a rx q t : ℕ) :
    (fun j : WeightedThresholdToSize.Stack =>
      (afterMT S a rx q t) (thresholdSlots j)) =
      WeightedThresholdToSize.initialBank
        (fun j => (afterMT S a rx q t)
          (thresholdSlots (.inl j))) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => rfl

theorem threshold_run (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ)
    (h57 : S (WeightedPrefixAT.writer 57) = []) :
    ∃ u ≤ WeightedThresholdToSize.bound q t
      (Construction.qOne a * rx),
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance thresholdProgram)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                WeightedThresholdToSize.thresholdStart))),
            WeightedThresholdToSize.initialControl,
            afterMT S a rx q t⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,WeightedThresholdToSize.initialControl,
            finalBank S a rx q t P⟩ ∧
        (∀ k : Fin 64,
          (finalBank S a rx q t P) (writer k) =
            Function.update
              (fun j => S (WeightedPrefixAT.writer j)) 57
              (List.replicate
                (PrimeSampler.size q t (Construction.qOne a * rx)) true) k) := by
  let T := WeightedMTPrefix.finalBank S a rx q t
  let B := afterMT S a rx q t
  let W := fun k : Fin 64 => T (WeightedMTPrefix.writer k)
  let S' := fun j : WeightedThresholdInputJoin.Stack =>
    B (thresholdSlots (.inl j))
  have hinput :
      (fun j : Fin 15 => S' (WeightedThresholdInputJoin.scalar j)) =
        Paper2.WeightedThresholdArithmetic.initial q t
          (Construction.qOne a * rx) := by
    simpa only [S',B,WeightedThresholdInputJoin.scalar,
      thresholdSlots,scalar,afterMT] using
      WeightedMTPrefix.threshold_input S a rx q t
  have hwriter (k : Fin 64) :
      S' (WeightedThresholdInputJoin.writer k) = W k := by
    rfl
  have h57' : W 57 = [] := by
    exact (WeightedMTPrefix.writer_frame S a rx q t 57).trans h57
  obtain ⟨u,hu,P,hr,hframe⟩ :=
    WeightedThresholdToSize.run S' W q t (Construction.qOne a * rx)
      hinput hwriter h57'
  have he := BitMachineStackRun.run thresholdSlots B
    WeightedThresholdToSize.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          WeightedThresholdToSize.thresholdStart))),
      WeightedThresholdToSize.initialControl,
      WeightedThresholdToSize.initialBank S'⟩ :
      TM2.Cfg (fun _ : WeightedThresholdToSize.Stack => Bool) _ _) u
  rw [hr] at he
  have hi : bank thresholdSlots B
      (WeightedThresholdToSize.initialBank S') = B :=
    bank_eq_self thresholdSlots B _
      (fun j => (congrFun (threshold_input_projection S a rx q t) j).symm)
  refine ⟨u,hu,P,?_,?_⟩
  · simpa only [thresholdProgram,stackCfg,hi,finalBank,S',W,T,B]
      using he
  · intro k
    change (bank thresholdSlots B _)
      (thresholdSlots (WeightedThresholdToSize.writer k)) = _
    rw [bank_at]
    have hW : W = fun j : Fin 64 =>
        S (WeightedPrefixAT.writer j) := by
      funext j
      exact WeightedMTPrefix.writer_frame S a rx q t j
    change WeightedThresholdToSize.finalBank S' W q t
      (Construction.qOne a * rx) P
        (WeightedThresholdToSize.writer k) =
      Function.update (fun j : Fin 64 =>
        S (WeightedPrefixAT.writer j)) 57
        (List.replicate
          (PrimeSampler.size q t (Construction.qOne a * rx)) true) k
    rw [hW]
    simpa only [hW] using hframe k

/-- Fixed physical controller from already reached a/q/t and a source rx
word to exact chosen size at writer57. The arithmetic m and threshold are
produced, not initial values. -/
theorem run (S : WeightedPrefixAT.Stack → List Bool)
    (a rx q t : ℕ)
    (ha : S (WeightedPrefixAT.writer 54) = List.replicate a true)
    (hrx : S (WeightedPrefixAT.writer 17) = List.replicate rx true)
    (hq : S (WeightedPrefixAT.writer 56) = List.replicate q true)
    (ht : S (WeightedScaleDerivedFromBins.balance 1) =
      List.replicate t true)
    (h57 : S (WeightedPrefixAT.writer 57) = []) :
    ∃ u ≤ bound a rx q t,
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel (Sum.inr false))))))),
            initialControl,initialBank S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,finalBank S a rx q t P⟩ ∧
        (∀ k : Fin 64,
          (finalBank S a rx q t P) (writer k) =
            Function.update
              (fun j => S (WeightedPrefixAT.writer j)) 57
              (List.replicate
                (PrimeSampler.size q t (Construction.qOne a * rx)) true) k) := by
  obtain ⟨um,hum,hm,hinput,hframe⟩ :=
    WeightedMTPrefix.run S a rx q t ha hrx hq ht
  obtain ⟨uz,huz,P,hz,hwriter⟩ :=
    threshold_run S a rx q t h57
  have hLift :
      ((advance mtProgram)^[um])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel (Sum.inr false)))))),
          WeightedMTPrefix.initialControl,initialBank S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedMTPrefix.initialControl,afterMT S a rx q t⟩ := by
    have he := BitMachineStackRun.run mtSlots (initialBank S)
      WeightedMTPrefix.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (Sum.inr false)))))),
        WeightedMTPrefix.initialControl,
        WeightedMTPrefix.initialBank S⟩ :
        TM2.Cfg (fun _ : WeightedMTPrefix.Stack => Bool) _ _) um
    rw [hm] at he
    have hi : bank mtSlots (initialBank S)
        (WeightedMTPrefix.initialBank S) = initialBank S :=
      bank_eq_self mtSlots _ _ (fun _ => rfl)
    have ho : bank mtSlots (initialBank S)
        (WeightedMTPrefix.finalBank S a rx q t) =
        afterMT S a rx q t := by
      funext j
      cases j with
      | inl j => exact bank_at mtSlots _ _ j
      | inr j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k,h⟩; cases h
    simpa only [mtProgram,stackCfg,hi,ho] using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    mtProgram thresholdProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (Sum.inr false))))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          WeightedThresholdToSize.thresholdStart)))
    WeightedMTPrefix.initialControl WeightedMTPrefix.initialControl
    WeightedThresholdToSize.initialControl
    WeightedThresholdToSize.initialControl
    (initialBank S) (afterMT S a rx q t)
    (finalBank S a rx q t P)
    um uz hLift hz
  refine ⟨u,by dsimp [bound]; omega,P,?_,hwriter⟩
  simpa only [program,initialControl] using hr

#print axioms threshold_run
#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedActualSizeSuffix
