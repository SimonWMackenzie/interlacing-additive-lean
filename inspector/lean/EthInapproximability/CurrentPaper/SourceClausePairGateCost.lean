import EthInapproximability.CurrentPaper.SourceClausePairGateCycle
import EthInapproximability.CurrentPaper.SourceClausePrefixLoopCost

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCost

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

abbrev Stack := PairUnitLift.Stack
noncomputable abbrev workCount :=
  SourceClauseClearExcept.workCount PrefixSharedClear.keep

theorem pair_blank_word_bound (n v ordinal : Nat)
    (saved output count : List Bool) :
    ∀ x : Stack,
      (PairUnitLift.pairBank n v ordinal saved output count x).length ≤
        n + v + ordinal + saved.length + output.length + count.length := by
  intro x
  rw [← PairGateBase.gateBlank_eq_pairBank]
  cases x with
  | inl y =>
      change (bank PairGateBase.coreEmbedding
        (PairGateBase.ordinalForeign ordinal)
        (PrefixGateReady.blank n v saved output count)
        (PairGateBase.coreEmbedding y)).length ≤ _
      rw [bank_at]
      have h := PrefixLoopCost.blank_word_bound n v saved output count y
      omega
  | inr z =>
      cases z
      rw [PairGateBase.gateBlank, bank_outside]
      · simp [PairGateBase.ordinalForeign]
        omega
      · rintro ⟨y, hy⟩
        cases hy

theorem clear_after_run {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (l : L) (v : V) (S F : Stack → List Bool)
    (t B H : Nat) (ht : t ≤ B)
    (hrun : ((advance P)^[t])
      (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, v, F⟩)
    (hinit : ∀ x, (S x).length ≤ H) :
    PrefixSharedClear.cost (fun x => F (PairGateBase.coreEmbedding x)) ≤
      workCount * (H + BitMachineStackGrowth.perStep P * B) +
        workCount + 2 := by
  have hi (i : Fin workCount) :
      (F (PairGateBase.coreEmbedding
        (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))).length ≤
        H + BitMachineStackGrowth.perStep P * B := by
    have hg := BitMachineStackGrowth.run_growth P
      (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) L V)
      t (PairGateBase.coreEmbedding
        (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))
    have hg' :
        (F (PairGateBase.coreEmbedding
          (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))).length ≤
        (S (PairGateBase.coreEmbedding
          (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))).length +
          BitMachineStackGrowth.perStep P * t := by
      simpa only [hrun] using hg
    have hs := hinit (PairGateBase.coreEmbedding
      (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))
    have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep P) ht
    omega
  have hsum :
      (∑ i : Fin workCount,
        (F (PairGateBase.coreEmbedding
          (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))).length) ≤
      workCount * (H + BitMachineStackGrowth.perStep P * B) := by
    calc
      _ ≤ ∑ _i : Fin workCount,
          (H + BitMachineStackGrowth.perStep P * B) := by
            apply Finset.sum_le_sum
            intro i _
            exact hi i
      _ = workCount * (H + BitMachineStackGrowth.perStep P * B) := by simp
  change (∑ i : Fin workCount,
      (F (PairGateBase.coreEmbedding
        (SourceClauseClearExcept.workBank PrefixSharedClear.keep i))).length) +
      workCount + 2 ≤ _
  omega

noncomputable def firstCost {n q : Nat} (v : Fin n)
    (s t ell : Fin 2) : Nat :=
  let bit := if ell = 0 then s else t
  let sign := if ell = 0 then PairSignedGate.signFirst s t
    else PairSignedGate.signSecond s t
  PrefixGateOperands.preparationCost bit.val (width 2 q + 1)
      (List.replicate v.val true) +
    (v.val + bit.val + 4) +
    (2 * (pairOrdinal v s t) + 2) +
    (PairGatePatch.offsetSize ell 0 + 2) + 3 +
    SourceClauseRowGate.cost v.val 2 bit.val n ell.val
      (pairOrdinal v s t) (width 2 q + 1) sign + 1

theorem first_run {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then PairSignedGate.signFirst s t
      else PairSignedGate.signSecond s t
    ∃ u ≤ firstCost (q := q) v s t ell,
      ((advance (PairGateCycle.firstProgram bit ell sign
        (width 2 q + 1)))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (SourceClauseFixedBatch.labelAt
                    (PrefixGateOperands.constantSize bit.val
                      (width 2 q + 1)) 0)))))),
          ((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl),
          PairUnitLift.pairBank n v.val (pairOrdinal v s t)
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl),
          PairGateExecute.finished (q := q) v s t ell
            saved output count⟩ := by
  dsimp
  let bit : Fin 2 := if ell = 0 then s else t
  let sign : Bool := if ell = 0 then PairSignedGate.signFirst s t
    else PairSignedGate.signSecond s t
  obtain ⟨a, ha, hA⟩ := PairGatePrep.run (q := q) v bit ell
    (pairOrdinal v s t) saved output count
  obtain ⟨b, hb, hB⟩ := PairGateExecute.run (q := q) v s t ell
    saved output count
  obtain ⟨u, hu, hU⟩ := BitMachineRawSequence.runs
    (PairGatePrep.program bit ell (width 2 q + 1))
    (PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixGateOperands.constantSize bit.val
                (width 2 q + 1)) 0)))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    (((((), ((), none)), ((), none)), none), ())
    PairGateExecute.gateControl PairGateExecute.gateControl
    (PairUnitLift.pairBank n v.val (pairOrdinal v s t)
      saved output count)
    (PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
      saved output count)
    (PairGateExecute.finished (q := q) v s t ell
      saved output count)
    a b hA hB
  refine ⟨u, ?_, ?_⟩
  · dsimp [firstCost, bit, sign]
    dsimp [bit, sign] at ha hb
    omega
  · simpa only [PairGateCycle.firstProgram, bit, sign] using hU

theorem cleanup_cost_le {n q : Nat} (v : Fin n)
    (s t ell : Fin 2) (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then PairSignedGate.signFirst s t
      else PairSignedGate.signSecond s t
    PrefixSharedClear.cost (PairGateCleanup.localBank (q := q)
      v s t ell saved output count) ≤
      workCount *
        ((n + v.val + (pairOrdinal v s t) + saved.length +
          output.length + count.length) +
        BitMachineStackGrowth.perStep
          (PairGateCycle.firstProgram bit ell sign (width 2 q + 1)) *
          firstCost (q := q) v s t ell) + workCount + 2 := by
  dsimp
  obtain ⟨u, hu, hrun⟩ := first_run (q := q) v s t ell
    saved output count
  exact clear_after_run
    (PairGateCycle.firstProgram (if ell = 0 then s else t) ell
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t) (width 2 q + 1))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixGateOperands.constantSize
                  (if ell = 0 then s else t).val
                  (width 2 q + 1)) 0))))))
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl)
    (PairUnitLift.pairBank n v.val (pairOrdinal v s t)
      saved output count)
    (PairGateExecute.finished (q := q) v s t ell
      saved output count)
    u (firstCost (q := q) v s t ell)
    (n + v.val + pairOrdinal v s t + saved.length +
      output.length + count.length)
    hu hrun
    (pair_blank_word_bound n v.val (pairOrdinal v s t)
      saved output count)

noncomputable def clockEnvelope {n q : Nat} (v : Fin n)
    (s t ell : Fin 2) (saved output count : List Bool) : Nat :=
  let bit := if ell = 0 then s else t
  let sign := if ell = 0 then PairSignedGate.signFirst s t
    else PairSignedGate.signSecond s t
  firstCost (q := q) v s t ell +
    workCount *
      ((n + v.val + pairOrdinal v s t + saved.length +
        output.length + count.length) +
        BitMachineStackGrowth.perStep
          (PairGateCycle.firstProgram bit ell sign (width 2 q + 1)) *
          firstCost (q := q) v s t ell) + workCount + 3

theorem charged_cost_le_envelope {n q : Nat} (v : Fin n)
    (s t ell : Fin 2) (saved output count : List Bool) :
    firstCost (q := q) v s t ell +
      PrefixSharedClear.cost (PairGateCleanup.localBank (q := q)
        v s t ell saved output count) + 1 ≤
      clockEnvelope (q := q) v s t ell saved output count := by
  have hc := cleanup_cost_le (q := q) v s t ell
    saved output count
  dsimp only [clockEnvelope] at hc ⊢
  omega

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCost
