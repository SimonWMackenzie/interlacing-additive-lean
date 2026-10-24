import EthInapproximability.CurrentPaper.SourceClausePrefixLoopIteration
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopCost

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

noncomputable abbrev workCount := SourceClauseClearExcept.workCount PrefixSharedClear.keep

theorem blank_word_bound (n v : ℕ) (saved output count : List Bool) :
    ∀ x : PrefixSharedCore.Stack,
      (PrefixGateReady.blank n v saved output count x).length ≤
        n + v + saved.length + output.length + count.length := by
  intro x
  cases x with
  | inl i =>
    fin_cases i <;>
      simp [PrefixGateReady.blank, PrefixGateReady.coreWords] <;> omega
  | inr j =>
    simp [PrefixGateReady.blank]

/-- A physical cleanup scans a fixed list of work stacks. Its charged
cost is bounded by the words at the beginning of the preceding run and the
literal per-transition stack growth of that run. -/
theorem clear_after_run {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : PrefixSharedCore.Stack => Bool) L V)
    (l : L) (v : V) (S F : PrefixSharedCore.Stack → List Bool)
    (t B H : ℕ) (ht : t ≤ B)
    (hrun : ((advance P)^[t])
      (⟨some l, v, S⟩ : TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) L V) =
      ⟨none, v, F⟩)
    (hinit : ∀ x, (S x).length ≤ H) :
    PrefixSharedClear.cost F ≤
      workCount * (H + BitMachineStackGrowth.perStep P * B) +
        workCount + 2 := by
  have hi (i : Fin workCount) :
      (F (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)).length ≤
        H + BitMachineStackGrowth.perStep P * B := by
    have hg := BitMachineStackGrowth.run_growth P
      (⟨some l, v, S⟩ :
        TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) L V)
      t (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)
    have hg' :
        (F (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)).length ≤
          (S (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)).length +
            BitMachineStackGrowth.perStep P * t := by
      simpa only [hrun] using hg
    have hs := hinit (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)
    have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep P) ht
    omega
  have hsum :
      (∑ i : Fin workCount,
        (F (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)).length) ≤
      workCount * (H + BitMachineStackGrowth.perStep P * B) := by
    calc
      _ ≤ ∑ _i : Fin workCount,
          (H + BitMachineStackGrowth.perStep P * B) := by
            apply Finset.sum_le_sum
            intro i _
            exact hi i
      _ = workCount * (H + BitMachineStackGrowth.perStep P * B) := by simp
  change (∑ i : Fin workCount,
      (F (SourceClauseClearExcept.workBank PrefixSharedClear.keep i)).length) +
      workCount + 2 ≤ _
  omega

noncomputable def unitPre (n v w ell : ℕ) : ℕ :=
  (SourceClauseFixedBatch.costPrefix
    (PrefixUnitClean.constantSize w ell) 3 + 1) +
    PrefixUnitRun.cost n v w ell + 1

noncomputable def gatePre {n q : ℕ} (v : Fin n) (s : Fin 2) : ℕ :=
  PrefixGateOperands.preparationCost s.val (width 2 q + 1)
      (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
      (width 2 q + 1) true + 1

noncomputable def unitPhaseCost (n v w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) : ℕ :=
  unitPre n v w ell +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.unitEmbedding
        (PrefixGateReady.blank n v saved output count)
        (PrefixUnitRun.finished n v w ell sign saved output count)) + 1

theorem unitPhaseCost_le (n v w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitPhaseCost n v w ell sign saved output count ≤
      unitPre n v w ell +
      workCount * ((n + v + saved.length + output.length + count.length) +
        BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w ell sign) *
          unitPre n v w ell) + workCount + 3 := by
  obtain ⟨t, ht, hr⟩ := PrefixSharedUnitPair.run n v w ell sign
    saved output count
  have ht' : t ≤ unitPre n v w ell := by
    simpa only [unitPre] using ht
  have hc := clear_after_run (PrefixSharedUnitPair.program w ell sign)
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (PrefixUnitClean.constantSize w ell) 0))
    ((), PrefixUnitRun.startControl)
    (PrefixGateReady.blank n v saved output count)
    (bank PrefixSharedCore.unitEmbedding
      (PrefixGateReady.blank n v saved output count)
      (PrefixUnitRun.finished n v w ell sign saved output count))
    t (unitPre n v w ell)
    (n + v + saved.length + output.length + count.length)
    ht' hr (blank_word_bound n v saved output count)
  unfold unitPhaseCost
  omega

theorem unitCost_le (n v w : ℕ)
    (saved output count : List Bool) :
    PrefixFirstTwoCycles.unitCost n v w saved output count ≤
      unitPre n v w 0 +
      workCount * ((n + v + saved.length + output.length + count.length) +
        BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 0 false) *
          unitPre n v w 0) + workCount + 3 := by
  simpa only [PrefixFirstTwoCycles.unitCost, unitPhaseCost, unitPre] using
    unitPhaseCost_le n v w 0 false saved output count

theorem terminalCost_le (n v w : ℕ)
    (saved output count : List Bool) :
    PrefixFullCallback.terminalCost n v w saved output count ≤
      unitPre n v w 2 +
      workCount * ((n + v + saved.length + output.length + count.length) +
        BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 2 true) *
          unitPre n v w 2) + workCount + 3 := by
  simpa only [PrefixFullCallback.terminalCost, unitPhaseCost, unitPre] using
    unitPhaseCost_le n v w 2 true saved output count

theorem gateCost_le {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    PrefixFirstTwoCycles.gateCost (q := q) v s saved output count ≤
      gatePre (q := q) v s +
      workCount * ((n + v.val + saved.length + output.length + count.length) +
        BitMachineStackGrowth.perStep
          (PrefixGateCycle.pairProgram s.val (width 2 q + 1)) *
          gatePre (q := q) v s) + workCount + 3 := by
  obtain ⟨t, ht, hr⟩ := PrefixGateCycle.pair_run (q := q) v s
    saved output count
  have ht' : t ≤ gatePre (q := q) v s := by
    simpa only [gatePre] using ht
  have hc := clear_after_run
    (PrefixGateCycle.pairProgram s.val (width 2 q + 1))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0)))
    (((), ((), none)), PrefixGateCycle.gateControl)
    (PrefixGateReady.blank n v.val saved output count)
    (bank PrefixSharedCore.gateEmbedding
      (PrefixGateReady.prepared (q := q) v s saved output count)
      (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
        v.val 2 s.val n s.val v.val (width 2 q + 1) true
        saved output count))
    t (gatePre (q := q) v s)
    (n + v.val + saved.length + output.length + count.length)
    ht' hr (blank_word_bound n v.val saved output count)
  unfold PrefixFirstTwoCycles.gateCost
  dsimp only [gatePre] at hc ⊢
  omega

def variableBound (n q : ℕ) : ℕ :=
  2 * n + n * (width 2 q + 2) + 4

theorem atLeast_word_length_le {n q : ℕ} (v : Fin n) :
    (PrefixLoopIteration.word n q v.val).length ≤
      8 * (6 * variableBound n q + 6) := by
  let b := base n q (atLeastOrdinal v)
  let M := variableBound n q
  have hvw : v.val * (width 2 q + 1) ≤
      n * (width 2 q + 1) :=
    Nat.mul_le_mul_right _ v.isLt.le
  have hbase : b + (atLeastPayload v).length < M := by
    change 2 * n + v.val * (width 2 q + 1) + 2 <
      2 * n + n * (width 2 q + 2) + 4
    nlinarith [v.isLt]
  have hlit : ∀ l ∈ atLeastPayload v, l.variable < M := by
    intro l hl
    simp only [atLeastPayload, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      simp only [SourceBooleanEncoding.positive] <;>
      have := (bitIndex v (0 : Fin 2)).isLt <;>
      have := (bitIndex v (1 : Fin 2)).isLt <;>
      simp only [M, variableBound] <;> omega
  have hv := chain_valid b M (atLeastPayload v) hbase hlit
  have hlen := EncodedCNF.clauseFields_length_upper M
    (chain b (atLeastPayload v)) hv
  rw [PrefixLoopIteration.word_of_lt n q v.val v.isLt,
    List.length_reverse]
  simpa only [b, M, atLeast_chain_length] using hlen

theorem savedAt_length_le (n q k : ℕ) (saved : List Bool)
    (hk : k ≤ n) :
    (PrefixLoopIteration.savedAt n q saved k).length ≤
      saved.length + k * (8 * (6 * variableBound n q + 6)) := by
  induction k with
  | zero => simp [PrefixLoopIteration.savedAt]
  | succ k ih =>
    have hkn : k < n := by omega
    have hw := atLeast_word_length_le (q := q) (⟨k, hkn⟩ : Fin n)
    change (PrefixLoopIteration.word n q k).length ≤
      8 * (6 * variableBound n q + 6) at hw
    have hs := ih (by omega)
    simp only [PrefixLoopIteration.savedAt, List.length_append]
    rw [Nat.succ_mul]
    omega

theorem countAt_length (count : List Bool) (k : ℕ) :
    (PrefixLoopIteration.countAt count k).length = 8 * k + count.length := by
  simp [PrefixLoopIteration.countAt]

theorem partialSaved_length_le {n q : ℕ} (v : Fin n)
    (saved : List Bool) :
    (PrefixFirstTwoCycles.firstSaved n v.val (width 2 q + 1) saved).length ≤
        saved.length + 8 * (6 * variableBound n q + 6) ∧
    (PrefixFirstTwoCycles.secondSaved (q := q) v saved).length ≤
        saved.length + 8 * (6 * variableBound n q + 6) ∧
    (PrefixThreeCycles.thirdSaved (q := q) v saved).length ≤
        saved.length + 8 * (6 * variableBound n q + 6) := by
  let s₁ := PrefixFirstTwoCycles.firstSaved n v.val (width 2 q + 1) saved
  let s₂ := PrefixFirstTwoCycles.secondSaved (q := q) v saved
  let s₃ := PrefixThreeCycles.thirdSaved (q := q) v saved
  let s₄ := PrefixSourceIdentity.savedAfter (q := q) v saved
  have h12 : s₁.length ≤ s₂.length := by
    dsimp only [s₁, s₂]
    simp only [PrefixFirstTwoCycles.secondSaved,
      PrefixSharedGateHandoff.nextSaved, List.length_append,
      List.length_reverse]
    omega
  have h23 : s₂.length ≤ s₃.length := by
    dsimp only [s₂, s₃]
    simp only [PrefixThreeCycles.thirdSaved,
      PrefixSharedGateHandoff.nextSaved, List.length_append,
      List.length_reverse]
    omega
  have h34 : s₃.length ≤ s₄.length := by
    change s₃.length ≤
      (PrefixSharedUnitHandoff.nextSaved n v.val (width 2 q + 1)
        2 true s₃).length
    simp [PrefixSharedUnitHandoff.nextSaved]
  have h4 : s₄.length ≤
      saved.length + 8 * (6 * variableBound n q + 6) := by
    change (PrefixSourceIdentity.savedAfter (q := q) v saved).length ≤ _
    rw [PrefixSourceIdentity.savedAfter_eq_chain]
    simp only [List.length_append, List.length_reverse]
    have hw := atLeast_word_length_le (q := q) v
    rw [PrefixLoopIteration.word_of_lt n q v.val v.isLt] at hw
    have hw' : (clauseFields
        (chain (base n q (atLeastOrdinal v)) (atLeastPayload v))).length ≤
        8 * (6 * variableBound n q + 6) := by
      simpa only [List.length_reverse, Fin.eta] using hw
    omega
  exact ⟨h12.trans (h23.trans (h34.trans h4)),
    h23.trans (h34.trans h4), h34.trans h4⟩

#print axioms clear_after_run

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopCost
