import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRepeat
import EthInapproximability.CurrentPaper.SourceNormalizationMachineRanks

/-!
# Shared-bank local endpoint rank pass

The preceding finite machine physically repeats the padded endpoint stream.
This stage ranks all repeated old labels against the same retained padded
support vector, initially with zero copy offset. A later physical shift pass
must add the per-copy offsets before serialization.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRankLocal

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeRepeat.Stack ⊕ Fin 7
abbrev Label := SourceNormalizationMachineDecodeRepeat.Label ⊕
  SourceNormalizationMachineRanks.Label
abbrev Control := SourceNormalizationMachineDecodeRepeat.Control ×
  SourceNormalizationMachineRanks.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def repeatStack : SourceNormalizationMachineDecodeRepeat.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def rankStack : SourceNormalizationMachineRanks.Stack ↪ Stack where
  toFun
    | .inl k => match k.val with
      | 0 => .inl (.inl (.inr 2))
      | 1 => .inr 0
      | 2 => .inr 1
      | 3 => .inr 2
      | _ => .inr 3
    | .inr k => match k.val with
      | 0 => .inl (.inl (.inl 5))
      | 1 => .inl (.inr 2)
      | 2 => .inr 4
      | 3 => .inr 5
      | _ => .inr 6
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialRank : SourceNormalizationMachineRanks.Control := ((none,false),none)
def afterRepeatControl : SourceNormalizationMachineDecodeRepeat.Control :=
  SourceNormalizationMachineDecodeRepeat.repeatControl none
def repeatControl (v : SourceNormalizationMachineDecodeRepeat.Control) : Control :=
  (v,initialRank)
def rankControl (v : SourceNormalizationMachineRanks.Control) : Control :=
  (afterRepeatControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt repeatStack Sum.inl
      repeatControl Prod.fst
      (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
      (SourceNormalizationMachineDecodeRepeat.program l)
  | .inr l => BitMachineStackEmbedding.stmt rankStack Sum.inr
      rankControl Prod.snd none (SourceNormalizationMachineRanks.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeRepeat.start graphBits originalN).l.map Sum.inl,
    repeatControl (SourceNormalizationMachineDecodeRepeat.start graphBits originalN).var,
    Sum.elim (SourceNormalizationMachineDecodeRepeat.start graphBits originalN).stk
      ![[], [], [], [], [], [], []]⟩

private theorem repeat_program_eq (l : SourceNormalizationMachineDecodeRepeat.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt repeatStack Sum.inl
      repeatControl Prod.fst
      (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
      (SourceNormalizationMachineDecodeRepeat.program l) := rfl

private theorem rank_program_eq (l : SourceNormalizationMachineRanks.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt rankStack Sum.inr
      rankControl Prod.snd none (SourceNormalizationMachineRanks.program l) := rfl

noncomputable def afterRepeat (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodeRepeat.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodeRepeat.repeatStack
    (SourceNormalizationMachineDecodeRepeat.afterCount g originalN).stk
    Sum.inr SourceNormalizationMachineDecodeRepeat.repeatControl none
    (SourceNormalizationMachineDecodeRepeat.repeatFinalCfg g originalN)

private theorem repeat_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg repeatStack
      (start graphBits originalN).stk Sum.inl repeatControl
      (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
      (SourceNormalizationMachineDecodeRepeat.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self repeatStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeRepeat.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank repeatStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeRepeat.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

private theorem decode_repeat_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13) +
      (SourceNormalizationNumeric.repetitions g originalN *
        (2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3) + 1),
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg repeatStack
          (start (EncodedGraph.encode g) originalN).stk
          Sum.inl repeatControl
          (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
          (afterRepeat g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineDecodeRepeat.decode_repeat_run
    g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs repeatStack
    (start (EncodedGraph.encode g) originalN).stk
    Sum.inl repeatControl Prod.fst (by intro v; rfl)
    (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
    SourceNormalizationMachineDecodeRepeat.program program repeat_program_eq
    (SourceNormalizationMachineDecodeRepeat.start
      (EncodedGraph.encode g) originalN) t (by
      change (SourceNormalizationMachineDecodeRepeat.run t
        (SourceNormalizationMachineDecodeRepeat.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodeRepeat.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s) (repeat_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, afterRepeat] using hr)

private theorem afterRepeat_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineRepeatStream.Stack) :
    (afterRepeat g originalN).stk
      (SourceNormalizationMachineDecodeRepeat.repeatStack k) =
    (SourceNormalizationMachineDecodeRepeat.repeatFinalCfg g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeRepeat.repeatStack
    (SourceNormalizationMachineDecodeRepeat.afterCount g originalN).stk
    (SourceNormalizationMachineDecodeRepeat.repeatFinalCfg g originalN).stk k

private theorem afterRepeat_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : SourceNormalizationMachineDecodeRepeat.Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachineRepeatStream.Stack,
      SourceNormalizationMachineDecodeRepeat.repeatStack k = j) :
    (afterRepeat g originalN).stk j =
      (SourceNormalizationMachineDecodeRepeat.afterCount g originalN).stk j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodeRepeat.repeatStack
    (SourceNormalizationMachineDecodeRepeat.afterCount g originalN).stk
    (SourceNormalizationMachineDecodeRepeat.repeatFinalCfg g originalN).stk j hj

noncomputable def afterRepeatHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg repeatStack
    (start (EncodedGraph.encode g) originalN).stk
    Sum.inl repeatControl
    (some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)))
    (afterRepeat g originalN)

private theorem host_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecodeRepeat.Stack) :
    (afterRepeatHost g originalN).stk (.inl k) =
      (afterRepeat g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at repeatStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRepeat g originalN).stk k

private theorem host_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : Fin 7) :
    (afterRepeatHost g originalN).stk (.inr k) = [] := by
  change BitMachineStackEmbedding.bank repeatStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRepeat g originalN).stk (.inr k) = []
  rw [BitMachineStackEmbedding.bank_outside repeatStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRepeat g originalN).stk (.inr k) (by
      rintro ⟨j,h⟩
      simp [repeatStack] at h)]
  fin_cases k <;> rfl

private theorem afterRepeat_vector (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterRepeat g originalN).stk (.inl (.inr 2)) =
      SourceNormalizationNumeric.paddedSupport g := by
  have hr : ¬ ∃ k : SourceNormalizationMachineRepeatStream.Stack,
      SourceNormalizationMachineDecodeRepeat.repeatStack k =
        (.inl (.inr 2) : SourceNormalizationMachineDecodeRepeat.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeRepeat.repeatStack] at hk
  rw [afterRepeat_outside g originalN _ hr]
  have hc : ¬ ∃ k : SourceNormalizationMachineCounts.Stack,
      SourceNormalizationMachineDecodeCount.countStack k =
        (.inl (.inr 2) : SourceNormalizationMachineDecodeRepeat.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeCount.countStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk
    (.inl (.inr 2) : SourceNormalizationMachineDecodeRepeat.Stack) = _
  rw [BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk
    (.inl (.inr 2) : SourceNormalizationMachineDecodeRepeat.Stack) hc]
  change (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreStack
      (.inl (.inl (0 : Fin 5)))) = _
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreStack
      (.inl (.inl (0 : Fin 5)))) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
    (.inl (.inl (0 : Fin 5)))]
  change (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
    (SourceNormalizationMachineCore.padStack 0) = _
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineCore.padStack
    (SourceNormalizationMachineCore.padForeign g.vertices
      (SourceNormalizationNumeric.support g) []
      (List.replicate originalN true))
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true)).stk
    (SourceNormalizationMachineCore.padStack 0) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineCore.padStack
    (SourceNormalizationMachineCore.padForeign g.vertices
      (SourceNormalizationNumeric.support g) []
      (List.replicate originalN true))
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true)).stk 0]
  rfl

def rankInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRanks.Config :=
  SourceNormalizationMachineRanks.cfg
    (some (.inr .read)) ((none,false),none)
    (SourceNormalizationNumeric.paddedSupport g) [] [] [] []
    (SourceNormalizationMachineMark.endpointStream
      (SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN))
    (List.replicate originalN true) [] [] []

def rankFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRanks.Config :=
  SourceNormalizationMachineRanks.cfg none ((none,false),none)
    (SourceNormalizationNumeric.paddedSupport g) [] [] [] [] []
    (List.replicate originalN true) [] []
    (SourceNormalizationMachineRanks.rankedStream
      (SourceNormalizationNumeric.paddedSupport g) 0
      (SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN))

theorem final_divisor (g : EncodedGraph.Graph) (originalN : ℕ) :
    (show Config from BitMachineStackEmbedding.cfg rankStack
      (afterRepeatHost g originalN).stk Sum.inr rankControl none
      (rankFinalCfg g originalN)).stk
      (.inl (.inl (.inl (1 : Fin 8)))) =
        List.replicate (g.edges.length + 1) true := by
  have hr : ¬ ∃ k : SourceNormalizationMachineRanks.Stack,
      rankStack k = (.inl (.inl (.inl (1 : Fin 8))) : Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [rankStack] at hk
  change BitMachineStackEmbedding.bank rankStack
    (afterRepeatHost g originalN).stk (rankFinalCfg g originalN).stk
    (.inl (.inl (.inl (1 : Fin 8))) : Stack) = _
  rw [BitMachineStackEmbedding.bank_outside rankStack
    (afterRepeatHost g originalN).stk (rankFinalCfg g originalN).stk _ hr]
  rw [host_at]
  have he : ¬ ∃ k : SourceNormalizationMachineRepeatStream.Stack,
      SourceNormalizationMachineDecodeRepeat.repeatStack k =
        (.inl (.inl (1 : Fin 8)) : SourceNormalizationMachineDecodeRepeat.Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;>
      simp [SourceNormalizationMachineDecodeRepeat.repeatStack] at hk
  rw [afterRepeat_outside g originalN _ he]
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk
    (SourceNormalizationMachineDecodeCount.countStack
      (.inl (1 : Fin 6))) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk
    (.inl (1 : Fin 6))]
  rfl

private theorem rank_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineRanks.Stack,
      (rankInitialCfg g originalN).stk k =
        (afterRepeatHost g originalN).stk (rankStack k) := by
  intro k
  fin_cases k <;>
    simp [rankInitialCfg, SourceNormalizationMachineRanks.cfg,
      rankStack, host_at, host_extra, afterRepeat_vector,
      afterRepeat_at, SourceNormalizationMachineDecodeRepeat.repeatFinalCfg,
      SourceNormalizationMachineRepeatStream.cfg,
      SourceNormalizationMachineDecodeRepeat.repeatedStream_eq_indices]
  case «5» =>
    have h := afterRepeat_at g originalN
      (3 : SourceNormalizationMachineRepeatStream.Stack)
    simpa [SourceNormalizationMachineDecodeRepeat.repeatStack,
      SourceNormalizationMachineDecodeRepeat.repeatFinalCfg,
      SourceNormalizationMachineRepeatStream.cfg,
      SourceNormalizationMachineDecodeRepeat.repeatedStream_eq_indices] using h.symm
  case «6» =>
    have h := afterRepeat_at g originalN
      (4 : SourceNormalizationMachineRepeatStream.Stack)
    simpa [SourceNormalizationMachineDecodeRepeat.repeatStack,
      SourceNormalizationMachineDecodeRepeat.repeatFinalCfg,
      SourceNormalizationMachineRepeatStream.cfg] using h.symm

private theorem rank_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterRepeatHost g originalN =
    BitMachineStackEmbedding.cfg rankStack
      (afterRepeatHost g originalN).stk Sum.inr rankControl none
      (rankInitialCfg g originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self rankStack
    (afterRepeatHost g originalN).stk (rankInitialCfg g originalN).stk
    (rank_initial_stacks g originalN)
  change (⟨some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)),
    repeatControl (afterRepeat g originalN).var,
    (afterRepeatHost g originalN).stk⟩ : Config) =
    (⟨some (.inr (.inr SourceNormalizationMachineRanks.Phase.read)),
      rankControl (rankInitialCfg g originalN).var,
      BitMachineStackEmbedding.bank rankStack
        (afterRepeatHost g originalN).stk (rankInitialCfg g originalN).stk⟩ : Config)
  rw [hb]
  rfl

def rankCost (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  let indices := SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN
  let bits := SourceNormalizationNumeric.paddedSupport g
  5 * indices.sum + 7 * indices.length +
    (SourceNormalizationMachineRanks.rankedStream bits 0 indices).length + 2

/-- The physical assembled program now parses, normalizes support, counts and
copies, then applies one zero-offset rank pass to all repeated local endpoint
fields. A separate per-copy shift is still needed. -/
theorem decode_rank_local_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13) +
      (SourceNormalizationNumeric.repetitions g originalN *
        (2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3) + 1) +
      rankCost g originalN,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg rankStack
          (afterRepeatHost g originalN).stk Sum.inr rankControl none
          (rankFinalCfg g originalN) := by
  obtain ⟨a,ha,hrepeat⟩ := decode_repeat_stage g hg originalN
  let indices := SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN
  let bits := SourceNormalizationNumeric.paddedSupport g
  obtain ⟨b,hb,hrank⟩ := SourceNormalizationMachineRanks.rank_stream
    bits indices
    (SourceNormalizationMachineDecodeRepeat.repeatedIndices_bounded g hg originalN)
    0 [] (List.replicate originalN true)
  have hrank' : SourceNormalizationMachineRanks.run b
      (rankInitialCfg g originalN) = rankFinalCfg g originalN := by
    simpa only [rankInitialCfg, rankFinalCfg, bits, indices,
      List.replicate_zero] using hrank
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs rankStack
    (afterRepeatHost g originalN).stk Sum.inr rankControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineRanks.program program rank_program_eq
    (rankInitialCfg g originalN) b (by
      change (SourceNormalizationMachineRanks.run b
        (rankInitialCfg g originalN)).l = none
      rw [hrank']
      rfl)
  change ((advance SourceNormalizationMachineRanks.program)^[b]) _ = _ at hrank'
  rw [hrank'] at hr
  refine ⟨a + s, by simpa only [rankCost, bits, indices] using
    (show a + s ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13) +
      (SourceNormalizationNumeric.repetitions g originalN *
        (2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3) + 1) +
      (5 * indices.sum + 7 * indices.length +
        (SourceNormalizationMachineRanks.rankedStream bits 0 indices).length + 2) by
      omega), ?_⟩
  exact (run_add hrepeat s).trans
    ((congrArg (run s) (rank_initial g originalN)).trans
      (by simpa only [run] using hr))

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRankLocal
