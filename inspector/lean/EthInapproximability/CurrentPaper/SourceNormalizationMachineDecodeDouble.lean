import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRankLocal
import EthInapproximability.CurrentPaper.SourceNormalizationMachineDoubleUnary

/-! The actual decoded/ranked machine continues with a charged scan doubling
the retained unary padded edge count into the per-copy field counter. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeDouble

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeRankLocal.Stack ⊕ Fin 2
abbrev Label := SourceNormalizationMachineDecodeRankLocal.Label ⊕
  SourceNormalizationMachineDoubleUnary.Phase
abbrev Control := SourceNormalizationMachineDecodeRankLocal.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def rankStack : SourceNormalizationMachineDecodeRankLocal.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def doubleStack : SourceNormalizationMachineDoubleUnary.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inl (.inl (.inl (1 : Fin 8))))
    | 1 => .inr 0
    | _ => .inr 1
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialDouble : Option Bool := none
def afterRankControl : SourceNormalizationMachineDecodeRankLocal.Control :=
  SourceNormalizationMachineDecodeRankLocal.rankControl ((none,false),none)
def rankControl (v : SourceNormalizationMachineDecodeRankLocal.Control) : Control :=
  (v,initialDouble)
def doubleControl (v : Option Bool) : Control := (afterRankControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt rankStack Sum.inl
      rankControl Prod.fst
      (some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan))
      (SourceNormalizationMachineDecodeRankLocal.program l)
  | .inr l => BitMachineStackEmbedding.stmt doubleStack Sum.inr
      doubleControl Prod.snd none
      (SourceNormalizationMachineDoubleUnary.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeRankLocal.start graphBits originalN).l.map Sum.inl,
    rankControl (SourceNormalizationMachineDecodeRankLocal.start graphBits originalN).var,
    Sum.elim (SourceNormalizationMachineDecodeRankLocal.start graphBits originalN).stk
      ![[],[]]⟩

private theorem rank_program_eq (l : SourceNormalizationMachineDecodeRankLocal.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt rankStack Sum.inl
      rankControl Prod.fst
      (some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan))
      (SourceNormalizationMachineDecodeRankLocal.program l) := rfl

private theorem double_program_eq (l : SourceNormalizationMachineDoubleUnary.Phase) :
    program (.inr l) = BitMachineStackEmbedding.stmt doubleStack Sum.inr
      doubleControl Prod.snd none
      (SourceNormalizationMachineDoubleUnary.program l) := rfl

noncomputable def afterRank (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodeRankLocal.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodeRankLocal.rankStack
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
    Sum.inr SourceNormalizationMachineDecodeRankLocal.rankControl none
    (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN)

noncomputable def afterRankHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg rankStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl rankControl
    (some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan))
    (afterRank g originalN)

def doubleInitialCfg (g : EncodedGraph.Graph) :
    SourceNormalizationMachineDoubleUnary.Config :=
  SourceNormalizationMachineDoubleUnary.cfg (some .scan) none
    (List.replicate (g.edges.length + 1) true) [] []

def doubleFinalCfg (g : EncodedGraph.Graph) :
    SourceNormalizationMachineDoubleUnary.Config :=
  SourceNormalizationMachineDoubleUnary.cfg none none
    (List.replicate (g.edges.length + 1) true) []
    (List.replicate (2 * (g.edges.length + 1)) true)

private theorem rank_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg rankStack
      (start graphBits originalN).stk Sum.inl rankControl
      (some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan))
      (SourceNormalizationMachineDecodeRankLocal.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self rankStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank rankStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

def rankBound (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  SourceNormalizationMachineDecode.graphCost g +
    SourceNormalizationMachineDecodePad.padCost g +
    SourceNormalizationMachineDecodeCore.coreCost g +
    (10 * originalN + 13 * g.edges.length + 13) +
    (SourceNormalizationNumeric.repetitions g originalN *
      (2 * (SourceNormalizationMachineDecodeRepeat.paddedStream g).length + 3) + 1) +
    SourceNormalizationMachineDecodeRankLocal.rankCost g originalN

private theorem rank_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ rankBound g originalN,
      run t (start (EncodedGraph.encode g) originalN) =
        afterRankHost g originalN := by
  obtain ⟨t,ht,he⟩ :=
    SourceNormalizationMachineDecodeRankLocal.decode_rank_local_run g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs rankStack
    (start (EncodedGraph.encode g) originalN).stk
    Sum.inl rankControl Prod.fst (by intro v; rfl)
    (some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan))
    SourceNormalizationMachineDecodeRankLocal.program program rank_program_eq
    (SourceNormalizationMachineDecodeRankLocal.start
      (EncodedGraph.encode g) originalN) t (by
      change (SourceNormalizationMachineDecodeRankLocal.run t
        (SourceNormalizationMachineDecodeRankLocal.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodeRankLocal.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, by simpa only [rankBound] using hs.trans ht, ?_⟩
  exact (congrArg (run s)
    (rank_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, afterRankHost, afterRank] using hr)

private theorem afterRankHost_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecodeRankLocal.Stack) :
    (afterRankHost g originalN).stk (.inl k) =
      (afterRank g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at rankStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRank g originalN).stk k

private theorem afterRankHost_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : Fin 2) :
    (afterRankHost g originalN).stk (.inr k) = [] := by
  change BitMachineStackEmbedding.bank rankStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRank g originalN).stk (.inr k) = []
  rw [BitMachineStackEmbedding.bank_outside rankStack
    (start (EncodedGraph.encode g) originalN).stk
    (afterRank g originalN).stk (.inr k) (by
      rintro ⟨j,h⟩
      simp [rankStack] at h)]
  fin_cases k <;> rfl

private theorem double_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineDoubleUnary.Stack,
      (doubleInitialCfg g).stk k =
        (afterRankHost g originalN).stk (doubleStack k) := by
  intro k
  fin_cases k <;>
    simp [doubleInitialCfg, SourceNormalizationMachineDoubleUnary.cfg,
      doubleStack, afterRankHost_extra, afterRankHost_at]
  exact (SourceNormalizationMachineDecodeRankLocal.final_divisor g originalN).symm

private theorem double_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterRankHost g originalN =
      BitMachineStackEmbedding.cfg doubleStack
        (afterRankHost g originalN).stk Sum.inr doubleControl none
        (doubleInitialCfg g) := by
  have hb := BitMachineStackEmbedding.bank_eq_self doubleStack
    (afterRankHost g originalN).stk (doubleInitialCfg g).stk
    (double_initial_stacks g originalN)
  change (⟨some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan),
    rankControl (afterRank g originalN).var,
    (afterRankHost g originalN).stk⟩ : Config) =
    (⟨some (.inr SourceNormalizationMachineDoubleUnary.Phase.scan),
      doubleControl (doubleInitialCfg g).var,
      BitMachineStackEmbedding.bank doubleStack
        (afterRankHost g originalN).stk (doubleInitialCfg g).stk⟩ : Config)
  rw [hb]
  rfl

/-- Shared-bank physical parsing, repetition, local rank, and unary padded
edge-count doubling. The original SAT variable bank is untouched. -/
theorem decode_double_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ rankBound g originalN + 2 * (g.edges.length + 1) + 2,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg doubleStack
          (afterRankHost g originalN).stk Sum.inr doubleControl none
          (doubleFinalCfg g) := by
  obtain ⟨a,ha,hrank⟩ := rank_stage g hg originalN
  have hdouble := SourceNormalizationMachineDoubleUnary.double_run
    (g.edges.length + 1)
  have hdouble' : SourceNormalizationMachineDoubleUnary.run
      (2 * (g.edges.length + 1) + 2) (doubleInitialCfg g) =
        doubleFinalCfg g := by
    simpa only [doubleInitialCfg, doubleFinalCfg] using hdouble
  obtain ⟨b,hb,hr⟩ := BitMachineStackEmbedding.outputs doubleStack
    (afterRankHost g originalN).stk Sum.inr doubleControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineDoubleUnary.program program double_program_eq
    (doubleInitialCfg g) (2 * (g.edges.length + 1) + 2) (by
      change (SourceNormalizationMachineDoubleUnary.run
        (2 * (g.edges.length + 1) + 2) (doubleInitialCfg g)).l = none
      rw [hdouble']
      rfl)
  change ((advance SourceNormalizationMachineDoubleUnary.program)^[2 *
    (g.edges.length + 1) + 2]) _ = _ at hdouble'
  rw [hdouble'] at hr
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hrank b).trans
    ((congrArg (run b) (double_initial g originalN)).trans
      (by simpa only [run] using hr))

noncomputable def finalHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg doubleStack
    (afterRankHost g originalN).stk Sum.inr doubleControl none
    (doubleFinalCfg g)

theorem final_counter (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (.inr 1) =
      List.replicate (2 * (g.edges.length + 1)) true := by
  change BitMachineStackEmbedding.bank doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk
    (doubleStack 2) = _
  rw [BitMachineStackEmbedding.bank_at doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk 2]
  rfl

theorem final_local_stream (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (.inl (.inr 6)) =
      (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN).stk
        (.inr (4 : Fin 5)) := by
  have hd : ¬ ∃ k : SourceNormalizationMachineDoubleUnary.Stack,
      doubleStack k = (.inl (.inr (6 : Fin 7)) : Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [doubleStack] at hk
  change BitMachineStackEmbedding.bank doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk
    (.inl (.inr (6 : Fin 7)) : Stack) = _
  rw [BitMachineStackEmbedding.bank_outside doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk _ hd]
  rw [afterRankHost_at]
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeRankLocal.rankStack
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankStack
      (.inr (4 : Fin 5))) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeRankLocal.rankStack
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN).stk
    (.inr (4 : Fin 5))]

theorem final_support (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (.inl (.inl (.inl (.inr 2)))) =
      SourceNormalizationNumeric.paddedSupport g := by
  have hd : ¬ ∃ k : SourceNormalizationMachineDoubleUnary.Stack,
      doubleStack k = (.inl (.inl (.inl (.inr (2 : Fin 6)))) : Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [doubleStack] at hk
  change BitMachineStackEmbedding.bank doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk
    (.inl (.inl (.inl (.inr (2 : Fin 6)))) : Stack) = _
  rw [BitMachineStackEmbedding.bank_outside doubleStack
    (afterRankHost g originalN).stk (doubleFinalCfg g).stk _ hd]
  rw [afterRankHost_at]
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeRankLocal.rankStack
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankStack
      (.inl (0 : Fin 5))) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeRankLocal.rankStack
    (SourceNormalizationMachineDecodeRankLocal.afterRepeatHost g originalN).stk
    (SourceNormalizationMachineDecodeRankLocal.rankFinalCfg g originalN).stk
    (.inl (0 : Fin 5))]
  rfl

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeDouble
