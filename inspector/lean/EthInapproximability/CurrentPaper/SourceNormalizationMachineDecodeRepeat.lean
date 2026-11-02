import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCount
import EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream

/-!
# Shared-bank decoding, support/count normalization, and copy-major stream repetition

The retained padded endpoint stream is copied once per physical unary
repetition token. The support vector and original SAT variable count remain
foreign stacks. Endpoint relabelling and graph serialization follow later.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRepeat

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeCount.Stack
abbrev Label := SourceNormalizationMachineDecodeCount.Label ⊕
  SourceNormalizationMachineRepeatStream.Phase
abbrev Control := SourceNormalizationMachineDecodeCount.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def repeatStack : SourceNormalizationMachineRepeatStream.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inr 0
    | 1 => .inl (.inl 0)
    | 2 => .inl (.inl 4)
    | 3 => .inl (.inl 5)
    | _ => .inr 2
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialRepeat : Option Bool := none
def afterCountControl : SourceNormalizationMachineDecodeCount.Control :=
  SourceNormalizationMachineDecodeCount.countControl
    (false,())
def countControl (v : SourceNormalizationMachineDecodeCount.Control) : Control :=
  (v,initialRepeat)
def repeatControl (v : Option Bool) : Control :=
  (afterCountControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl countControl Prod.fst
      (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
      (SourceNormalizationMachineDecodeCount.program l)
  | .inr l => BitMachineStackEmbedding.stmt repeatStack Sum.inr
      repeatControl Prod.snd none
      (SourceNormalizationMachineRepeatStream.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeCount.start graphBits originalN).l.map Sum.inl,
    countControl (SourceNormalizationMachineDecodeCount.start graphBits originalN).var,
    (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk⟩

private theorem count_program_eq (l : SourceNormalizationMachineDecodeCount.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl countControl Prod.fst
      (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
      (SourceNormalizationMachineDecodeCount.program l) := rfl

private theorem repeat_program_eq (l : SourceNormalizationMachineRepeatStream.Phase) :
    program (.inr l) = BitMachineStackEmbedding.stmt repeatStack Sum.inr
      repeatControl Prod.snd none
      (SourceNormalizationMachineRepeatStream.program l) := rfl

noncomputable def afterCount (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodeCount.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    Sum.inr SourceNormalizationMachineDecodeCount.countControl none
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN)

private theorem count_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk
      Sum.inl countControl
      (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
      (SourceNormalizationMachineDecodeCount.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk
    (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk
    (SourceNormalizationMachineDecodeCount.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

private theorem decode_count_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13),
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
          (SourceNormalizationMachineDecodeCount.start
            (EncodedGraph.encode g) originalN).stk
          Sum.inl countControl
          (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
          (afterCount g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineDecodeCount.decode_count_run
    g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCount.start
      (EncodedGraph.encode g) originalN).stk
    Sum.inl countControl Prod.fst (by intro v; rfl)
    (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
    SourceNormalizationMachineDecodeCount.program program count_program_eq
    (SourceNormalizationMachineDecodeCount.start (EncodedGraph.encode g) originalN)
    t (by
      change (SourceNormalizationMachineDecodeCount.run t
        (SourceNormalizationMachineDecodeCount.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodeCount.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s) (count_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, afterCount] using hr)

private theorem afterCount_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineCounts.Stack) :
    (afterCount g originalN).stk
      (SourceNormalizationMachineDecodeCount.countStack k) =
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk k

private theorem afterCount_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachineCounts.Stack,
      SourceNormalizationMachineDecodeCount.countStack k = j) :
    (afterCount g originalN).stk j =
      (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodeCount.countStack
    (SourceNormalizationMachineDecodeCount.afterCore g originalN).stk
    (SourceNormalizationMachineDecodeCount.countFinalCfg g originalN).stk j hj

def paddedStream (g : EncodedGraph.Graph) : List Bool :=
  SourceNormalizationMachineDecode.endpointStream g ++
    SourceNormalizationMachineEndpointPad.suffix g.vertices

private theorem endpointStream_append (xs ys : List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs ++ ys) =
      SourceNormalizationMachineMark.endpointStream xs ++
        SourceNormalizationMachineMark.endpointStream ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append,
        SourceNormalizationMachineMark.endpointStream, ih,
        List.append_assoc]

theorem paddedStream_eq_mark (g : EncodedGraph.Graph) :
    paddedStream g =
      SourceNormalizationMachineMark.endpointStream
        (SourceNormalizationNumeric.paddedEndpoints g) := by
  simp only [paddedStream,
    SourceNormalizationMachineDecode.endpointStream_eq_mark,
    SourceNormalizationMachineEndpointPad.suffix,
    SourceNormalizationNumeric.paddedEndpoints,
    endpointStream_append]
  rfl

theorem repeatedStream_copy_major (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRepeatStream.repeated
      (paddedStream g) (SourceNormalizationNumeric.repetitions g originalN) =
    (List.range (SourceNormalizationNumeric.repetitions g originalN)).flatMap
      (fun _ => SourceNormalizationMachineMark.endpointStream
        (SourceNormalizationNumeric.paddedEndpoints g)) := by
  rw [SourceNormalizationMachineRepeatStream.repeated_eq_flatMap_range,
    paddedStream_eq_mark]

private theorem endpointStream_flatMap {α : Type*} (xs : List α)
    (f : α → List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs.flatMap f) =
      xs.flatMap (fun x => SourceNormalizationMachineMark.endpointStream (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [endpointStream_append, ih]

def repeatedIndices (g : EncodedGraph.Graph) (originalN : ℕ) : List ℕ :=
  (List.range (SourceNormalizationNumeric.repetitions g originalN)).flatMap
    (fun _ => SourceNormalizationNumeric.paddedEndpoints g)

theorem repeatedStream_eq_indices (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRepeatStream.repeated
      (paddedStream g) (SourceNormalizationNumeric.repetitions g originalN) =
    SourceNormalizationMachineMark.endpointStream (repeatedIndices g originalN) := by
  rw [repeatedStream_copy_major, repeatedIndices, endpointStream_flatMap]

theorem repeatedIndices_bounded (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∀ u ∈ repeatedIndices g originalN,
      u < (SourceNormalizationNumeric.paddedSupport g).length := by
  intro u hu
  obtain ⟨k, _, hu'⟩ := List.mem_flatMap.mp hu
  exact SourceNormalizationNumeric.paddedEndpoints_bounded g hg u hu'

/-- The mathematical target of the missing physical per-copy rank pass is
exactly the endpoint stream of the numeric copy-major graph. -/
theorem rankedCopiedStream_eq_numeric (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (List.range (SourceNormalizationNumeric.repetitions g originalN)).flatMap
      (fun k => SourceNormalizationMachineRanks.rankedStream
        (SourceNormalizationNumeric.paddedSupport g)
        (k * ((SourceNormalizationNumeric.support g).count true + 2))
        (SourceNormalizationNumeric.paddedEndpoints g)) =
    SourceNormalizationMachineMark.endpointStream
      (SourceNormalizationNumeric.endpoints
        (SourceNormalizationNumeric.numericGraph g originalN)) := by
  unfold SourceNormalizationNumeric.numericGraph SourceNormalizationNumeric.endpoints
  rw [endpointStream_flatMap]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro k hk
  rw [SourceNormalizationNumeric.rankedStream_padded g hg]
  simp [SourceNormalizationNumeric.paddedEdges, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def,
    endpointStream_append, endpointStream_flatMap,
    Nat.add_assoc, Nat.add_comm]

theorem padded_width_eq_numeric (g : EncodedGraph.Graph) :
    (SourceNormalizationNumeric.paddedSupport g).count true =
      (SourceNormalizationNumeric.support g).count true + 2 := by
  simp [SourceNormalizationNumeric.paddedSupport]

private theorem afterCount_stream (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterCount g originalN).stk (.inr 0) = paddedStream g := by
  have hc : ¬ ∃ k : SourceNormalizationMachineCounts.Stack,
      SourceNormalizationMachineDecodeCount.countStack k =
        (.inr 0 : Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeCount.countStack] at hk
  rw [afterCount_outside g originalN _ hc]
  have hcore : ¬ ∃ k : SourceNormalizationMachineCore.Stack,
      SourceNormalizationMachineDecodeCore.coreStack k =
        (.inr 0 : Stack) := by
    rintro ⟨k,hk⟩
    fin_cases k <;> simp [SourceNormalizationMachineDecodeCore.coreStack] at hk
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
    (.inr 0 : Stack) = _
  rw [BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
    (.inr 0 : Stack) hcore]
  change (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 2) = _
  change BitMachineStackEmbedding.bank
    SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    (SourceNormalizationMachineDecodePad.padded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 2) = _
  rw [BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    (SourceNormalizationMachineDecodePad.padded g originalN).stk 2]
  rfl

def repeatInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRepeatStream.Config :=
  SourceNormalizationMachineRepeatStream.cfg
    (some .next) none (paddedStream g) []
    (List.replicate (SourceNormalizationNumeric.repetitions g originalN) true)
    [] (List.replicate originalN true)

def repeatFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRepeatStream.Config :=
  SourceNormalizationMachineRepeatStream.cfg none none
    (paddedStream g) [] []
    (SourceNormalizationMachineRepeatStream.repeated (paddedStream g)
      (SourceNormalizationNumeric.repetitions g originalN))
    (List.replicate originalN true)

private theorem repeat_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineRepeatStream.Stack,
      (repeatInitialCfg g originalN).stk k =
        (afterCount g originalN).stk (repeatStack k) := by
  intro k
  fin_cases k <;> simp [repeatInitialCfg,
    SourceNormalizationMachineRepeatStream.cfg, repeatStack]
  · exact (afterCount_stream g originalN).symm
  · have h := afterCount_at g originalN (.inl (0 : Fin 6))
    simpa [SourceNormalizationMachineDecodeCount.countStack,
      SourceNormalizationMachineDecodeCount.countFinalCfg,
      SourceNormalizationMachineCounts.cfg] using h.symm
  · have h := afterCount_at g originalN (.inl (4 : Fin 6))
    simpa [SourceNormalizationMachineDecodeCount.countStack,
      SourceNormalizationMachineDecodeCount.countFinalCfg,
      SourceNormalizationMachineCounts.cfg,
      SourceNormalizationNumeric.repetitions] using h.symm
  · have h := afterCount_at g originalN (.inl (5 : Fin 6))
    simpa [SourceNormalizationMachineDecodeCount.countStack,
      SourceNormalizationMachineDecodeCount.countFinalCfg,
      SourceNormalizationMachineCounts.cfg] using h.symm
  · have h := afterCount_at g originalN (.inr (0 : Fin 3))
    simpa [SourceNormalizationMachineDecodeCount.countStack,
      SourceNormalizationMachineDecodeCount.countFinalCfg,
      SourceNormalizationMachineCounts.cfg] using h.symm

private theorem repeat_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCount.start
        (EncodedGraph.encode g) originalN).stk
      Sum.inl countControl
      (some (.inr SourceNormalizationMachineRepeatStream.Phase.next))
      (afterCount g originalN) =
    BitMachineStackEmbedding.cfg repeatStack (afterCount g originalN).stk
      Sum.inr repeatControl none (repeatInitialCfg g originalN) := by
  have hleft : BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCount.start
        (EncodedGraph.encode g) originalN).stk
      (afterCount g originalN).stk = (afterCount g originalN).stk := by
    funext k
    exact BitMachineStackEmbedding.bank_at (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCount.start
        (EncodedGraph.encode g) originalN).stk
      (afterCount g originalN).stk k
  have hright := BitMachineStackEmbedding.bank_eq_self repeatStack
    (afterCount g originalN).stk (repeatInitialCfg g originalN).stk
    (repeat_initial_stacks g originalN)
  change (⟨some (.inr SourceNormalizationMachineRepeatStream.Phase.next),
    countControl (afterCount g originalN).var,
    BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCount.start
        (EncodedGraph.encode g) originalN).stk
      (afterCount g originalN).stk⟩ : Config) =
    (⟨some (.inr SourceNormalizationMachineRepeatStream.Phase.next),
      repeatControl (repeatInitialCfg g originalN).var,
      BitMachineStackEmbedding.bank repeatStack
        (afterCount g originalN).stk (repeatInitialCfg g originalN).stk⟩ : Config)
  rw [hleft, hright]
  rfl

/-- One physical program now parses the graph, pads and marks its support,
counts repetitions from the original `n`, then constructs the copy-major
sequence of padded endpoint fields. The fields are not yet relabelled. -/
theorem decode_repeat_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13) +
      (SourceNormalizationNumeric.repetitions g originalN *
        (2 * (paddedStream g).length + 3) + 1),
      run t (start (EncodedGraph.encode g) originalN) =
      BitMachineStackEmbedding.cfg repeatStack (afterCount g originalN).stk
        Sum.inr repeatControl none (repeatFinalCfg g originalN) := by
  obtain ⟨a,ha,hcount⟩ := decode_count_stage g hg originalN
  let r := SourceNormalizationNumeric.repetitions g originalN
  let xs := paddedStream g
  have hrepeat := SourceNormalizationMachineRepeatStream.repeat_run
    xs [] (List.replicate originalN true) r none
  have hrepeat' : SourceNormalizationMachineRepeatStream.run
      (r * (2 * xs.length + 3) + 1) (repeatInitialCfg g originalN) =
      repeatFinalCfg g originalN := by
    simpa only [repeatInitialCfg, repeatFinalCfg, r, xs,
      List.append_nil] using hrepeat
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs repeatStack
    (afterCount g originalN).stk Sum.inr repeatControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineRepeatStream.program program repeat_program_eq
    (repeatInitialCfg g originalN) (r * (2 * xs.length + 3) + 1) (by
      change (SourceNormalizationMachineRepeatStream.run
        (r * (2 * xs.length + 3) + 1)
        (repeatInitialCfg g originalN)).l = none
      rw [hrepeat']
      rfl)
  change ((advance SourceNormalizationMachineRepeatStream.program)^[
    r * (2 * xs.length + 3) + 1]) _ = _ at hrepeat'
  rw [hrepeat'] at hr
  refine ⟨a + s, by simpa only [r, xs] using
    (show a + s ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13) +
      (r * (2 * xs.length + 3) + 1) by omega), ?_⟩
  exact (run_add hcount s).trans
    ((congrArg (run s) (repeat_initial g originalN)).trans
      (by simpa only [run] using hr))

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeRepeat
