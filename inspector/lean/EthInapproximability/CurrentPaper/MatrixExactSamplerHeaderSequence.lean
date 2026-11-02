import EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderBridge
import EthInapproximability.CurrentPaper.SamplerWriterFullSequence

/-!
# Physical sampler followed by exact-instance construction

The two fixed controllers run on one Boolean-stack bank. The sampler writes
both literal family arrays and clears its temporary stacks before the scalar,
matrix, unary-header, and serializer phases begin. The source array and
parameter words are still supplied here; their physical producers are
separate upstream components.
-/

namespace EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderSequence

open Turing BitMachineEncoding
open MatrixExactSamplerHeaderBridge

private def localDecidable :
    DecidableEq MatrixExactComputableUnaryHeaderSequence.Local := inferInstance
private def baseDecidable :
    DecidableEq MatrixExactComputableUnaryHeaderSequence.Base := inferInstance

instance : DecidableEq Stack := by
  letI : DecidableEq MatrixExactComputableUnaryHeaderSequence.Base := baseDecidable
  letI : DecidableEq MatrixExactComputableUnaryHeaderSequence.Local := localDecidable
  dsimp [Stack, MatrixExactSamplerHeaderBridge.Header,
    MatrixExactComputableUnaryHeaderSequence.Stack]
  infer_instance

abbrev SamplerLabel := SamplerWriterFullSequence.Label
abbrev SamplerControl := SamplerWriterFullSequence.Control
abbrev HeaderLabel := MatrixExactComputableUnaryHeaderSequence.Label
abbrev HeaderControl := MatrixExactComputableUnaryHeaderSequence.Control

def samplerProgram (l : SamplerLabel) :
    TM2.Stmt (fun _ : Stack => Bool) SamplerLabel SamplerControl :=
  BitMachineStackEmbedding.stmt samplerSlots id id id none
    (SamplerWriterFullSequence.program l)

def headerProgram (l : HeaderLabel) :
    TM2.Stmt (fun _ : Stack => Bool) HeaderLabel HeaderControl :=
  BitMachineStackEmbedding.stmt headerSlots id id id none
    (MatrixExactComputableUnaryHeaderSequence.program l)

def headerStart : HeaderLabel := .inl (.inl (.inl (.inr false)))
def headerIdle : HeaderControl :=
  ((MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
    MatrixExactComputableUnaryHeaderSequence.tailIdle)

def exactStart (s threshold : ℕ) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : Stack → List Bool :=
  startBank (ExactParameters.firstExponent s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5*n)
    threshold (ExecutableExactReduction.payload s e).source
    (SamplerWriterFullSequence.exactFirstBits s)
    (SamplerWriterFullSequence.exactSecondBits s)
    (SamplerWriterFullSequence.firstLength (ExactParameters.firstExponent s))
    (ExactParameters.dimension s * ExactParameters.firstExponent s)

def exactReady (s threshold : ℕ) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : Stack → List Bool :=
  readyBank (ExactParameters.firstExponent s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5*n)
    threshold (ExecutableExactReduction.payload s e)

theorem run_sampler (s threshold : ℕ) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    ∃ t ≤ SamplerWriterFullSequence.totalCost
      (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
      (ExactParameters.secondOrder s) (ExactParameters.dimension s)
      (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5*n)
      (ExecutableExactReduction.payload s e).source
      (SamplerWriterFullSequence.exactFirstBits s)
      (SamplerWriterFullSequence.exactSecondBits s)
      (ExactConstruction.sourceVectors (ExactParameters.dimension s) e),
      ((advance samplerProgram)^[t])
        (⟨some SamplerWriterFullSequence.startLabel,
          SamplerWriterFullSequence.startControl, exactStart s threshold e⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SamplerLabel SamplerControl) =
        ⟨none, SamplerWriterFullSequence.startControl,
          exactReady s threshold e⟩ := by
  classical
  obtain ⟨u, hu, hr⟩ := SamplerWriterFullSequence.run_payload s e
  have hh : (((advance SamplerWriterFullSequence.program)^[u])
      (⟨some SamplerWriterFullSequence.startLabel,
        SamplerWriterFullSequence.startControl,
        SamplerWriterFullSequence.exactStart s e⟩ :
        TM2.Cfg (fun _ : Sampler => Bool) SamplerLabel SamplerControl)).l = none := by
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs samplerSlots
    (exactStart s threshold e) id id id (by intro v; rfl) none
    SamplerWriterFullSequence.program samplerProgram (by intro l; rfl)
    (⟨some SamplerWriterFullSequence.startLabel,
      SamplerWriterFullSequence.startControl,
      SamplerWriterFullSequence.exactStart s e⟩ :
      TM2.Cfg (fun _ : Sampler => Bool) SamplerLabel SamplerControl) u hh
  rw [hr] at he
  change ((advance samplerProgram)^[t])
      ⟨some SamplerWriterFullSequence.startLabel,
        SamplerWriterFullSequence.startControl,
        BitMachineStackEmbedding.bank samplerSlots (exactStart s threshold e)
          (SamplerWriterFullSequence.exactStart s e)⟩ =
      ⟨none, SamplerWriterFullSequence.startControl,
        BitMachineStackEmbedding.bank samplerSlots (exactStart s threshold e)
          (SamplerWriterFullSequence.exactReady s e)⟩ at he
  refine ⟨t, ht.trans hu, ?_⟩
  simpa only [exactStart, exactReady, SamplerWriterFullSequence.exactStart,
    SamplerWriterFullSequence.exactReady,
    startBank_embedded, readyBank_from_sampler] using he

def threshold (s : ℕ) : ℕ :=
  ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2

def finalBank (S : MatrixExactComputableUnaryHeaderSequence.Stack → List Bool) :
    Stack → List Bool := Sum.elim S (fun _ => [])

theorem finalBank_embedded (s threshold : ℕ) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n)
    (S : MatrixExactComputableUnaryHeaderSequence.Stack → List Bool) :
    BitMachineStackEmbedding.bank headerSlots (exactReady s threshold e) S =
      finalBank S := by
  classical
  funext k
  cases k with
  | inl k => exact BitMachineStackEmbedding.bank_at headerSlots _ S k
  | inr k =>
    rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · intro ⟨j, hj⟩
      cases hj

theorem run_header (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) :
    let e := EncodedGraph.endpoints g hg
    ∃ t ≤
      MatrixExactComputableUnaryHeaderSequence.baseCost
        (ExactParameters.firstExponent s) (ExactParameters.dimension s)
        (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
        (5*g.vertices) +
      MatrixExactComputableUnaryHeaderSequence.conversionCost
        (ExactParameters.dimension s) (ExactParameters.firstListSize s)
        (ExactParameters.secondListSize s) (5*g.vertices) (threshold s) +
      2 * (EncodedCommunication.encodeInstance
        (ExecutableExactReduction.instanceAt s hs e)).length + 4,
      ∃ S : MatrixExactComputableUnaryHeaderSequence.Stack → List Bool,
        ((advance headerProgram)^[t])
          (⟨some headerStart, headerIdle, exactReady s (threshold s) e⟩ :
            TM2.Cfg (fun _ : Stack => Bool) HeaderLabel HeaderControl) =
          ⟨none, headerIdle, finalBank S⟩ ∧
        S (.inl (.inl (.inr .output))) =
          EncodedCommunication.encodeInstance
            (ExecutableExactReduction.instanceAt s hs e) := by
  classical
  dsimp only
  obtain ⟨u, hu, S, hr, ho⟩ :=
    MatrixExactComputableUnaryHeaderSequence.encoded_graph_output s hs g hg
  have hr' : ((advance MatrixExactComputableUnaryHeaderSequence.program)^[u])
      (⟨some headerStart, headerIdle,
        MatrixExactComputableUnaryHeaderSequence.initial
          (ExactParameters.firstExponent s) (ExactParameters.dimension s)
          (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
          (5*g.vertices) (threshold s)
          (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
        TM2.Cfg (fun _ : Header => Bool) HeaderLabel HeaderControl) =
      ⟨none, headerIdle, S⟩ := by
    simpa only [headerStart, headerIdle, threshold] using hr
  have hh : (((advance MatrixExactComputableUnaryHeaderSequence.program)^[u])
      (⟨some headerStart, headerIdle,
        MatrixExactComputableUnaryHeaderSequence.initial
          (ExactParameters.firstExponent s) (ExactParameters.dimension s)
          (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
          (5*g.vertices) (threshold s)
          (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
        TM2.Cfg (fun _ : Header => Bool) HeaderLabel HeaderControl)).l = none := by
    rw [hr']
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs headerSlots
    (exactReady s (threshold s) (EncodedGraph.endpoints g hg))
    id id id (by intro v; rfl) none
    MatrixExactComputableUnaryHeaderSequence.program headerProgram
    (by intro l; rfl)
    (⟨some headerStart, headerIdle,
      MatrixExactComputableUnaryHeaderSequence.initial
        (ExactParameters.firstExponent s) (ExactParameters.dimension s)
        (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
        (5*g.vertices) (threshold s)
        (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
      TM2.Cfg (fun _ : Header => Bool) HeaderLabel HeaderControl) u hh
  rw [hr'] at he
  change ((advance headerProgram)^[t])
      ⟨some headerStart, headerIdle,
        BitMachineStackEmbedding.bank headerSlots
          (exactReady s (threshold s) (EncodedGraph.endpoints g hg))
          (MatrixExactComputableUnaryHeaderSequence.initial
            (ExactParameters.firstExponent s) (ExactParameters.dimension s)
            (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
            (5*g.vertices) (threshold s)
            (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg)))⟩ =
      ⟨none, headerIdle,
        BitMachineStackEmbedding.bank headerSlots
          (exactReady s (threshold s) (EncodedGraph.endpoints g hg)) S⟩ at he
  refine ⟨t, ht.trans ?_, S, ?_, ho⟩
  · simpa only [headerStart, headerIdle, threshold] using hu
  · simp only [exactReady, readyBank_embedded] at he
    change ((advance headerProgram)^[t])
        ⟨some headerStart, headerIdle,
          exactReady s (threshold s) (EncodedGraph.endpoints g hg)⟩ =
        ⟨none, headerIdle,
          BitMachineStackEmbedding.bank headerSlots
            (exactReady s (threshold s) (EncodedGraph.endpoints g hg)) S⟩ at he
    rw [finalBank_embedded] at he
    exact he

abbrev Label := BitMachineRawSequence.Label SamplerLabel HeaderLabel
abbrev Control := BitMachineRawSequence.Control SamplerControl HeaderControl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program samplerProgram headerProgram headerStart
    SamplerWriterFullSequence.startControl headerIdle

def startLabel : Label := .inl SamplerWriterFullSequence.startLabel
def startControl : Control := (SamplerWriterFullSequence.startControl, headerIdle)

def cost (s : ℕ) {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hs : 2 ^ 21 ≤ s) : ℕ :=
  SamplerWriterFullSequence.totalCost
    (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
    (ExactParameters.secondOrder s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5*n)
    (ExecutableExactReduction.payload s e).source
    (SamplerWriterFullSequence.exactFirstBits s)
    (SamplerWriterFullSequence.exactSecondBits s)
    (ExactConstruction.sourceVectors (ExactParameters.dimension s) e) +
  MatrixExactComputableUnaryHeaderSequence.baseCost
    (ExactParameters.firstExponent s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5*n) +
  MatrixExactComputableUnaryHeaderSequence.conversionCost
    (ExactParameters.dimension s) (ExactParameters.firstListSize s)
    (ExactParameters.secondListSize s) (5*n) (threshold s) +
  2 * (EncodedCommunication.encodeInstance
    (ExecutableExactReduction.instanceAt s hs e)).length + 5

/-- One fixed finite Boolean-stack controller executes both sampler calls,
their physical cleanup, all exact matrix entries, unary-header conversion,
and serialization. The starting source and parameter words still require
separate physical producers. -/
theorem encoded_graph_output (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) :
    let e := EncodedGraph.endpoints g hg
    ∃ t ≤ cost s e hs,
      ∃ S : MatrixExactComputableUnaryHeaderSequence.Stack → List Bool,
        ((advance program)^[t])
          (⟨some startLabel, startControl,
            exactStart s (threshold s) e⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          ⟨none, startControl, finalBank S⟩ ∧
        S (.inl (.inl (.inr .output))) =
          EncodedCommunication.encodeInstance
            (ExecutableExactReduction.instanceAt s hs e) := by
  dsimp only
  let e := EncodedGraph.endpoints g hg
  obtain ⟨ts, hts, hrs⟩ := run_sampler s (threshold s) e
  obtain ⟨th, hth, S, hrh, ho⟩ := run_header s hs g hg
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    samplerProgram headerProgram SamplerWriterFullSequence.startLabel headerStart
    SamplerWriterFullSequence.startControl SamplerWriterFullSequence.startControl
    headerIdle headerIdle
    (exactStart s (threshold s) e) (exactReady s (threshold s) e)
    (finalBank S) ts th hrs hrh
  refine ⟨t, ?_, S, ?_, ho⟩
  · unfold cost
    simp only [e] at hts
    omega
  · simpa only [program, startLabel, startControl] using hr

end EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderSequence
