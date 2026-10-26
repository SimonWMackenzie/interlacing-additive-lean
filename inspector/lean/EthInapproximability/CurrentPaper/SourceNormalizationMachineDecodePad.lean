import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
import EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointPad
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Physical graph decoder followed by K2 endpoint padding

The valid graph parser and padded-stream writer share the vertex and stream
stacks. One external stack holds the original SAT variable count in unary;
the graph input occupies only the decoder's input stack. No graph payload is
duplicated at entry. The padded stream is a separate physical output stack.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodePad

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecode.Stack ⊕ Fin 3
abbrev Label := SourceNormalizationMachineDecode.Label ⊕
  SourceNormalizationMachineEndpointPad.Label
abbrev Control := SourceNormalizationMachineDecode.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def decodeStack : SourceNormalizationMachineDecode.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def padStack : SourceNormalizationMachineEndpointPad.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inr 0)
    | 1 => .inl (.inr 5)
    | 2 => .inr 0
    | 3 => .inr 1
    | 4 => .inr 2
    | 5 => .inl (.inr 4)
    | _ => .inl (.inr 3)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def decodeControl (s : SourceNormalizationMachineDecode.Control) : Control :=
  (s,none)
def padControl (s : Option Bool) : Control :=
  (SourceNormalizationMachineDecode.doneControl true,s)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst
      (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
      (SourceNormalizationMachineDecode.program l)
  | .inr l => BitMachineStackEmbedding.stmt padStack Sum.inr
      padControl Prod.snd none
      (SourceNormalizationMachineEndpointPad.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨some (.inl (.inr SourceNormalizationMachineDecode.Admin.capScan)),
    decodeControl (SourceNormalizationMachineField.initialControl,.count,none),
    Sum.elim (SourceNormalizationMachineDecode.start graphBits).stk
      ![[],[],List.replicate originalN true]⟩

def foreign (graphBits : List Bool) (originalN : ℕ) : Stack → List Bool :=
  Sum.elim (SourceNormalizationMachineDecode.start graphBits).stk
    ![[],[],List.replicate originalN true]

private theorem decode_program_eq (l : SourceNormalizationMachineDecode.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst
      (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
      (SourceNormalizationMachineDecode.program l) := rfl

private theorem pad_program_eq (l : SourceNormalizationMachineEndpointPad.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt padStack Sum.inr
      padControl Prod.snd none
      (SourceNormalizationMachineEndpointPad.program l) := rfl

private theorem decode_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg decodeStack (foreign graphBits originalN)
      Sum.inl decodeControl
      (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
      (SourceNormalizationMachineDecode.start graphBits) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self decodeStack
    (foreign graphBits originalN)
    (SourceNormalizationMachineDecode.start graphBits).stk (by
      intro k
      rfl)
  change (⟨some (.inl (.inr SourceNormalizationMachineDecode.Admin.capScan)),
    decodeControl (SourceNormalizationMachineField.initialControl,.count,none),
    BitMachineStackEmbedding.bank decodeStack (foreign graphBits originalN)
      (SourceNormalizationMachineDecode.start graphBits).stk⟩ : Config) = _
  rw [hb]
  rfl

theorem decode_stage (g : EncodedGraph.Graph) (hg : g.Valid) (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g,
      run t (start (EncodedGraph.encode g) originalN) =
      BitMachineStackEmbedding.cfg decodeStack
        (foreign (EncodedGraph.encode g) originalN) Sum.inl decodeControl
        (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
        (SourceNormalizationMachineDecode.cfg none
          (SourceNormalizationMachineDecode.doneControl true) {}
          (List.replicate g.vertices true)
          (List.replicate g.edges.length true) [] []
          (SourceNormalizationMachineDecode.endpointStream g) []) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineDecode.decode_valid_run g hg
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs decodeStack
    (foreign (EncodedGraph.encode g) originalN)
    Sum.inl decodeControl Prod.fst (by intro v; rfl)
    (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
    SourceNormalizationMachineDecode.program program decode_program_eq
    (SourceNormalizationMachineDecode.start (EncodedGraph.encode g)) t (by
      change (SourceNormalizationMachineDecode.run t
        (SourceNormalizationMachineDecode.start (EncodedGraph.encode g))).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecode.program)^[t])
    (SourceNormalizationMachineDecode.start (EncodedGraph.encode g)) = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s) (decode_initial (EncodedGraph.encode g) originalN).symm).trans hr

def decoded (g : EncodedGraph.Graph) : SourceNormalizationMachineDecode.Config :=
  SourceNormalizationMachineDecode.cfg none
    (SourceNormalizationMachineDecode.doneControl true) {}
    (List.replicate g.vertices true)
    (List.replicate g.edges.length true) [] []
    (SourceNormalizationMachineDecode.endpointStream g) []

noncomputable def afterDecodeBank (g : EncodedGraph.Graph) (originalN : ℕ) : Stack → List Bool :=
  BitMachineStackEmbedding.bank decodeStack
    (foreign (EncodedGraph.encode g) originalN) (decoded g).stk

private theorem pad_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg decodeStack
      (foreign (EncodedGraph.encode g) originalN) Sum.inl decodeControl
      (some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)))
      (decoded g) =
    BitMachineStackEmbedding.cfg padStack (afterDecodeBank g originalN)
      Sum.inr padControl none
      (SourceNormalizationMachineEndpointPad.cfg
        (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
        (List.replicate g.vertices true) [] [] []
        (List.replicate originalN true)
        (SourceNormalizationMachineDecode.endpointStream g) []) := by
  let S := afterDecodeBank g originalN
  have hdec (k : SourceNormalizationMachineDecode.Stack) :
      S (.inl k) = (decoded g).stk k := by
    simpa only [S, afterDecodeBank, decodeStack] using
      (BitMachineStackEmbedding.bank_at decodeStack
        (foreign (EncodedGraph.encode g) originalN) (decoded g).stk k)
  have hextra (j : Fin 3) :
      S (.inr j) = (foreign (EncodedGraph.encode g) originalN) (.inr j) := by
    apply BitMachineStackEmbedding.bank_outside decodeStack
      (foreign (EncodedGraph.encode g) originalN) (decoded g).stk (.inr j)
    simp [decodeStack]
  have hlocal : ∀ k : SourceNormalizationMachineEndpointPad.Stack,
      (SourceNormalizationMachineEndpointPad.cfg
        (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
        (List.replicate g.vertices true) [] [] []
        (List.replicate originalN true)
        (SourceNormalizationMachineDecode.endpointStream g) []).stk k =
      S (padStack k) := by
    intro k
    fin_cases k <;>
      simp [padStack, hdec, hextra, decoded, foreign,
        SourceNormalizationMachineDecode.cfg,
        SourceNormalizationMachineEndpointPad.cfg]
  have hb := BitMachineStackEmbedding.bank_eq_self padStack S _ hlocal
  change (⟨some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)),
    padControl none,S⟩ : Config) =
    (⟨some (.inr (.inl SourceNormalizationMachineK2Stream.Phase.start)),
      padControl none,BitMachineStackEmbedding.bank padStack S
        (SourceNormalizationMachineEndpointPad.cfg
          (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
          (List.replicate g.vertices true) [] [] []
          (List.replicate originalN true)
          (SourceNormalizationMachineDecode.endpointStream g) []).stk⟩ : Config)
  rw [hb]

def padCost (g : EncodedGraph.Graph) : ℕ :=
  (2 * g.vertices + 5) +
    (2 * (SourceNormalizationMachineDecode.endpointStream g).length + 2)

def padded (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineEndpointPad.Config :=
  SourceNormalizationMachineEndpointPad.cfg none none
    (List.replicate g.vertices true) []
    (SourceNormalizationMachineDecode.endpointStream g ++
      SourceNormalizationMachineEndpointPad.suffix g.vertices)
    [] (List.replicate originalN true)
    (SourceNormalizationMachineDecode.endpointStream g) []

private theorem pad_stage (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∃ t ≤ padCost g,
      run t (BitMachineStackEmbedding.cfg padStack (afterDecodeBank g originalN)
        Sum.inr padControl none
        (SourceNormalizationMachineEndpointPad.cfg
          (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
          (List.replicate g.vertices true) [] [] []
          (List.replicate originalN true)
          (SourceNormalizationMachineDecode.endpointStream g) [])) =
      BitMachineStackEmbedding.cfg padStack (afterDecodeBank g originalN)
        Sum.inr padControl none (padded g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineEndpointPad.endpointPad_run
    g.vertices [] (List.replicate originalN true)
    (SourceNormalizationMachineDecode.endpointStream g)
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs padStack
    (afterDecodeBank g originalN) Sum.inr padControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineEndpointPad.program program pad_program_eq
    (SourceNormalizationMachineEndpointPad.cfg
      (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
      (List.replicate g.vertices true) [] [] []
      (List.replicate originalN true)
      (SourceNormalizationMachineDecode.endpointStream g) []) t (by
      change (SourceNormalizationMachineEndpointPad.run t
        (SourceNormalizationMachineEndpointPad.cfg
          (some (.inl SourceNormalizationMachineK2Stream.Phase.start)) none
          (List.replicate g.vertices true) [] [] []
          (List.replicate originalN true)
          (SourceNormalizationMachineDecode.endpointStream g) [])).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineEndpointPad.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  simpa only [run, padded, padCost] using hr

theorem decode_pad_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g + padCost g,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg padStack (afterDecodeBank g originalN)
          Sum.inr padControl none (padded g originalN) := by
  obtain ⟨a,ha,hdecode⟩ := decode_stage g hg originalN
  obtain ⟨b,hb,hpad⟩ := pad_stage g originalN
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hdecode b).trans ((congrArg (run b) (pad_initial g originalN)).trans hpad)

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodePad
