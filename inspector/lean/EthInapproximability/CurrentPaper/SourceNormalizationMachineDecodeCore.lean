import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodePad
import EthInapproximability.CurrentPaper.SourceNormalizationMachineCore

/-!
# Shared-bank graph decoding, endpoint padding, and support marking

The first two stages run as `DecodePad`; the support seed/mark/K2-support
stage is embedded into the same physical bank. In particular the original
SAT variable count and the padded endpoint stream remain on disjoint stacks.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCore

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodePad.Stack
abbrev Label := SourceNormalizationMachineDecodePad.Label ⊕
  SourceNormalizationMachineCore.Label
abbrev Control := SourceNormalizationMachineDecodePad.Control ×
  SourceNormalizationMachineCore.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def coreStack : SourceNormalizationMachineCore.Stack ↪ Stack where
  toFun
    | .inl (.inl k) => match k.val with
      | 0 => .inl (.inr 2)
      | 1 => .inl (.inl 1)
      | 2 => .inl (.inl 2)
      | 3 => .inl (.inl 3)
      | _ => .inr 1
    | .inl (.inr k) => if k.val = 0 then .inl (.inr 4) else .inr 2
    | .inr k => match k.val with
      | 0 => .inl (.inr 0)
      | 1 => .inl (.inl 4)
      | _ => .inl (.inl 5)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialCore : SourceNormalizationMachineCore.Control :=
  SourceNormalizationMachineCore.seedControl none
def afterPadControl : SourceNormalizationMachineDecodePad.Control :=
  SourceNormalizationMachineDecodePad.padControl none
def decodeControl (v : SourceNormalizationMachineDecodePad.Control) : Control :=
  (v,initialCore)
def coreControl (v : SourceNormalizationMachineCore.Control) : Control :=
  (afterPadControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl decodeControl Prod.fst
      (some (.inr (SourceNormalizationMachineCore.seedLabel
        SourceNormalizationMachineSeed.Phase.copy)))
      (SourceNormalizationMachineDecodePad.program l)
  | .inr l => BitMachineStackEmbedding.stmt coreStack Sum.inr
      coreControl Prod.snd none (SourceNormalizationMachineCore.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodePad.start graphBits originalN).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecodePad.start graphBits originalN).var,
    (SourceNormalizationMachineDecodePad.start graphBits originalN).stk⟩

private theorem decode_program_eq (l : SourceNormalizationMachineDecodePad.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl decodeControl Prod.fst
      (some (.inr (SourceNormalizationMachineCore.seedLabel
        SourceNormalizationMachineSeed.Phase.copy)))
      (SourceNormalizationMachineDecodePad.program l) := rfl

private theorem core_program_eq (l : SourceNormalizationMachineCore.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt coreStack Sum.inr
      coreControl Prod.snd none (SourceNormalizationMachineCore.program l) := rfl

noncomputable def decodedPadded (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodePad.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    Sum.inr SourceNormalizationMachineDecodePad.padControl none
    (SourceNormalizationMachineDecodePad.padded g originalN)

private theorem decode_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodePad.start graphBits originalN).stk
      Sum.inl decodeControl
      (some (.inr (SourceNormalizationMachineCore.seedLabel
        SourceNormalizationMachineSeed.Phase.copy)))
      (SourceNormalizationMachineDecodePad.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodePad.start graphBits originalN).stk
    (SourceNormalizationMachineDecodePad.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodePad.start graphBits originalN).stk
    (SourceNormalizationMachineDecodePad.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

private theorem decode_pad_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
          (SourceNormalizationMachineDecodePad.start
            (EncodedGraph.encode g) originalN).stk
          Sum.inl decodeControl
          (some (.inr (SourceNormalizationMachineCore.seedLabel
            SourceNormalizationMachineSeed.Phase.copy)))
          (decodedPadded g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineDecodePad.decode_pad_run g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodePad.start
      (EncodedGraph.encode g) originalN).stk
    Sum.inl decodeControl Prod.fst (by intro v; rfl)
    (some (.inr (SourceNormalizationMachineCore.seedLabel
      SourceNormalizationMachineSeed.Phase.copy)))
    SourceNormalizationMachineDecodePad.program program decode_program_eq
    (SourceNormalizationMachineDecodePad.start (EncodedGraph.encode g) originalN)
    t (by
      change (SourceNormalizationMachineDecodePad.run t
        (SourceNormalizationMachineDecodePad.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodePad.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s) (decode_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, decodedPadded] using hr)

noncomputable def coreInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineCore.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineCore.seedStack
    (SourceNormalizationMachineCore.seedForeign g.vertices []
      (SourceNormalizationMachineMark.endpointStream
        (SourceNormalizationNumeric.endpoints g))
      (List.replicate originalN true))
    SourceNormalizationMachineCore.seedLabel
    SourceNormalizationMachineCore.seedControl
    (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
    (SourceNormalizationMachineSeed.cfg (some .copy) none
      (List.replicate g.vertices true) [] [] []
      (List.replicate originalN true))

private theorem coreInitial_bank (g : EncodedGraph.Graph) (originalN : ℕ) :
    (coreInitialCfg g originalN).stk =
      SourceNormalizationMachineCore.seedForeign g.vertices []
        (SourceNormalizationMachineMark.endpointStream
          (SourceNormalizationNumeric.endpoints g))
        (List.replicate originalN true) := by
  let S := SourceNormalizationMachineCore.seedForeign g.vertices []
    (SourceNormalizationMachineMark.endpointStream
      (SourceNormalizationNumeric.endpoints g))
    (List.replicate originalN true)
  have hlocal : ∀ k : SourceNormalizationMachineSeed.Stack,
      (SourceNormalizationMachineSeed.cfg (some .copy) none
        (List.replicate g.vertices true) [] [] []
        (List.replicate originalN true)).stk k =
        S (SourceNormalizationMachineCore.seedStack k) := by
    intro k
    fin_cases k <;> rfl
  exact BitMachineStackEmbedding.bank_eq_self
    SourceNormalizationMachineCore.seedStack S _ hlocal

private theorem padded_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineEndpointPad.Stack) :
    (decodedPadded g originalN).stk
      (SourceNormalizationMachineDecodePad.padStack k) =
    (SourceNormalizationMachineDecodePad.padded g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    (SourceNormalizationMachineDecodePad.padded g originalN).stk k

private theorem padded_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachineEndpointPad.Stack,
      SourceNormalizationMachineDecodePad.padStack k = j) :
    (decodedPadded g originalN).stk j =
      (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN) j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    (SourceNormalizationMachineDecodePad.padded g originalN).stk j hj

private theorem afterDecode_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecode.Stack) :
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN) (.inl k) =
    (SourceNormalizationMachineDecodePad.decoded g).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodePad.decodeStack
    (SourceNormalizationMachineDecodePad.foreign (EncodedGraph.encode g) originalN)
    (SourceNormalizationMachineDecodePad.decoded g).stk k

private theorem padded_field_empty (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineField.Stack) :
    (decodedPadded g originalN).stk (.inl (.inl k)) = [] := by
  have hnot : ¬ ∃ j : SourceNormalizationMachineEndpointPad.Stack,
      SourceNormalizationMachineDecodePad.padStack j =
        (.inl (.inl k) : Stack) := by
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [SourceNormalizationMachineDecodePad.padStack] at hj
  rw [padded_outside g originalN _ hnot,
    afterDecode_at g originalN (.inl k)]
  fin_cases k <;> rfl

private theorem padded_vector_empty (g : EncodedGraph.Graph) (originalN : ℕ) :
    (decodedPadded g originalN).stk (.inl (.inr 2)) = [] := by
  have hnot : ¬ ∃ j : SourceNormalizationMachineEndpointPad.Stack,
      SourceNormalizationMachineDecodePad.padStack j =
        (.inl (.inr 2) : Stack) := by
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [SourceNormalizationMachineDecodePad.padStack] at hj
  rw [padded_outside g originalN _ hnot,
    afterDecode_at g originalN (.inr 2)]
  rfl

private theorem padded_vertices (g : EncodedGraph.Graph) (originalN : ℕ) :
    (decodedPadded g originalN).stk (.inl (.inr 0)) =
      List.replicate g.vertices true := by
  change (decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 0) = _
  rw [padded_at]
  rfl

private theorem padded_stream (g : EncodedGraph.Graph) (originalN : ℕ) :
    (decodedPadded g originalN).stk (.inl (.inr 4)) =
      SourceNormalizationMachineDecode.endpointStream g := by
  change (decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 5) = _
  rw [padded_at]
  rfl

private theorem padded_payload (g : EncodedGraph.Graph) (originalN : ℕ) :
    (decodedPadded g originalN).stk (.inr 1) = [] := by
  change (decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 3) = _
  rw [padded_at]
  rfl

private theorem padded_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (decodedPadded g originalN).stk (.inr 2) =
      List.replicate originalN true := by
  change (decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodePad.padStack 4) = _
  rw [padded_at]
  rfl

private theorem core_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineCore.Stack,
      (coreInitialCfg g originalN).stk k =
        (decodedPadded g originalN).stk (coreStack k) := by
  intro k
  rw [coreInitial_bank]
  fin_cases k <;>
    simp [SourceNormalizationMachineCore.seedForeign, coreStack,
      SourceNormalizationMachineDecode.endpointStream_eq_mark,
      SourceNormalizationNumeric.endpoints,
      padded_field_empty, padded_vector_empty,
      padded_vertices, padded_stream, padded_payload, padded_originalN]

private theorem core_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodePad.start
        (EncodedGraph.encode g) originalN).stk
      Sum.inl decodeControl
      (some (.inr (SourceNormalizationMachineCore.seedLabel
        SourceNormalizationMachineSeed.Phase.copy)))
      (decodedPadded g originalN) =
    BitMachineStackEmbedding.cfg coreStack (decodedPadded g originalN).stk
      Sum.inr coreControl none (coreInitialCfg g originalN) := by
  have hleft := BitMachineStackEmbedding.bank_eq_self
    (Function.Embedding.refl Stack)
    (decodedPadded g originalN).stk
    (decodedPadded g originalN).stk (by intro k; rfl)
  have hright := BitMachineStackEmbedding.bank_eq_self coreStack
    (decodedPadded g originalN).stk
    (coreInitialCfg g originalN).stk (core_initial_stacks g originalN)
  have hleft' : BitMachineStackEmbedding.bank
      (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodePad.start
        (EncodedGraph.encode g) originalN).stk
      (decodedPadded g originalN).stk = (decodedPadded g originalN).stk := by
    funext k
    exact BitMachineStackEmbedding.bank_at (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodePad.start
        (EncodedGraph.encode g) originalN).stk
      (decodedPadded g originalN).stk k
  change (⟨some (.inr (SourceNormalizationMachineCore.seedLabel
    SourceNormalizationMachineSeed.Phase.copy)),
    decodeControl (decodedPadded g originalN).var,
    BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodePad.start
        (EncodedGraph.encode g) originalN).stk
      (decodedPadded g originalN).stk⟩ : Config) =
    (⟨some (.inr (SourceNormalizationMachineCore.seedLabel
      SourceNormalizationMachineSeed.Phase.copy)),
      coreControl (coreInitialCfg g originalN).var,
      BitMachineStackEmbedding.bank coreStack
        (decodedPadded g originalN).stk
        (coreInitialCfg g originalN).stk⟩ : Config)
  rw [hleft', hright]
  rfl

def coreCost (g : EncodedGraph.Graph) : ℕ :=
  (2 * g.vertices + 2) +
    (5 * (SourceNormalizationNumeric.endpoints g).sum +
      5 * (SourceNormalizationNumeric.endpoints g).length + 1) +
    (2 * g.vertices + 4)

noncomputable def coreFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineCore.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineCore.padStack
    (SourceNormalizationMachineCore.padForeign g.vertices
      (SourceNormalizationNumeric.support g) []
      (List.replicate originalN true))
    SourceNormalizationMachineCore.padLabel
    SourceNormalizationMachineCore.padControl none
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true))

private theorem core_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ coreCost g,
      run t (BitMachineStackEmbedding.cfg coreStack
        (decodedPadded g originalN).stk Sum.inr coreControl none
        (coreInitialCfg g originalN)) =
      BitMachineStackEmbedding.cfg coreStack
        (decodedPadded g originalN).stk Sum.inr coreControl none
        (coreFinalCfg g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineCore.support_core_run
    g hg [] (List.replicate originalN true)
  change SourceNormalizationMachineCore.run t (coreInitialCfg g originalN) =
    coreFinalCfg g originalN at he
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs coreStack
    (decodedPadded g originalN).stk Sum.inr coreControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineCore.program program core_program_eq
    (coreInitialCfg g originalN) t (by
      change (SourceNormalizationMachineCore.run t
        (coreInitialCfg g originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineCore.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  simpa only [run, coreInitialCfg, coreFinalCfg, coreCost] using hr

theorem decode_core_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g + coreCost g,
      run t (start (EncodedGraph.encode g) originalN) =
      BitMachineStackEmbedding.cfg coreStack
        (decodedPadded g originalN).stk Sum.inr coreControl none
        (coreFinalCfg g originalN) := by
  obtain ⟨a,ha,hdecode⟩ := decode_pad_stage g hg originalN
  obtain ⟨b,hb,hcore⟩ := core_stage g hg originalN
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hdecode b).trans
    ((congrArg (run b) (core_initial g originalN)).trans hcore)

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCore
