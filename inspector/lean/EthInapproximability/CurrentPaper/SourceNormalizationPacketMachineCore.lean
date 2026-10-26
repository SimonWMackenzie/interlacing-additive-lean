import EthInapproximability.CurrentPaper.SourceNormalizationMachineComplete
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-! One canonical two-field branch packet is physically parsed into the
normalizer's graph and original-variable stacks. The same finite program then
serializes those two selected result stacks back into a two-field packet. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCore

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineGraphOutput.Stack ⊕ Fin 3
abbrev Label := BitMachineBankCodec.ParserLabel 2 ⊕
  (SourceNormalizationMachineGraphOutput.Label ⊕ BitMachineBankSerialize.Label 2)
abbrev Control := Option Bool ×
  (SourceNormalizationMachineGraphOutput.Control × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

abbrev graphInputStack : SourceNormalizationMachineGraphOutput.Stack :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (0 : Fin 8)))))))
abbrev originalNStack : SourceNormalizationMachineGraphOutput.Stack :=
  SourceNormalizationMachineGraphCost.originalNStack
noncomputable abbrev resultStack : SourceNormalizationMachineGraphOutput.Stack :=
  SourceNormalizationMachineGraphOutput.finalizerStack 4

def parserStack : BitMachineBankCodec.Stack 2 ↪ Stack where
  toFun
    | .inl k => if k = 0 then .inl originalNStack else .inl graphInputStack
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp [graphInputStack,
            originalNStack, SourceNormalizationMachineGraphCost.originalNStack,
            SourceNormalizationMachineGraphOutput.Stack] at h ⊢
        | inr b => fin_cases a <;> simp at h
    | inr a =>
        cases b with
        | inl b => fin_cases b <;> simp at h
        | inr b => simpa using h

def graphStack : SourceNormalizationMachineGraphOutput.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

noncomputable def serializerStack : BitMachineBankSerialize.Stack 2 ↪ Stack where
  toFun
    | .inl k => if k = 0 then .inl originalNStack else .inl resultStack
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp [originalNStack,
            resultStack, SourceNormalizationMachineGraphOutput.finalizerStack,
            SourceNormalizationMachineGraphCost.originalNStack,
            SourceNormalizationMachineGraphOutput.Stack] at h ⊢
        | inr b => fin_cases a <;> simp at h
    | inr a =>
        cases b with
        | inl b => fin_cases b <;> simp at h
        | inr b => simpa using h

noncomputable def initialGraphControl : SourceNormalizationMachineGraphOutput.Control :=
  (SourceNormalizationMachineGraphOutput.start [] 0).var

noncomputable def parserControl (v : Option Bool) : Control :=
  (v,(initialGraphControl,none))
def graphControl (v : SourceNormalizationMachineGraphOutput.Control) : Control :=
  (some true,(v,none))
noncomputable def serializerControl (v : Option Bool) : Control :=
  (some true,(SourceNormalizationMachineGraphOutput.finalizerControl none,v))

noncomputable def graphInitialLabel : Option Label :=
  (SourceNormalizationMachineGraphOutput.start [] 0).l.map (fun l => .inr (.inl l))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt parserStack Sum.inl
      parserControl Prod.fst graphInitialLabel (BitMachineBankCodec.parser 2 l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt graphStack
      (fun l => .inr (.inl l)) graphControl (fun v => v.2.1)
      (some (.inr (.inr (.emit 0))))
      (SourceNormalizationMachineGraphOutput.program l)
  | .inr (.inr l) => BitMachineStackEmbedding.stmt serializerStack
      (fun l => .inr (.inr l)) serializerControl (fun v => v.2.2)
      none (BitMachineBankSerialize.program 2 l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def entry (packet : List Bool) : Config :=
  BitMachineStackEmbedding.cfg parserStack (fun _ => []) Sum.inl
    parserControl graphInitialLabel
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] [])

noncomputable def afterParse (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg parserStack (fun _ => []) Sum.inl
    parserControl graphInitialLabel
    (BitMachineBankCodec.parserCfg none (some true)
      (SourceOriginalBranchPackets.bank originalN (EncodedGraph.encode g)) [] [] [])

private theorem parser_program_eq (l : BitMachineBankCodec.ParserLabel 2) :
    program (.inl l) = BitMachineStackEmbedding.stmt parserStack Sum.inl
      parserControl Prod.fst graphInitialLabel (BitMachineBankCodec.parser 2 l) := rfl

theorem parse_canonical_run (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∃ t ≤ 5 * ((SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)).length + 1),
      run t (entry (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g))) = afterParse g originalN := by
  let packet := SourceOriginalBranchPackets.packet originalN (EncodedGraph.encode g)
  let bank := SourceOriginalBranchPackets.bank originalN (EncodedGraph.encode g)
  obtain ⟨t,ht,hparse⟩ := BitMachineBankCodec.parser_correct 2 packet []
  have hd : BitMachineBankCodec.decode 2 packet = some bank :=
    SourceOriginalBranchPackets.packet_decode originalN (EncodedGraph.encode g)
  rw [hd] at hparse
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] []) =
    BitMachineBankCodec.parserCfg none (some true) bank [] [] [] at hparse
  have hh := congrArg (fun c => c.l) hparse
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs parserStack
    (fun _ => []) Sum.inl parserControl Prod.fst
    (by intro v; rfl) graphInitialLabel
    (BitMachineBankCodec.parser 2) program parser_program_eq
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] []) t (by simpa only [BitMachineBankCodec.parserRun] using hh)
  refine ⟨u, hu.trans ht, ?_⟩
  change run u (entry packet) = _
  change ((advance program)^[u]) _ = _ at hr
  unfold BitMachineBankCodec.parserRun at hparse
  rw [hparse] at hr
  simpa only [run, entry, afterParse, packet, bank] using hr

private theorem graph_start_shape (graphBits : List Bool) (originalN : ℕ)
    (k : SourceNormalizationMachineGraphOutput.Stack) :
    (SourceNormalizationMachineGraphOutput.start graphBits originalN).stk k =
      if k = graphInputStack then graphBits
      else if k = originalNStack then List.replicate originalN true else [] := by
  fin_cases k <;> simp [SourceNormalizationMachineGraphOutput.start,
    BitMachineInline.cfg,
    SourceNormalizationMachineDecodeWrite.start,
    SourceNormalizationMachineDecodeVertices.start,
    SourceNormalizationMachineDecodeShift.start,
    SourceNormalizationMachineDecodeDouble.start,
    SourceNormalizationMachineDecodeRankLocal.start,
    SourceNormalizationMachineDecodeRepeat.start,
    SourceNormalizationMachineDecodeCount.start,
    SourceNormalizationMachineDecodeCore.start,
    SourceNormalizationMachineDecodePad.start,
    SourceNormalizationMachineDecode.start,
    graphInputStack, originalNStack,
    SourceNormalizationMachineGraphCost.originalNStack]

private theorem afterParse_shape (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineGraphOutput.Stack) :
    (afterParse g originalN).stk (.inl k) =
      if k = graphInputStack then EncodedGraph.encode g
      else if k = originalNStack then List.replicate originalN true else [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  by_cases hgraph : k = graphInputStack
  · subst k
    rw [show (.inl graphInputStack : Stack) =
      parserStack (.inl (1 : Fin 2)) by simp [parserStack]]
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
      SourceOriginalBranchPackets.bank]
  by_cases hn : k = originalNStack
  · subst k
    rw [show (.inl originalNStack : Stack) =
      parserStack (.inl (0 : Fin 2)) by simp [parserStack]]
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
      SourceOriginalBranchPackets.bank, hgraph]
  have hout : ¬ ∃ p : BitMachineBankCodec.Stack 2,
      parserStack p = (.inl k : Stack) := by
    rintro ⟨p,hp⟩
    cases p with
    | inl p =>
        fin_cases p
        · simp [parserStack] at hp
          exact hn hp.symm
        · simp [parserStack] at hp
          exact hgraph hp.symm
    | inr p => simp [parserStack] at hp
  change BitMachineStackEmbedding.bank parserStack _ _ (.inl k) = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
  simp [hgraph, hn]

private theorem graph_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterParse g originalN =
      BitMachineStackEmbedding.cfg graphStack (afterParse g originalN).stk
        (fun l => .inr (.inl l)) graphControl
        (some (.inr (.inr (.emit 0))))
        (SourceNormalizationMachineGraphOutput.start
          (EncodedGraph.encode g) originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self graphStack
    (afterParse g originalN).stk
    (SourceNormalizationMachineGraphOutput.start
      (EncodedGraph.encode g) originalN).stk (by
        intro k
        simpa only [graphStack] using
          (graph_start_shape (EncodedGraph.encode g) originalN k).trans
            (afterParse_shape g originalN k).symm)
  change (⟨graphInitialLabel, parserControl (some true),
      (afterParse g originalN).stk⟩ : Config) =
    ⟨(SourceNormalizationMachineGraphOutput.start
        (EncodedGraph.encode g) originalN).l.map (fun l => .inr (.inl l)),
      graphControl (SourceNormalizationMachineGraphOutput.start
        (EncodedGraph.encode g) originalN).var,
      BitMachineStackEmbedding.bank graphStack (afterParse g originalN).stk
        (SourceNormalizationMachineGraphOutput.start
          (EncodedGraph.encode g) originalN).stk⟩
  rw [hb]
  rfl

noncomputable def afterGraph (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg graphStack (afterParse g originalN).stk
    (fun l => .inr (.inl l)) graphControl
    (some (.inr (.inr (.emit 0))))
    (SourceNormalizationMachineGraphOutput.finalHost g originalN)

private theorem graph_program_eq (l : SourceNormalizationMachineGraphOutput.Label) :
    program (.inr (.inl l)) = BitMachineStackEmbedding.stmt graphStack
      (fun l => .inr (.inl l)) graphControl (fun v => v.2.1)
      (some (.inr (.inr (.emit 0))))
      (SourceNormalizationMachineGraphOutput.program l) := rfl

theorem graph_canonical_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ 10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8,
      run t (afterParse g originalN) = afterGraph g originalN := by
  obtain ⟨t,ht,hr⟩ := SourceNormalizationMachineGraphCost.graph_output_polynomial_run
    g hg originalN
  have hh : (SourceNormalizationMachineGraphOutput.run t
      (SourceNormalizationMachineGraphOutput.start
        (EncodedGraph.encode g) originalN)).l = none := by
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs graphStack
    (afterParse g originalN).stk (fun l => .inr (.inl l))
    graphControl (fun v => v.2.1) (by intro v; rfl)
    (some (.inr (.inr (.emit 0))))
    SourceNormalizationMachineGraphOutput.program program graph_program_eq
    (SourceNormalizationMachineGraphOutput.start
      (EncodedGraph.encode g) originalN) t
    (by simpa only [SourceNormalizationMachineGraphOutput.run] using hh)
  refine ⟨u, hu.trans ht, ?_⟩
  change ((advance program)^[u]) _ = _ at he
  unfold SourceNormalizationMachineGraphOutput.run at hr
  rw [hr] at he
  exact (congrArg (run u) (graph_initial g originalN)).trans he

def resultWord (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) : List Bool :=
  EncodedGraph.encode
    (SourceNormalizationNumericSource.serializeNormalized
      (EncodedETHSource.rawGraph g hg) originalN)

def resultBank (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) : Fin 2 → List Bool :=
  SourceOriginalBranchPackets.bank originalN (resultWord g hg originalN)

private theorem afterGraph_originalN (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterGraph g originalN).stk (.inl originalNStack) =
      List.replicate originalN true := by
  change BitMachineStackEmbedding.bank graphStack _ _
    (graphStack originalNStack) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact SourceNormalizationMachineGraphCost.final_originalN g originalN

private theorem afterGraph_result (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (afterGraph g originalN).stk (.inl resultStack) = resultWord g hg originalN := by
  change BitMachineStackEmbedding.bank graphStack _ _
    (graphStack resultStack) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact SourceNormalizationMachineComplete.final_abstract_output g hg originalN

private theorem afterParse_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Fin 3) : (afterParse g originalN).stk (.inr j) = [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  change BitMachineStackEmbedding.bank parserStack _ _ (parserStack (.inr j)) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]

private theorem afterGraph_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Fin 3) : (afterGraph g originalN).stk (.inr j) = [] := by
  have ho : ¬ ∃ k : SourceNormalizationMachineGraphOutput.Stack,
      graphStack k = (.inr j : Stack) := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr hk
  change BitMachineStackEmbedding.bank graphStack _ _ (.inr j) = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterParse_extra g originalN j

noncomputable def serializerInitial (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) : TM2.Cfg
      (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool) :=
  BitMachineBankSerialize.cfg (some (.emit 0)) none
    (resultBank g hg originalN) [] [] []

private theorem serializer_initial (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    afterGraph g originalN =
      BitMachineStackEmbedding.cfg serializerStack (afterGraph g originalN).stk
        (fun l => .inr (.inr l)) serializerControl none
        (serializerInitial g hg originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self serializerStack
    (afterGraph g originalN).stk (serializerInitial g hg originalN).stk (by
      intro k
      cases k with
      | inl k =>
          fin_cases k
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              SourceOriginalBranchPackets.bank, serializerStack,
              afterGraph_originalN]
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              SourceOriginalBranchPackets.bank, serializerStack,
              afterGraph_result g hg originalN]
      | inr k =>
          simp [serializerInitial, BitMachineBankSerialize.cfg,
            BitMachineBankSerialize.contents, serializerStack,
            afterGraph_extra g originalN k])
  change (⟨some (.inr (.inr (.emit 0))),
      graphControl (SourceNormalizationMachineGraphOutput.finalHost g originalN).var,
      (afterGraph g originalN).stk⟩ : Config) =
    ⟨some (.inr (.inr (.emit 0))), serializerControl none,
      BitMachineStackEmbedding.bank serializerStack (afterGraph g originalN).stk
        (serializerInitial g hg originalN).stk⟩
  rw [hb]
  rfl

private theorem serializer_program_eq (l : BitMachineBankSerialize.Label 2) :
    program (.inr (.inr l)) = BitMachineStackEmbedding.stmt serializerStack
      (fun l => .inr (.inr l)) serializerControl (fun v => v.2.2)
      none (BitMachineBankSerialize.program 2 l) := rfl

noncomputable def afterSerialize (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) (S' : BitMachineBankSerialize.Bank 2) : Config :=
  BitMachineStackEmbedding.cfg serializerStack (afterGraph g originalN).stk
    (fun l => .inr (.inr l)) serializerControl none
    (BitMachineBankSerialize.cfg none none S' [] []
      (SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN)))

theorem serialize_canonical_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ (t : ℕ) (S' : BitMachineBankSerialize.Bank 2),
      t ≤ 2 * (SourceOriginalBranchPackets.packet originalN
        (resultWord g hg originalN)).length + 2 ∧
      run t (afterGraph g originalN) = afterSerialize g hg originalN S' := by
  let S := resultBank g hg originalN
  have hpacket : BitMachineBankSerialize.encode (List.ofFn S) =
      SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN) := by
    rw [SourceOriginalBranchPackets.packet, BitMachineBankCodec.encode_eq_list]
    rfl
  obtain ⟨t,S',ht,hr⟩ := BitMachineBankSerialize.serialize S [] []
  rw [hpacket] at ht hr
  have hh : (BitMachineBankSerialize.run t (serializerInitial g hg originalN)).l = none := by
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none S [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs serializerStack
    (afterGraph g originalN).stk (fun l => .inr (.inr l))
    serializerControl (fun v => v.2.2) (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) program serializer_program_eq
    (serializerInitial g hg originalN) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u,S',hu.trans ht,?_⟩
  change ((advance program)^[u]) _ = _ at he
  unfold BitMachineBankSerialize.run at hr
  have hr' :
      ((advance (BitMachineBankSerialize.program 2))^[t])
        (serializerInitial g hg originalN) =
      BitMachineBankSerialize.cfg none none S' [] []
        (SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN)) := by
    simpa only [serializerInitial, List.append_nil] using hr
  rw [hr'] at he
  exact (congrArg (run u) (serializer_initial g hg originalN)).trans he

theorem final_packet (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) (S' : BitMachineBankSerialize.Bank 2) :
    (afterSerialize g hg originalN S').stk (.inr (2 : Fin 3)) =
      SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN) := by
  change BitMachineStackEmbedding.bank serializerStack _ _
    (serializerStack (.inr (2 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  simp only [run] at h ⊢
  rw [show t + u = u + t by omega, Function.iterate_add_apply, h]

theorem canonical_packet_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤
      5 * ((SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)).length + 1) +
      10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8 +
      2 * (SourceOriginalBranchPackets.packet originalN
        (resultWord g hg originalN)).length + 2,
      (run t (entry (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)))).l = none ∧
      (run t (entry (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)))).stk (.inr (2 : Fin 3)) =
        SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN) := by
  obtain ⟨p,hp,hparse⟩ := parse_canonical_run g originalN
  obtain ⟨q,hq,hgraph⟩ := graph_canonical_run g hg originalN
  obtain ⟨r,S',hr,hserialize⟩ := serialize_canonical_run g hg originalN
  have hpart : run (p + q)
      (entry (SourceOriginalBranchPackets.packet originalN (EncodedGraph.encode g))) =
      afterGraph g originalN := (run_add hparse q).trans hgraph
  have hfull : run (p + q + r)
      (entry (SourceOriginalBranchPackets.packet originalN (EncodedGraph.encode g))) =
      afterSerialize g hg originalN S' := (run_add hpart r).trans hserialize
  refine ⟨p + q + r, by omega, ?_, ?_⟩
  · rw [hfull]
    rfl
  · rw [hfull]
    exact final_packet g hg originalN S'

end EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCore
