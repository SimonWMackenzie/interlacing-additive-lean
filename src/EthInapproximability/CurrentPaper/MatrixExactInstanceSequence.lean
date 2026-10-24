import EthInapproximability.CurrentPaper.MatrixExactGraphTable
import EthInapproximability.CurrentPaper.MatrixInstanceEncoding

/-! # Literal exact-NP table followed by physical instance-header writing

The table phase and three-word serializer share one finite Boolean-stack bank.
The serializer's output is the table writer's output cell, so no table is
silently copied or supplied a second time. At this stage the three canonical
binary header words are physical input cells. Their conversion from unary
scalar registers is a separate preceding machine obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixExactInstanceSequence

open Turing BitMachineEncoding

abbrev Base := MatrixScalarTableSequence.Stack
abbrev Stack := Base ⊕ Fin 4
abbrev BaseLabel := BitMachineRawSequence.Label
  MatrixScalarParameters.Label MatrixScalarTableSequence.WriterLabel
abbrev BaseControl := BitMachineRawSequence.Control
  MatrixScalarParameters.Control MatrixScalarTableSequence.WriterControl
abbrev HeaderLabel := MatrixInstanceEncoding.Label
abbrev HeaderControl := Option Bool

def baseSlots : Base ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl.inj h⟩

def headerSlots : MatrixInstanceEncoding.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl j => .inr ⟨j.val, by omega⟩
    | .inr j => match j.val with
      | 0 => .inr 3
      | 1 => .inl (.inl (.inr .temp))
      | _ => .inl (.inl (.inr .output)), by decide⟩

def baseProgram (l : BaseLabel) :
    TM2.Stmt (fun _ : Stack => Bool) BaseLabel BaseControl :=
  BitMachineStackEmbedding.stmt baseSlots id id id none
    (MatrixScalarTableSequence.program l)

def headerProgram (l : HeaderLabel) :
    TM2.Stmt (fun _ : Stack => Bool) HeaderLabel HeaderControl :=
  BitMachineStackEmbedding.stmt headerSlots id id id none
    (MatrixInstanceEncoding.program l)

def program :
    BitMachineRawSequence.Label BaseLabel HeaderLabel →
      TM2.Stmt (fun _ : Stack => Bool)
        (BitMachineRawSequence.Label BaseLabel HeaderLabel)
        (BitMachineRawSequence.Control BaseControl HeaderControl) :=
  BitMachineRawSequence.program baseProgram headerProgram (.emit 0)
    (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial) none

def initial (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) : Stack → List Bool :=
  Sum.elim (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data)
    ![rows.bits, cols.bits, threshold.bits, []]

def afterTable (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    Stack → List Bool :=
  Sum.elim (MatrixScalarTableSequence.finalFrame a d N₁ N₂ n data table)
    ![rows.bits, cols.bits, threshold.bits, []]

noncomputable def finished (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (S' : BitMachineBankSerialize.Bank 3) : Stack → List Bool :=
  BitMachineStackEmbedding.bank headerSlots
    (afterTable a d N₁ N₂ n rows cols threshold data table)
    (BitMachineBankSerialize.contents S' [] []
      (EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold ++ table))

theorem finished_output (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (S' : BitMachineBankSerialize.Bank 3) :
    finished a d N₁ N₂ n rows cols threshold data table S'
        (.inl (.inl (.inr .output))) =
      EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold ++ table := by
  change BitMachineStackEmbedding.bank headerSlots _ _
    (headerSlots (.inr 2)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem base_run {a d N₁ N₂ n rows cols threshold : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1) +
        MatrixTableRuntimeBounds.bound a d N₁ N₂ n + 1,
      ∃ state,
        ((advance baseProgram)^[t])
          (⟨some (.inl (.inl (.inr false))),
            (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
            initial a d N₁ N₂ n rows cols threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, (MatrixScalarParameters.idle, state),
            afterTable a d N₁ N₂ n rows cols threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)
              (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
                (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha)⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let table := MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
    (n := n) data ha
  obtain ⟨t, ht, state, hr⟩ :=
    MatrixScalarTableSequence.scalar_write_run ha C₁ C₂ v cap
  have hh : (((advance MatrixScalarTableSequence.program)^[t])
      (⟨some (.inl (.inl (.inr false))),
        (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
        MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data⟩ :
        TM2.Cfg (fun _ : Base => Bool) _ _)).l = none := by rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs baseSlots
    (initial a d N₁ N₂ n rows cols threshold data) id id id (fun _ => rfl) none
    MatrixScalarTableSequence.program baseProgram (fun _ => rfl)
    (⟨some (.inl (.inl (.inr false))),
      (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
      MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data⟩ :
      TM2.Cfg (fun _ : Base => Bool) _ _) t hh
  rw [hr] at he
  have hstart : BitMachineStackEmbedding.bank baseSlots
      (initial a d N₁ N₂ n rows cols threshold data)
      (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data) =
      initial a d N₁ N₂ n rows cols threshold data := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    rfl
  have hfinal : BitMachineStackEmbedding.bank baseSlots
      (initial a d N₁ N₂ n rows cols threshold data)
      (MatrixScalarTableSequence.finalFrame a d N₁ N₂ n data table) =
      afterTable a d N₁ N₂ n rows cols threshold data table := by
    funext k
    cases k with
    | inl j =>
        change BitMachineStackEmbedding.bank baseSlots _ _ (baseSlots j) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
    | inr j =>
        rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · intro ⟨j, hj⟩
          cases hj
  refine ⟨u, hu.trans ht, state, ?_⟩
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hstart] at he
  rw [hfinal] at he
  exact he

theorem header_run (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∃ t ≤ 2 * (EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold).length + 2,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance headerProgram)^[t])
          (⟨some (.emit 0), none,
            afterTable a d N₁ N₂ n rows cols threshold data table⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, none,
            finished a d N₁ N₂ n rows cols threshold data table S'⟩ := by
  obtain ⟨t, S', ht, hr⟩ :=
    MatrixInstanceEncoding.encode_run rows cols threshold [] table []
  have hh : ((MatrixInstanceEncoding.run t
      (MatrixInstanceEncoding.initial rows cols threshold [] table [])).l) = none := by
    rw [hr]; rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs headerSlots
    (afterTable a d N₁ N₂ n rows cols threshold data table) id id id (fun _ => rfl)
    none MatrixInstanceEncoding.program headerProgram (fun _ => rfl)
    (MatrixInstanceEncoding.initial rows cols threshold [] table []) t hh
  change ((advance headerProgram)^[u] _ =
    BitMachineStackEmbedding.cfg headerSlots
      (afterTable a d N₁ N₂ n rows cols threshold data table) id id none
      (MatrixInstanceEncoding.run t
        (MatrixInstanceEncoding.initial rows cols threshold [] table []))) at he
  rw [hr] at he
  have hstart : BitMachineStackEmbedding.bank headerSlots
      (afterTable a d N₁ N₂ n rows cols threshold data table)
      (BitMachineBankSerialize.contents
        (MatrixInstanceEncoding.binaryBank rows cols threshold) [] [] table) =
      afterTable a d N₁ N₂ n rows cols threshold data table := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    cases k with
    | inl j => fin_cases j <;> rfl
    | inr j => fin_cases j <;> rfl
  refine ⟨u, hu.trans ht, S', ?_⟩
  simpa only [MatrixInstanceEncoding.run, MatrixInstanceEncoding.initial,
    BitMachineBankSerialize.cfg, List.append_nil,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hstart, finished] using he

/-- Scalar arithmetic, the entire literal matrix write, and the instance
header are one fixed physical program. Its starting bank contains no table
bits; the three canonical binary header words and payload arrays are genuine
input cells whose production is charged by separate upstream stages. -/
theorem scalar_write_encode_run {a d N₁ N₂ n rows cols threshold : ℕ}
    (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤
      200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1) +
        MatrixTableRuntimeBounds.bound a d N₁ N₂ n + 1 +
        (2 * (EncodedCommunication.natField rows ++
          EncodedCommunication.natField cols ++
          EncodedCommunication.natField threshold).length + 2) + 1,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance program)^[t])
          (⟨some (.inl (.inl (.inl (.inr false)))),
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), none),
            initial a d N₁ N₂ n rows cols threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), none),
            finished a d N₁ N₂ n rows cols threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)
              (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
                (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha) S'⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let table := MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
    (n := n) data ha
  obtain ⟨tb, htb, state, hb⟩ :=
    base_run (rows := rows) (cols := cols) (threshold := threshold) ha C₁ C₂ v cap
  obtain ⟨th, hth, S', hh⟩ :=
    header_run a d N₁ N₂ n rows cols threshold data table
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs baseProgram headerProgram
    (.inl (.inl (.inr false))) (.emit 0)
    (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial)
    (MatrixScalarParameters.idle, state) none none
    (initial a d N₁ N₂ n rows cols threshold data)
    (afterTable a d N₁ N₂ n rows cols threshold data table)
    (finished a d N₁ N₂ n rows cols threshold data table S')
    tb th hb hh
  exact ⟨t, by omega, S', hr⟩

/-- Exact graph-instance specialization. The final output cell is the
complete accepted binary encoding of `ExecutableExactReduction.instanceAt`.
The source and two sampler arrays, five unary scalar inputs, and three binary
header words are still supplied as physical initial cells. -/
theorem encoded_graph_instance (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤
      200 * (2^(ExactParameters.firstExponent s) + ExactParameters.firstExponent s +
        ExactParameters.dimension s + ExactParameters.firstListSize s +
        ExactParameters.secondListSize s + 5*g.vertices +
        (ExactParameters.dimension s * ExactParameters.firstListSize s)^4 + 1) +
        MatrixTableRuntimeBounds.bound (ExactParameters.firstExponent s)
          (ExactParameters.dimension s) (ExactParameters.firstListSize s)
          (ExactParameters.secondListSize s) (5*g.vertices) + 1 +
        (2 * (EncodedCommunication.encodeInstance
          (ExecutableExactReduction.instanceAt s hs (EncodedGraph.endpoints g hg))).length + 2) + 1,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance program)^[t])
          (⟨some (.inl (.inl (.inl (.inr false)))),
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), none),
            initial (ExactParameters.firstExponent s) (ExactParameters.dimension s)
              (ExactParameters.firstListSize s)
              (ExactParameters.secondListSize s) (5*g.vertices)
              (ExactEncodedReduction.rowCount s g.vertices)
              (ExactEncodedReduction.columnCount s)
              (ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2)
              (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), none),
            finished (ExactParameters.firstExponent s) (ExactParameters.dimension s)
              (ExactParameters.firstListSize s)
              (ExactParameters.secondListSize s) (5*g.vertices)
              (ExactEncodedReduction.rowCount s g.vertices)
              (ExactEncodedReduction.columnCount s)
              (ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2)
              (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))
              (ExecutableExactReduction.literalTable s hs (EncodedGraph.endpoints g hg)) S'⟩ := by
  let e := EncodedGraph.endpoints g hg
  have h := scalar_write_encode_run
    (rows := ExactEncodedReduction.rowCount s g.vertices)
    (cols := ExactEncodedReduction.columnCount s)
    (threshold := ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2)
    (ExecutableExactReduction.alphabet_valid s hs)
    (ExecutableExactReduction.firstFamily s)
    (ExecutableExactReduction.secondFamily s)
    (ExactConstruction.sourceVectors (ExactParameters.dimension s) e)
    (ExactConstruction.sourceVectors_cap (ExactParameters.dimension s) e)
  obtain ⟨t, ht, S', hr⟩ := h
  refine ⟨t, ?_, S', ?_⟩
  · have hlen :
        (EncodedCommunication.natField (ExactEncodedReduction.rowCount s g.vertices) ++
          EncodedCommunication.natField (ExactEncodedReduction.columnCount s) ++
          EncodedCommunication.natField
            (ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2)).length ≤
          (EncodedCommunication.encodeInstance
            (ExecutableExactReduction.instanceAt s hs
              (EncodedGraph.endpoints g hg))).length := by
      simp only [EncodedCommunication.encodeInstance,
        ExecutableExactReduction.instanceAt, List.length_append]
      omega
    omega
  · simpa only [ExecutableExactReduction.literalTable,
      ExecutableExactReduction.payload] using hr

end EthInapproximability.CurrentPaper.MatrixExactInstanceSequence
