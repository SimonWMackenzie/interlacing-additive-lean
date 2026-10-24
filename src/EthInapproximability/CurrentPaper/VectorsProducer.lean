import EthInapproximability.CurrentPaper.VectorsTable
import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode

/-!
# Segment 1c: the vectors table from the literal graph bytes and unary `s`

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

ONE fixed controller (sixteen phases, right-nested
`BitMachineRawSequence`, fifteen charged handoffs) on the bank
`Z = Fin 3 ⊕ MatrixTableWriter.Stack 25`:

* `inp 0` holds the literal guarded graph code
  `true :: EncodedGraph.encode (serializeGraph G)` (retained),
* `inp 1` holds unary `s` (retained),
* `inp 2` holds unary `q2 G s` (SUPPLIED operand word, retained; in the
  level it is the admitted writer-56 word),
* the table-writer region starts blank except an arbitrary old output.

Phases: (1) copy the graph code into the parser input cell; (2) the admitted
parser `SourceNormalizationMachineDecode` (`guarded_valid_run`), embedded so
that its three outputs land directly in the cell bank (endpoint stream in
cell 0, unary `|V|` in cell 8, unary `|E|` in cell 9); (3) copy `|V|` to
cell 7; (4) copy `s`; (5) three pops (`s - 3`); (6) append onto cell 7
(`|V| + (s-3)`); (7) clear; (8-11) four appending copies of `s` (`4s`);
(12) admitted multiplication `4s * |E|` into cell 10; (13) admitted
multiplication `4s * (|V| + (s-3))` into the writer's `rows` counter;
(14) copy `q2` into the `cols` counter; (15) clear `4s`; (16) the admitted
row-major table writer with the checked `EntryVectorsCell.program`
(`VectorsTable.vectors_table`), lifted onto the writer region.

Exit bank exact: inputs unchanged, the writer region is
`ready (graphBank G s) r (q2 G s) 0 0 0 0 [] (rowMajor (vectors G s) ++ output)`.
-/

namespace EthInapproximability.CurrentPaper.VectorsProducer

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

noncomputable section

abbrev TS := MatrixTableWriter.Stack 25
abbrev Z := Fin 3 ⊕ TS

def b (i : Fin 25) : Z := .inr (.inl (.inl i))
def ex (e : MatrixTableWriter.Extra) : Z := .inr (.inr e)
def inp (j : Fin 3) : Z := .inl j

/-! ## Slots and phase programs -/

def sP1 : Fin 3 ↪ Z := ⟨![inp 0, b 11, b 12], by decide⟩
def sP3 : Fin 3 ↪ Z := ⟨![b 8, b 7, b 11], by decide⟩
def sP4 : Fin 3 ↪ Z := ⟨![inp 1, b 12, b 11], by decide⟩
def sP6 : Fin 3 ↪ Z := ⟨![b 12, b 7, b 11], by decide⟩
def sP12 : Fin 6 ↪ Z := ⟨![b 12, b 9, b 11, b 13, b 14, b 10], by decide⟩
def sP13 : Fin 6 ↪ Z := ⟨![b 12, b 7, b 11, b 13, b 14, ex .rows], by decide⟩
def sP14 : Fin 3 ↪ Z := ⟨![inp 2, ex .cols, b 11], by decide⟩

def decFun : SourceNormalizationMachineDecode.Stack → Z
  | .inl k => (![b 11, b 12, b 13, b 14, b 15, b 16, b 17, b 18] : Fin 8 → Z) k
  | .inr j => (![b 8, b 9, b 19, b 20, b 0, b 21] : Fin 6 → Z) j

def decMap : SourceNormalizationMachineDecode.Stack ↪ Z := ⟨decFun, by decide⟩

def decProg := fun l => stackStmt decMap (SourceNormalizationMachineDecode.program l)

def ctl0 : SourceNormalizationMachineDecode.Control :=
  (SourceNormalizationMachineField.initialControl, .count, none)

def pop3 : Unit → TM2.Stmt (fun _ : Z => Bool) Unit (Option Bool)
  | () => .pop (b 12) (fun _ x => x) (.pop (b 12) (fun _ x => x)
      (.pop (b 12) (fun _ x => x) .halt))

def clr12 : EntryVectorsCell.ClearLabel →
    TM2.Stmt (fun _ : Z => Bool) EntryVectorsCell.ClearLabel (Unit × Option Bool)
  | .loop => BitMachineClearBank.clearStep (b 12) EntryVectorsCell.ClearLabel.loop
      EntryVectorsCell.ClearLabel.done
  | .done => .halt

def tInj : TS ↪ Z := ⟨Sum.inr, Sum.inr_injective⟩

def Pw := fun l => stackStmt tInj (MatrixTableWriter.program EntryVectorsCell.program
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) EntryVectorsCell.initControl l)

/-! ## The fixed controller -/

def i16 := (EntryVectorsCell.initControl, (none : Option Bool))
def r15 := BitMachineRawSequence.program clr12 Pw
  (Sum.inr (MatrixTableWriter.Admin.copy .rows)) ((), none) i16
def i15 := ((((), none) : Unit × Option Bool), i16)
def r14 := BitMachineRawSequence.program (copyProgram sP14) r15
  (BitMachineRawSequence.leftLabel EntryVectorsCell.ClearLabel.loop) (none : Option Bool) i15
def i14 := ((none : Option Bool), i15)
def r13 := BitMachineRawSequence.program (multiplyProgram sP13) r14
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false i14
def i13 := (false, i14)
def r12 := BitMachineRawSequence.program (multiplyProgram sP12) r13
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) false i13
def i12 := (false, i13)
def r11 := BitMachineRawSequence.program (copyProgram sP4) r12
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) (none : Option Bool) i12
def i11 := ((none : Option Bool), i12)
def r10 := BitMachineRawSequence.program (copyProgram sP4) r11
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) i11
def i10 := ((none : Option Bool), i11)
def r9 := BitMachineRawSequence.program (copyProgram sP4) r10
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) i10
def i9 := ((none : Option Bool), i10)
def r8 := BitMachineRawSequence.program (copyProgram sP4) r9
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) i9
def i8 := ((none : Option Bool), i9)
def r7 := BitMachineRawSequence.program clr12 r8
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((), none) i8
def i7 := ((((), none) : Unit × Option Bool), i8)
def r6 := BitMachineRawSequence.program (copyProgram sP6) r7
  (BitMachineRawSequence.leftLabel EntryVectorsCell.ClearLabel.loop) (none : Option Bool) i7
def i6 := ((none : Option Bool), i7)
def r5 := BitMachineRawSequence.program pop3 r6
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) i6
def i5 := ((none : Option Bool), i6)
def r4 := BitMachineRawSequence.program (copyProgram sP4) r5
  (BitMachineRawSequence.leftLabel ()) (none : Option Bool) i5
def i4 := ((none : Option Bool), i5)
def r3 := BitMachineRawSequence.program (copyProgram sP3) r4
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) i4
def i3 := ((none : Option Bool), i4)
def r2 := BitMachineRawSequence.program decProg r3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ctl0 i3
def i2 := (ctl0, i3)
/-- The single fixed producer-and-writer controller. -/
def program := BitMachineRawSequence.program (copyProgram sP1) r2
  (BitMachineRawSequence.leftLabel
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate :
      SourceNormalizationMachineDecode.Label)) (none : Option Bool) i2
def initial := ((none : Option Bool), i2)

/-! ## Banks -/

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The literal guarded graph code. -/
def code (G : EndpointGraph V E) : List Bool :=
  true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G)

def rowsN (V : Type) [Fintype V] (s : ℕ) : ℕ :=
  GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s

def inputs (G : EndpointGraph V E) (s : ℕ) : Fin 3 → List Bool :=
  ![code G, List.replicate s true, List.replicate (q2 G s) true]

def B0 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Sum.elim (inputs G s)
    (MatrixTableWriter.ready (K := 25) (fun _ => []) 0 0 0 0 0 0 [] output).contents

def B1 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B0 G s output) (b 11) (code G)

def B2 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (Function.update (Function.update (Function.update (B1 G s output)
    (b 11) []) (b 8) (List.replicate (Fintype.card V) true))
    (b 9) (List.replicate (Fintype.card E) true))
    (b 0) (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges)

def B3 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B2 G s output) (b 7) (List.replicate (Fintype.card V) true)

def B4 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B3 G s output) (b 12) (List.replicate s true)

def B5 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B4 G s output) (b 12) (List.replicate (s - 3) true)

def B6 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B5 G s output) (b 7) (List.replicate (Fintype.card V + (s - 3)) true)

def B7 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B6 G s output) (b 12) []

def B8 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B7 G s output) (b 12) (List.replicate s true)

def B9 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B8 G s output) (b 12) (List.replicate (2 * s) true)

def B10 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B9 G s output) (b 12) (List.replicate (3 * s) true)

def B11 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B10 G s output) (b 12) (List.replicate (4 * s) true)

def B12 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B11 G s output) (b 10) (List.replicate (4 * s * Fintype.card E) true)

def B13 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B12 G s output) (ex .rows) (List.replicate (rowsN V s) true)

def B14 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B13 G s output) (ex .cols) (List.replicate (q2 G s) true)

def B15 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Function.update (B14 G s output) (b 12) []

/-- The writer start data reached by the fifteen producer phases. -/
def readyData (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    MatrixTableWriter.Data 25 :=
  MatrixTableWriter.ready (VectorsTable.graphBank G s) (rowsN V s) (q2 G s) 0 0 0 0 [] output

/-- The exact exit bank of the whole controller. -/
def exitBank (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Sum.elim (inputs G s)
    (readyData G s (MatrixMaterialization.rowMajor (GraphVectors.vectors G s) ++ output)).contents

theorem B15_eq (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    B15 G s output = Sum.elim (inputs G s) (readyData G s output).contents := by
  funext k
  rcases k with k | ((k | k) | k)
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

/-! ## Phase runs -/

theorem p1 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP1))^[2 * (code G).length + 2])
      (⟨some BitMachineCopy.Label.scan, none, B0 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B1 G s output⟩ := by
  have h := FamilyRowGeneric.copy_blank sP1 (B0 G s output) (by rfl) (by rfl)
  have hsrc : B0 G s output (sP1 0) = code G := rfl
  rw [hsrc] at h
  exact h

theorem p2 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ 101 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 3,
      ((advance decProg)^[t])
        (⟨some (Sum.inr SourceNormalizationMachineDecode.Admin.gate), ctl0, B1 G s output⟩ :
          TM2.Cfg (fun _ : Z => Bool) _ _) =
        ⟨none, SourceNormalizationMachineDecode.doneControl true, B2 G s output⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceNormalizationMachineDecode.guarded_valid_run
    (EncodedETHSource.serializeGraph G) (EncodedETHSource.serializeGraph_valid G)
  rw [EncodedETHSource.serializeGraph_edges,
    ← SourceGraphPayloadMachine.endpointStream_graph] at hr
  have hrun := BitMachineStackRun.run decMap (B1 G s output)
    SourceNormalizationMachineDecode.program
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))) t
  unfold SourceNormalizationMachineDecode.run at hr
  rw [hr] at hrun
  have hs : bank decMap (B1 G s output)
      (SourceNormalizationMachineDecode.guardedStart
        (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))).stk =
      B1 G s output := by
    apply bank_eq_self
    intro k
    rcases k with k | k <;> fin_cases k <;> rfl
  have hf : bank decMap (B1 G s output)
      (SourceNormalizationMachineDecode.cfg none
        (SourceNormalizationMachineDecode.doneControl true) {}
        (List.replicate (EncodedETHSource.serializeGraph G).vertices true)
        (List.replicate (Fintype.card E) true) [] []
        (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges)
        []).stk = B2 G s output := by
    funext j
    by_cases hj : ∃ k, decMap k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [bank_at]
      rcases k with k | k <;> fin_cases k <;> rfl
    · rw [bank_outside _ _ _ j hj]
      have hne : ∀ k, j ≠ decMap k := fun k e => hj ⟨k, e.symm⟩
      have h0 : j ≠ b 0 := hne (.inr 4)
      have h9 : j ≠ b 9 := hne (.inr 1)
      have h8 : j ≠ b 8 := hne (.inr 0)
      have h11 : j ≠ b 11 := hne (.inl 0)
      simp only [B2, Function.update_of_ne h0, Function.update_of_ne h9,
        Function.update_of_ne h8, Function.update_of_ne h11]
  have e1 : stackCfg decMap (B1 G s output)
      (SourceNormalizationMachineDecode.guardedStart
        (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))) =
      (⟨some (Sum.inr SourceNormalizationMachineDecode.Admin.gate), ctl0, B1 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) := by
    unfold stackCfg
    rw [hs]
    rfl
  have e2 : stackCfg decMap (B1 G s output)
      (SourceNormalizationMachineDecode.cfg none
        (SourceNormalizationMachineDecode.doneControl true) {}
        (List.replicate (EncodedETHSource.serializeGraph G).vertices true)
        (List.replicate (Fintype.card E) true) [] []
        (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges)
        []) =
      (⟨none, SourceNormalizationMachineDecode.doneControl true, B2 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) := by
    unfold stackCfg
    rw [hf]
    rfl
  rw [e1, e2] at hrun
  exact ⟨t, ht, hrun⟩

theorem p3 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP3))^[2 * Fintype.card V + 2])
      (⟨some BitMachineCopy.Label.scan, none, B2 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B3 G s output⟩ := by
  have h := FamilyRowGeneric.copy_blank sP3 (B2 G s output) (by rfl) (by rfl)
  have hsrc : B2 G s output (sP3 0) = List.replicate (Fintype.card V) true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem p4 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B3 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B4 G s output⟩ := by
  have h := FamilyRowGeneric.copy_blank sP4 (B3 G s output) (by rfl) (by rfl)
  have hsrc : B3 G s output (sP4 0) = List.replicate s true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem pop3_step (S : Z → List Bool) (n : ℕ) (h : S (b 12) = List.replicate n true) :
    ∃ v, advance pop3 (⟨some (), none, S⟩ : TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, v, Function.update S (b 12) (List.replicate (n - 3) true)⟩ := by
  have ht : ((List.replicate n true).tail.tail.tail) = List.replicate (n - 3) true := by
    simp only [List.tail_replicate]
    congr 1
  refine ⟨(List.replicate n true).tail.tail.head?, ?_⟩
  simp only [advance, TM2.step, TM2.stepAux, pop3, Function.update_self,
    Function.update_idem, h, ht, Option.getD_some]

theorem p5 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ v, ((advance pop3)^[1])
      (⟨some (), none, B4 G s output⟩ : TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, v, B5 G s output⟩ := by
  obtain ⟨v, hv⟩ := pop3_step (B4 G s output) s rfl
  exact ⟨v, hv⟩

theorem p6 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP6))^[2 * (s - 3) + 2])
      (⟨some BitMachineCopy.Label.scan, none, B5 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B6 G s output⟩ := by
  have h := copy_run sP6 (B5 G s output) (by rfl)
  have hsrc : B5 G s output (sP6 0) = List.replicate (s - 3) true := rfl
  have htgt : B5 G s output (sP6 1) = List.replicate (Fintype.card V) true := rfl
  rw [hsrc, htgt, List.length_replicate, ← List.replicate_add,
    show s - 3 + Fintype.card V = Fintype.card V + (s - 3) by omega] at h
  exact h

theorem clear12 (S : Z → List Bool) (n : ℕ) (hS : S (b 12) = List.replicate n true) :
    ((advance clr12)^[n + 2])
      (⟨some EntryVectorsCell.ClearLabel.loop, ((), none), S⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, ((), none), Function.update S (b 12) []⟩ := by
  have hp : clr12 EntryVectorsCell.ClearLabel.loop =
      BitMachineClearBank.clearStep (b 12) EntryVectorsCell.ClearLabel.loop
        EntryVectorsCell.ClearLabel.done := rfl
  have h := BitMachineClearBank.clear_one_run clr12 (b 12)
    EntryVectorsCell.ClearLabel.loop EntryVectorsCell.ClearLabel.done hp () S
  rw [hS, List.length_replicate] at h
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply', h]
  rfl

theorem p7 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance clr12)^[(s - 3) + 2])
      (⟨some EntryVectorsCell.ClearLabel.loop, ((), none), B6 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, ((), none), B7 G s output⟩ :=
  clear12 (B6 G s output) (s - 3) rfl

theorem p8 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B7 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B8 G s output⟩ := by
  have h := FamilyRowGeneric.copy_blank sP4 (B7 G s output) (by rfl) (by rfl)
  have hsrc : B7 G s output (sP4 0) = List.replicate s true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem append_s (S : Z → List Bool) (s k : ℕ)
    (hsrc : S (sP4 0) = List.replicate s true)
    (htgt : S (sP4 1) = List.replicate (k * s) true)
    (hscr : S (sP4 2) = []) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, Function.update S (b 12) (List.replicate ((k + 1) * s) true)⟩ := by
  have h := copy_run sP4 S hscr
  rw [hsrc, htgt, List.length_replicate, ← List.replicate_add,
    show s + k * s = (k + 1) * s by ring] at h
  exact h

theorem p9 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B8 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B9 G s output⟩ :=
  append_s (B8 G s output) s 1 rfl (by rw [one_mul]; rfl) rfl

theorem p10 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B9 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B10 G s output⟩ :=
  append_s (B9 G s output) s 2 rfl rfl rfl

theorem p11 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP4))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B10 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B11 G s output⟩ :=
  append_s (B10 G s output) s 3 rfl rfl rfl

theorem p12 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (multiplyProgram sP12))^[MatrixAddressMachine.exactTime (4 * s)
        (Fintype.card E) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B11 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, false, B12 G s output⟩ := by
  have h := multiply_run sP12 (B11 G s output) (4 * s) (Fintype.card E)
    rfl rfl rfl rfl rfl
  have h0 : B11 G s output (sP12 5) = [] := rfl
  rw [h0, List.append_nil] at h
  exact h

theorem p13 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (multiplyProgram sP13))^[MatrixAddressMachine.exactTime (4 * s)
        (Fintype.card V + (s - 3)) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B12 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, false, B13 G s output⟩ := by
  have h := multiply_run sP13 (B12 G s output) (4 * s) (Fintype.card V + (s - 3))
    rfl rfl rfl rfl rfl
  have h0 : B12 G s output (sP13 5) = [] := rfl
  have hr : 4 * s * (Fintype.card V + (s - 3)) = rowsN V s := by
    unfold rowsN GraphVectors.vertexCount GraphVectors.auxiliaryCount
    ring
  rw [h0, List.append_nil, hr] at h
  exact h

theorem p14 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sP14))^[2 * q2 G s + 2])
      (⟨some BitMachineCopy.Label.scan, none, B13 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, none, B14 G s output⟩ := by
  have h := FamilyRowGeneric.copy_blank sP14 (B13 G s output) (by rfl) (by rfl)
  have hsrc : B13 G s output (sP14 0) = List.replicate (q2 G s) true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem p15 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance clr12)^[4 * s + 2])
      (⟨some EntryVectorsCell.ClearLabel.loop, ((), none), B14 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) =
      ⟨none, ((), none), B15 G s output⟩ :=
  clear12 (B14 G s output) (4 * s) rfl

theorem p16 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (rowsN V s) (q2 G s) (VectorsTable.tableT G s),
      ∃ v, ((advance Pw)^[t])
        (⟨some (Sum.inr (MatrixTableWriter.Admin.copy .rows)), i16, B15 G s output⟩ :
          TM2.Cfg (fun _ : Z => Bool) _ _) =
        ⟨none, v, exitBank G s output⟩ := by
  obtain ⟨t, ht, v, hr⟩ := VectorsTable.vectors_table G s output
  have hrun := BitMachineStackRun.run tInj (B15 G s output)
    (MatrixTableWriter.program EntryVectorsCell.program
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) EntryVectorsCell.initControl)
    (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (EntryVectorsCell.initControl, none)
      (readyData G s output)) t
  unfold MatrixTableWriter.run at hr
  unfold readyData rowsN at hrun
  rw [hr] at hrun
  have hs : bank tInj (B15 G s output) (readyData G s output).contents =
      B15 G s output := by
    apply bank_eq_self
    intro k
    rw [B15_eq]
    rfl
  have hf : bank tInj (B15 G s output)
      (readyData G s (MatrixMaterialization.rowMajor (GraphVectors.vectors G s) ++
        output)).contents = exitBank G s output := by
    funext j
    rcases j with j | k
    · rw [bank_outside]
      · rw [B15_eq]
        rfl
      · rintro ⟨k, hk⟩
        cases hk
    · exact bank_at tInj (B15 G s output) _ k
  unfold readyData rowsN at hs hf
  simp only [stackCfg, MatrixTableWriter.cfg, hs, hf] at hrun
  exact ⟨t, ht, v, hrun⟩

/-! ## The composite -/

def producerBound (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  (2 * (code G).length + 2) +
    101 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 3 +
    (2 * Fintype.card V + 2) + (2 * s + 2) + 1 + (2 * (s - 3) + 2) + ((s - 3) + 2) +
    4 * (2 * s + 2) +
    MatrixAddressMachine.exactTime (4 * s) (Fintype.card E) 0 +
    MatrixAddressMachine.exactTime (4 * s) (Fintype.card V + (s - 3)) 0 +
    (2 * q2 G s + 2) + (4 * s + 2) +
    MatrixTableWriter.writerBound (rowsN V s) (q2 G s) (VectorsTable.tableT G s) + 15

theorem vectors_from_graph (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ producerBound G s, ∃ v,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), initial,
          B0 G s output⟩ : TM2.Cfg (fun _ : Z => Bool) _ _) =
        ⟨none, v, exitBank G s output⟩ := by
  obtain ⟨t16, ht16, v16, h16⟩ := p16 G s output
  obtain ⟨u15, hu15, r15'⟩ := BitMachineRawSequence.runs clr12 Pw
    EntryVectorsCell.ClearLabel.loop (Sum.inr (MatrixTableWriter.Admin.copy .rows))
    ((), none) ((), none) i16 v16 (B14 G s output) (B15 G s output) (exitBank G s output)
    (4 * s + 2) t16 (p15 G s output) h16
  obtain ⟨u14, hu14, r14'⟩ := BitMachineRawSequence.runs (copyProgram sP14) r15
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel EntryVectorsCell.ClearLabel.loop)
    none none i15 (((), none), v16) (B13 G s output) (B14 G s output) (exitBank G s output)
    (2 * q2 G s + 2) u15 (p14 G s output) r15'
  obtain ⟨u13, hu13, r13'⟩ := BitMachineRawSequence.runs (multiplyProgram sP13) r14
    MatrixAddressMachine.Label.outer (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    false false i14 (none, (((), none), v16)) (B12 G s output) (B13 G s output)
    (exitBank G s output) _ u14 (p13 G s output) r14'
  obtain ⟨u12, hu12, r12'⟩ := BitMachineRawSequence.runs (multiplyProgram sP12) r13
    MatrixAddressMachine.Label.outer
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    false false i13 (false, (none, (((), none), v16))) (B11 G s output) (B12 G s output)
    (exitBank G s output) _ u13 (p12 G s output) r13'
  obtain ⟨u11, hu11, r11'⟩ := BitMachineRawSequence.runs (copyProgram sP4) r12
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    none none i12 (false, (false, (none, (((), none), v16)))) (B10 G s output)
    (B11 G s output) (exitBank G s output) _ u12 (p11 G s output) r12'
  obtain ⟨u10, hu10, r10'⟩ := BitMachineRawSequence.runs (copyProgram sP4) r11
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none i11 (none, (false, (false, (none, (((), none), v16))))) (B9 G s output)
    (B10 G s output) (exitBank G s output) _ u11 (p10 G s output) r11'
  obtain ⟨u9, hu9, r9'⟩ := BitMachineRawSequence.runs (copyProgram sP4) r10
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none i10 (none, (none, (false, (false, (none, (((), none), v16)))))) (B8 G s output)
    (B9 G s output) (exitBank G s output) _ u10 (p9 G s output) r10'
  obtain ⟨u8, hu8, r8'⟩ := BitMachineRawSequence.runs (copyProgram sP4) r9
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none i9 (none, (none, (none, (false, (false, (none, (((), none), v16)))))))
    (B7 G s output) (B8 G s output) (exitBank G s output) _ u9 (p8 G s output) r9'
  obtain ⟨u7, hu7, r7'⟩ := BitMachineRawSequence.runs clr12 r8
    EntryVectorsCell.ClearLabel.loop (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((), none) ((), none) i8
    (none, (none, (none, (none, (false, (false, (none, (((), none), v16))))))))
    (B6 G s output) (B7 G s output) (exitBank G s output) _ u8 (p7 G s output) r8'
  obtain ⟨u6, hu6, r6'⟩ := BitMachineRawSequence.runs (copyProgram sP6) r7
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel EntryVectorsCell.ClearLabel.loop)
    none none i7
    (((), none), (none, (none, (none, (none, (false, (false, (none, (((), none), v16)))))))))
    (B5 G s output) (B6 G s output) (exitBank G s output) _ u7 (p6 G s output) r7'
  obtain ⟨v5, h5⟩ := p5 G s output
  obtain ⟨u5, hu5, r5'⟩ := BitMachineRawSequence.runs pop3 r6
    () (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none v5 i6
    (none, (((), none), (none, (none, (none, (none, (false, (false, (none,
      (((), none), v16))))))))))
    (B4 G s output) (B5 G s output) (exitBank G s output) 1 u6 h5 r6'
  obtain ⟨u4, hu4, r4'⟩ := BitMachineRawSequence.runs (copyProgram sP4) r5
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel ())
    none none i5
    (none, (none, (((), none), (none, (none, (none, (none, (false, (false, (none,
      (((), none), v16)))))))))))
    (B3 G s output) (B4 G s output) (exitBank G s output) _ u5 (p4 G s output) r5'
  obtain ⟨u3, hu3, r3'⟩ := BitMachineRawSequence.runs (copyProgram sP3) r4
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none i4
    (none, (none, (none, (((), none), (none, (none, (none, (none, (false, (false, (none,
      (((), none), v16))))))))))))
    (B2 G s output) (B3 G s output) (exitBank G s output) _ u4 (p3 G s output) r4'
  obtain ⟨t2, ht2, h2⟩ := p2 G s output
  obtain ⟨u2, hu2, r2'⟩ := BitMachineRawSequence.runs decProg r3
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ctl0 (SourceNormalizationMachineDecode.doneControl true) i3
    (none, (none, (none, (none, (((), none), (none, (none, (none, (none, (false, (false,
      (none, (((), none), v16)))))))))))))
    (B1 G s output) (B2 G s output) (exitBank G s output) t2 u3 h2 r3'
  obtain ⟨u1, hu1, r1'⟩ := BitMachineRawSequence.runs (copyProgram sP1) r2
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (Sum.inr SourceNormalizationMachineDecode.Admin.gate :
        SourceNormalizationMachineDecode.Label))
    none none i2
    (ctl0, (none, (none, (none, (none, (((), none), (none, (none, (none, (none, (false,
      (false, (none, (((), none), v16))))))))))))))
    (B0 G s output) (B1 G s output) (exitBank G s output) _ u2 (p1 G s output) r2'
  refine ⟨u1, ?_, _, r1'⟩
  unfold producerBound
  omega

/-- The output cell of the exit bank is the row-major vectors table in
front of the old output. -/
theorem exit_output (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    exitBank G s output (ex .output) =
      MatrixMaterialization.rowMajor (GraphVectors.vectors G s) ++ output := rfl

#print axioms p2
#print axioms pop3_step
#print axioms B15_eq
#print axioms p16
#print axioms vectors_from_graph
#print axioms exit_output

end
end EthInapproximability.CurrentPaper.VectorsProducer
