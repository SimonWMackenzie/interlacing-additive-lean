import EthInapproximability.CurrentPaper.MatrixWeightedOrderToEntry
import EthInapproximability.CurrentPaper.MatrixWeightedEntryRuns
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# One finite program for canonical-order preparation and protected writing

The canonical-order prelude is embedded in the writer's physical stack and
handed to the literal protected-table writer by one charged control step.
This owner still begins with all other weighted scalar words and the raw
Stage--4 table supplied, as well as the three unary order-seed counts.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedOrderWriter

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixWeightedOrderPreparation MatrixWeightedEntryController

abbrev Stack := MatrixTableWriter.Stack 64
abbrev WriterLabel := MatrixTableWriter.Label MatrixWeightedEntryController.Label
abbrev WriterControl := MatrixTableWriter.Control MatrixWeightedEntryController.Control
abbrev PreludeLabel := MatrixWeightedOrderPreparation.Label
abbrev PreludeControl := MatrixWeightedOrderPreparation.Control
abbrev Label := BitMachineRawSequence.Label PreludeLabel WriterLabel
abbrev Control := BitMachineRawSequence.Control PreludeControl WriterControl
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def preludeSlots : Fin 64 ↪ Stack :=
  ⟨fun i => .inl (.inl i), by intro i j h; exact Sum.inl.inj (Sum.inl.inj h)⟩

def preludeProgram (l : PreludeLabel) :
    TM2.Stmt (fun _ : Stack => Bool) PreludeLabel PreludeControl :=
  stmt preludeSlots id id id none (MatrixWeightedOrderPreparation.program l)

def writerProgram : WriterLabel →
    TM2.Stmt (fun _ : Stack => Bool) WriterLabel WriterControl :=
  MatrixTableWriter.program MatrixWeightedEntryController.program
    MatrixWeightedEntryController.start MatrixWeightedEntryController.initial

def writerStart : WriterLabel := .inr (.copy .rows)
def writerInitial : WriterControl := (MatrixWeightedEntryController.initial, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program preludeProgram writerProgram
    writerStart MatrixWeightedOrderPreparation.initial writerInitial

def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l, v, S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem prelude_framed (foreign : Stack → List Bool)
    (S T : Fin 64 → List Bool) (n : ℕ)
    (h : MatrixWeightedOrderPreparation.run n
      (MatrixWeightedOrderPreparation.cfg
        (some MatrixWeightedOrderPreparation.start)
        MatrixWeightedOrderPreparation.initial S) =
      MatrixWeightedOrderPreparation.cfg none
        MatrixWeightedOrderPreparation.initial T) :
    ∃ t ≤ n,
      ((advance preludeProgram)^[t])
        ⟨some MatrixWeightedOrderPreparation.start,
          MatrixWeightedOrderPreparation.initial,
          bank preludeSlots foreign S⟩ =
        ⟨none, MatrixWeightedOrderPreparation.initial,
          bank preludeSlots foreign T⟩ := by
  have hhalt :
      (((advance MatrixWeightedOrderPreparation.program)^[n])
        (MatrixWeightedOrderPreparation.cfg
          (some MatrixWeightedOrderPreparation.start)
          MatrixWeightedOrderPreparation.initial S)).l = none := by
    change (MatrixWeightedOrderPreparation.run n
      (MatrixWeightedOrderPreparation.cfg
        (some MatrixWeightedOrderPreparation.start)
        MatrixWeightedOrderPreparation.initial S)).l = none
    rw [h]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    preludeSlots foreign id id id (by intro v; rfl) none
    MatrixWeightedOrderPreparation.program preludeProgram
    (by intro l; rfl)
    (MatrixWeightedOrderPreparation.cfg
      (some MatrixWeightedOrderPreparation.start)
      MatrixWeightedOrderPreparation.initial S) n hhalt
  change ((advance MatrixWeightedOrderPreparation.program)^[n])
      (MatrixWeightedOrderPreparation.cfg
        (some MatrixWeightedOrderPreparation.start)
        MatrixWeightedOrderPreparation.initial S) =
      MatrixWeightedOrderPreparation.cfg none
        MatrixWeightedOrderPreparation.initial T at h
  rw [h] at he
  refine ⟨t, ht, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixWeightedOrderPreparation.cfg] using he

theorem ready_bank_frame (S T : Fin 64 → List Bool)
    (rows cols : ℕ) (output : List Bool) :
    bank preludeSlots
      (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents T =
      (MatrixTableWriter.ready T rows cols 0 0 0 0 [] output).contents := by
  funext k
  cases k with
  | inl cell =>
      cases cell with
      | inl i => exact bank_at preludeSlots _ T i
      | inr i =>
          rw [bank_outside]
          · rfl
          · rintro ⟨j, hj⟩
            cases hj
  | inr extra =>
      rw [bank_outside]
      · rfl
      · rintro ⟨j, hj⟩
        cases hj

/-- Composition takes place on the same physical writer stacks.  The
administrative handoff is one charged transition, not a host-side bank
replacement. -/
theorem composed_runs (S T : Fin 64 → List Bool)
    (rows cols N M : ℕ) (output finalOutput : List Bool)
    (hprep : ∃ n ≤ N,
      MatrixWeightedOrderPreparation.run n
        (MatrixWeightedOrderPreparation.cfg
          (some MatrixWeightedOrderPreparation.start)
          MatrixWeightedOrderPreparation.initial S) =
        MatrixWeightedOrderPreparation.cfg none
          MatrixWeightedOrderPreparation.initial T)
    (hwriter : ∃ m ≤ M, ∃ w,
      MatrixTableWriter.run MatrixWeightedEntryController.program
        MatrixWeightedEntryController.start MatrixWeightedEntryController.initial
        m (MatrixTableWriter.cfg (some writerStart) writerInitial
          (MatrixTableWriter.ready T rows cols 0 0 0 0 [] output)) =
        MatrixTableWriter.cfg none w
          (MatrixTableWriter.ready T rows cols 0 0 0 0 [] finalOutput)) :
    ∃ t ≤ N + M + 1, ∃ w,
      run t (cfg (some (BitMachineRawSequence.leftLabel
          MatrixWeightedOrderPreparation.start))
        (MatrixWeightedOrderPreparation.initial, writerInitial)
        (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents) =
      cfg none (MatrixWeightedOrderPreparation.initial, w)
        (MatrixTableWriter.ready T rows cols 0 0 0 0 [] finalOutput).contents := by
  obtain ⟨n, hn, hpn⟩ := hprep
  obtain ⟨m, hm, w, hwm⟩ := hwriter
  let initialData := MatrixTableWriter.ready S rows cols 0 0 0 0 [] output
  let preparedData := MatrixTableWriter.ready T rows cols 0 0 0 0 [] output
  let finalData := MatrixTableWriter.ready T rows cols 0 0 0 0 [] finalOutput
  obtain ⟨u, hu, hpu⟩ := prelude_framed initialData.contents S T n hpn
  have hstart : bank preludeSlots initialData.contents S = initialData.contents := by
    simpa only [initialData] using ready_bank_frame S S rows cols output
  have hend : bank preludeSlots initialData.contents T = preparedData.contents := by
    simpa only [initialData, preparedData] using
      ready_bank_frame S T rows cols output
  rw [hstart, hend] at hpu
  have hwriter' : ((advance writerProgram)^[m])
      ⟨some writerStart, writerInitial, preparedData.contents⟩ =
      ⟨none, w, finalData.contents⟩ := by
    exact hwm
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    preludeProgram writerProgram
    MatrixWeightedOrderPreparation.start writerStart
    MatrixWeightedOrderPreparation.initial
    MatrixWeightedOrderPreparation.initial writerInitial w
    initialData.contents preparedData.contents finalData.contents
    u m hpu hwriter'
  refine ⟨t, ?_, w, ?_⟩
  · omega
  · exact he

def protectedWord {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    List Bool :=
  MatrixMaterialization.rowMajor (fun x y =>
    Construction.protectedMatrix R a s q L nv nb hs family order vectors cap
      (MatrixWeightedArithmetic.typedColumn
        (MatrixWeightedTable.rawColumnCode' a s q cy)
        (MatrixWeightedTable.diagonalCode a s q cy)
        (Construction.uniformCopies (Y := Fin cy) a s q) x)
      (MatrixWeightedArithmetic.typedRow
        (MatrixWeightedTable.rawRowCode s L nv nb rx order)
        (MatrixWeightedTable.templateCode s L)
        (MatrixWeightedTable.vertexCode nv rx)
        (MatrixWeightedTable.auxiliaryCode nb rx) y))

/-- Canonical order generation and literal protected-table writing now run
inside one fixed program.  The initial bank still visibly supplies the raw
Stage--4 table, unary weighted scalars, and the three order-seed counts. -/
theorem graph_order_write_actual {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (g : ℕ) {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (vectors : Fin (GraphVectors.vertexCount V g +
      GraphVectors.auxiliaryCount g) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s)
    (hcy : 0 < cy)
    (hbin : 2 ≤ MatrixStage4Digits.binBase a s q cy)
    (hrx : 0 < rx) (output : List Bool) :
    let nv := GraphVectors.vertexCount V g
    let nb := GraphVectors.auxiliaryCount g
    let order := GraphVectors.itemOrder G g
    let d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs
      family order vectors cap
    let rows := Fintype.card (Construction.ProtectedColumns a s q (Fin cy))
    let cols := Fintype.card (Construction.ProtectedRows s L nv nb (Fin rx))
    let T := MatrixWeightedEntryCost.commonCost d rows cols order
    ∃ t ≤ prepCost (Fintype.card V) (g - 3) (4 * g) +
        MatrixTableWriter.writerBound rows cols T + 1, ∃ w,
      run t (cfg (some (BitMachineRawSequence.leftLabel
          MatrixWeightedOrderPreparation.start))
        (MatrixWeightedOrderPreparation.initial, writerInitial)
        (MatrixTableWriter.ready
          (sourceBank (persistentBank d) (Fintype.card V) (g - 3) (4 * g))
          rows cols 0 0 0 0 [] output).contents) =
      cfg none (MatrixWeightedOrderPreparation.initial, w)
        (MatrixTableWriter.ready (persistentBank d)
          rows cols 0 0 0 0 []
          (protectedWord R a s q L nv nb hs family order vectors cap ++
            output)).contents := by
  dsimp only
  let nv := GraphVectors.vertexCount V g
  let nb := GraphVectors.auxiliaryCount g
  let order := GraphVectors.itemOrder G g
  let d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs
    family order vectors cap
  let rows := Fintype.card (Construction.ProtectedColumns a s q (Fin cy))
  let cols := Fintype.card (Construction.ProtectedRows s L nv nb (Fin rx))
  let T := MatrixWeightedEntryCost.commonCost d rows cols order
  have horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order := rfl
  have hprep := MatrixWeightedOrderToEntry.graph_order_into_entry G g d horder
  have hwriter := MatrixWeightedEntryRuns.write_actual_protected
    R a s q L nv nb hs family order vectors cap hcy hbin hrx output
  exact composed_runs
    (sourceBank (persistentBank d) (Fintype.card V) (g - 3) (4 * g))
    (persistentBank d) rows cols
    (prepCost (Fintype.card V) (g - 3) (4 * g))
    (MatrixTableWriter.writerBound rows cols T)
    output (protectedWord R a s q L nv nb hs family order vectors cap ++
      output) hprep hwriter

end EthInapproximability.CurrentPaper.MatrixWeightedOrderWriter
