import EthInapproximability.CurrentPaper.MatrixScalarWriterFrame
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! # Sequential scalar initialization and literal exact-NP table writing

Both phases are fixed finite Boolean-stack programs on the same bank. The
writer is embedded under one additional persistent stack carrying `n`.
The three payload arrays are physical input cells, not table oracles; their
production from encoded graph bits is a distinct upstream obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixScalarTableSequence

open Turing BitMachineEncoding
open MatrixScalarWriterFrame

abbrev Stack := WriterStack
abbrev WriterLabel := MatrixTableWriter.Label MatrixEntryProgram.Label
abbrev WriterControl := MatrixTableWriter.Control MatrixEntryProgram.Control

def writerSlots : MatrixTableWriter.Stack 51 ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl.inj h⟩

def writerProgram (l : WriterLabel) :
    TM2.Stmt (fun _ : Stack => Bool) WriterLabel WriterControl :=
  BitMachineStackEmbedding.stmt writerSlots id id id none
    (MatrixTableWriter.program MatrixTableRuntime.entryProgram
      MatrixEntryProgram.start MatrixEntryProgram.initial l)

def writerStart : WriterLabel := .inr (.copy .rows)
def writerInitial : WriterControl := (MatrixEntryProgram.initial, none)

def program :
    BitMachineRawSequence.Label MatrixScalarParameters.Label WriterLabel →
      TM2.Stmt (fun _ : Stack => Bool)
        (BitMachineRawSequence.Label MatrixScalarParameters.Label WriterLabel)
        (BitMachineRawSequence.Control MatrixScalarParameters.Control WriterControl) :=
  BitMachineRawSequence.program scalarProgram writerProgram writerStart
    MatrixScalarParameters.idle writerInitial

def finalFrame (a d N₁ N₂ n : ℕ) (data : MatrixMaterialization.ExactBitData)
    (table : List Bool) : Stack → List Bool :=
  Sum.elim
    (MatrixTableWriter.ready (MatrixTableRuntime.persistentBank a d N₁ N₂ data)
      (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 [] table).contents
    (fun _ => List.replicate n true)

/-- Physical writer phase in the combined stack bank. -/
theorem writer_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤ MatrixTableRuntimeBounds.bound a d N₁ N₂ n, ∃ state,
      ((advance writerProgram)^[t])
        (⟨some writerStart, writerInitial,
          postFrame a d N₁ N₂ n (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, state,
          finalFrame a d N₁ N₂ n (MatrixMaterialization.storeBits C₁ C₂ v)
            (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
              (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha)⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let localInput := MatrixTableWriter.cfg (some writerStart) writerInitial
    (post a d N₁ N₂ n data)
  obtain ⟨t, ht, state, hr⟩ := MatrixTableRuntime.write_bitTable ha C₁ C₂ v cap []
  change ((advance (MatrixTableWriter.program MatrixTableRuntime.entryProgram
    MatrixEntryProgram.start MatrixEntryProgram.initial))^[t]) localInput = _ at hr
  have hh : (((advance (MatrixTableWriter.program MatrixTableRuntime.entryProgram
      MatrixEntryProgram.start MatrixEntryProgram.initial))^[t]) localInput).l = none := by
    rw [hr]; rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs writerSlots
    (postFrame a d N₁ N₂ n data) id id id (fun _ => rfl) none
    (MatrixTableWriter.program MatrixTableRuntime.entryProgram
      MatrixEntryProgram.start MatrixEntryProgram.initial)
    writerProgram (fun _ => rfl) localInput t hh
  rw [hr] at he
  have hstart : BitMachineStackEmbedding.cfg writerSlots
      (postFrame a d N₁ N₂ n data) id id none localInput =
      (⟨some writerStart, writerInitial, postFrame a d N₁ N₂ n data⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) := by
    change (⟨some writerStart, writerInitial,
      BitMachineStackEmbedding.bank writerSlots (postFrame a d N₁ N₂ n data)
        (post a d N₁ N₂ n data).contents⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) = _
    rw [BitMachineStackEmbedding.bank_eq_self]
    intro k
    rfl
  have hfinal : BitMachineStackEmbedding.cfg writerSlots
      (postFrame a d N₁ N₂ n data) id id none
      (MatrixTableWriter.cfg (L := MatrixEntryProgram.Label) none state
        (MatrixTableWriter.ready (MatrixTableRuntime.persistentBank a d N₁ N₂ data)
          (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 []
          (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
            (n := n) data ha))) =
      (⟨none, state, finalFrame a d N₁ N₂ n data
        (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
          (n := n) data ha)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) := by
    change (⟨none, state,
      BitMachineStackEmbedding.bank writerSlots (postFrame a d N₁ N₂ n data)
        (MatrixTableWriter.ready (MatrixTableRuntime.persistentBank a d N₁ N₂ data)
          (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 []
          (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
            (n := n) data ha)).contents⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) = _
    apply congrArg (fun S => (⟨none, state, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _))
    funext j
    cases j with
    | inl k =>
        change BitMachineStackEmbedding.bank writerSlots _ _ (writerSlots k) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
    | inr u =>
        rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · intro ⟨k, hk⟩
          cases hk
  refine ⟨u, hu.trans ht, state, ?_⟩
  simp only [List.append_nil] at he
  rw [hstart, hfinal] at he
  exact he

/-- One fixed finite machine performs scalar arithmetic, a single charged
handoff, and the entire row-major exact-NP table write. Its starting bank
contains unary scalar inputs and the three literal payload arrays; it does
not contain precomputed matrix entries. -/
theorem scalar_write_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1) +
        MatrixTableRuntimeBounds.bound a d N₁ N₂ n + 1, ∃ state,
      ((advance program)^[t])
        (⟨some (.inl (.inl (.inr false))),
          (MatrixScalarParameters.idle, writerInitial),
          rawInput a d N₁ N₂ n (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (MatrixScalarParameters.idle, state),
          finalFrame a d N₁ N₂ n (MatrixMaterialization.storeBits C₁ C₂ v)
            (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
              (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha)⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  obtain ⟨ts, hts, hs⟩ := scalar_run_raw ha data
  obtain ⟨tw, htw, state, hw⟩ := writer_run ha C₁ C₂ v cap
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs scalarProgram writerProgram
    (.inl (.inr false)) writerStart MatrixScalarParameters.idle
    MatrixScalarParameters.idle writerInitial state
    (rawInput a d N₁ N₂ n data) (postFrame a d N₁ N₂ n data)
    (finalFrame a d N₁ N₂ n data
      (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
        (n := n) data ha)) ts tw hs hw
  refine ⟨t, ?_, state, ?_⟩
  · omega
  · exact hr

end EthInapproximability.CurrentPaper.MatrixScalarTableSequence
