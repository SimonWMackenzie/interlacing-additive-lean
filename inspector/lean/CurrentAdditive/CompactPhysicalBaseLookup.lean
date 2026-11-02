import CurrentAdditive.CompactPhysicalBaseParse

/-! A three-field physical base lookup: the existing parser expands row and
width, the existing Horner machine expands the column, and the existing
row-major callback reads the unchanged packet table. -/

namespace Paper2.CompactPhysicalBaseLookup

open Paper2.CompactRationalPacket Paper2.ASquare.Post
open Paper2.CompactFinCodec
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post
open Turing Turing.TM2.Stmt

def input {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) : List Bool :=
  EncodedCommunication.encodeInstance ⟨i.val, cols, j.val, P.table.bits⟩

theorem input_eq_compact {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    input P i j = (codec rows).encode i ++
      EncodedCommunication.field cols.bits ++
      (codec cols).encode j ++ P.table.bits := by
  have h (bs : List Bool) : frame bs = EncodedCommunication.field bs := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [frame, EncodedCommunication.field, ih]
  simp only [input, EncodedCommunication.encodeInstance,
    EncodedCommunication.natField, codec, h, List.append_assoc]

def ιBAcol : Fin 3 ↪ Stack := ⟨![xs 0, xs 1, xs 2], by decide⟩
def sBAcol := fun l => BitMachineStackEmbedding.stackStmt ιBAcol
  (MatrixBinaryAddress.program l)

theorem stage_col (n : ℕ) (row width source : List Bool)
    (s : Bool × Bool) :
    ((advance sBAcol)^[MatrixBinaryAddress.workFrom 0 n.bits.reverse])
      ⟨some MatrixBinaryAddress.Label.readBit, s,
        pbank row width source (ext n.bits.reverse [] [] [] [] [] [] [])⟩ =
      ⟨none, (false, false),
        pbank row width source (ext (List.replicate n true) [] [] [] [] [] [] [])⟩ := by
  have h := MatrixBinaryAddress.run_correct n.bits.reverse 0 s
  rw [Paper2.ASquare.ReadField.valueFrom_reverse_bits] at h
  exact embed_run ιBAcol MatrixBinaryAddress.program .readBit s (false, false)
    (MatrixBinaryAddress.stackContents n.bits.reverse [] [])
    (MatrixBinaryAddress.stackContents (List.replicate n true) [] []) _ _ _ h
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    (by amb_out)

def ιLookup : MatrixTableLookup.Stack ↪ Stack :=
  ⟨![slot 0, slot 1, xs 0, xs 4, xs 5, xs 6, slot 2, xs 3, xs 7, slot 3],
    by decide⟩

def sLookup := fun l => BitMachineStackEmbedding.stackStmt ιLookup
  (MatrixTableLookup.program l)

theorem stage_lookup {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    ∃ t ≤ 32 * (i.val + cols + j.val + P.table.bits.length + 1) ^ 2,
      ((advance sLookup)^[t])
        ⟨some MatrixTableLookup.start, MatrixTableLookup.initial,
          pbank (List.replicate i.val true) (List.replicate cols true)
            P.table.bits
            (ext (List.replicate j.val true) [] [] [] [] [] [] [])⟩ =
        ⟨none, MatrixTableLookup.initial,
          pbank (List.replicate i.val true) (List.replicate cols true)
            P.table.bits
            (ext (List.replicate j.val true) [] []
              [P.table.matrix i j] [] [] [] [])⟩ := by
  obtain ⟨t, ht, h⟩ := Paper2.PhysicalBaseTableLookup.packet_lookup_run P i j []
  refine ⟨t, ht, ?_⟩
  exact embed_run ιLookup MatrixTableLookup.program MatrixTableLookup.start
    MatrixTableLookup.initial MatrixTableLookup.initial
    (![List.replicate i.val true, List.replicate cols true,
      List.replicate j.val true, [], [], [], P.table.bits, [], [], []])
    (![List.replicate i.val true, List.replicate cols true,
      List.replicate j.val true, [], [], [], P.table.bits,
      [P.table.matrix i j], [], []]) _ _ t h
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
    (by
      intro j hj
      rcases j with ((k | k) | k) | k
      · fin_cases k <;> rfl
      · fin_cases k <;> rfl
      · cases k <;> rfl
      · fin_cases k <;> first
          | rfl
          | exact absurd rfl (hj 7))

abbrev CL := BitMachineRawSequence.Label MatrixBinaryAddress.Label MatrixTableLookup.Label
abbrev CV := BitMachineRawSequence.Control (Bool × Bool) MatrixTableLookup.Control

def colThenLookup := BitMachineRawSequence.program sBAcol sLookup
  MatrixTableLookup.start (false, false) MatrixTableLookup.initial
def colThenLookupStart : CL := BitMachineRawSequence.leftLabel .readBit
def colThenLookupInit : CV := ((false, false), MatrixTableLookup.initial)

abbrev Label := BitMachineRawSequence.Label PLabel CL
abbrev Control := BitMachineRawSequence.Control PControl CV

def program := BitMachineRawSequence.program parser colThenLookup
  colThenLookupStart pinit colThenLookupInit
def start : Label := BitMachineRawSequence.leftLabel pstart
def initial : Control := (pinit, colThenLookupInit)

/-- One fixed Boolean-stack program parses the compact binary row and column
indices, expands the supplied width, and performs the literal table read. -/
theorem lookup_run {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    ∃ t ≤ parseBound i.val cols j.val +
      MatrixBinaryAddress.workFrom 0 j.val.bits.reverse +
      32 * (i.val + cols + j.val + P.table.bits.length + 1) ^ 2 + 2,
      ((advance program)^[t])
        ⟨some start, initial, pbank [] [] (input P i j) ext0⟩ =
      ⟨none, (pinit, ((false, false), MatrixTableLookup.initial)),
        pbank (List.replicate i.val true) (List.replicate cols true)
          P.table.bits
          (ext (List.replicate j.val true) [] []
            [P.table.matrix i j] [] [] [] [])⟩ := by
  obtain ⟨tp, htp, vp, hp⟩ := parse_run i.val cols j.val P.table.bits
  obtain ⟨tl, htl, hl⟩ := stage_lookup P i j
  have hc := stage_col j.val (List.replicate i.val true)
    (List.replicate cols true) P.table.bits (false, false)
  obtain ⟨tc, htc, hc'⟩ := BitMachineRawSequence.runs
    sBAcol sLookup .readBit MatrixTableLookup.start
    (false, false) (false, false) MatrixTableLookup.initial MatrixTableLookup.initial
    _ _ _ _ _ hc hl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    parser colThenLookup pstart colThenLookupStart
    pinit vp colThenLookupInit colThenLookupInit
    _ _ _ _ _ hp hc'
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [program, start, initial, input, colThenLookup] using h

/-- The same fixed program reads a validated raw packet, whose Boolean table
is supplied as data rather than as a proof-bearing matrix function. -/
theorem raw_lookup_run {rows cols : ℕ}
    (R : Paper2.RawRationalPacket.RawPacket rows cols)
    (P : Packet rows cols) (h : R.compile? = some P)
    (i : Fin rows) (j : Fin cols) :
    ∃ t ≤ parseBound i.val cols j.val +
      MatrixBinaryAddress.workFrom 0 j.val.bits.reverse +
      32 * (i.val + cols + j.val + R.bits.length + 1) ^ 2 + 2,
      ((advance program)^[t])
        ⟨some start, initial,
          pbank [] []
            (EncodedCommunication.encodeInstance ⟨i.val, cols, j.val, R.bits⟩)
            ext0⟩ =
      ⟨none, (pinit, ((false, false), MatrixTableLookup.initial)),
        pbank (List.replicate i.val true) (List.replicate cols true)
          R.bits
          (ext (List.replicate j.val true) [] []
            [P.table.matrix i j] [] [] [] [])⟩ := by
  have he := (R.compiled_fields P h).1
  simpa only [he, input] using lookup_run P i j

#print axioms input_eq_compact
#print axioms stage_col
#print axioms stage_lookup
#print axioms lookup_run
#print axioms raw_lookup_run

end Paper2.CompactPhysicalBaseLookup
