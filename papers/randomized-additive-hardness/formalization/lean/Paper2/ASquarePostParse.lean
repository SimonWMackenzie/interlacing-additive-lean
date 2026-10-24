import Paper2.ASquareSideWrite
import Paper2.ASquareReadField
import EthInapproximability.CurrentPaper.MatrixBinaryAddress

/-!
# U17 segment 1: the parser of the encoded instance (lane owner:a-square-2)

Private, 26 September 2026. Paper A lock v12 (`01-introduction.tex:92`, `06-reduction.tex:83-86`).

ONE fixed program `parser` on the ambient stack type `Stack = MatrixTableWriter.Stack 10 ⊕ Fin 8`
(the admitted writer's own 20 stacks plus 8 extra stacks). Started on the bank whose writer slot 2
holds the input word `encodeInstance ⟨r, c, thr, bits⟩` and every other stack empty, it halts on the
bank with `unary r`, `unary c`, `bits` in writer slots 0, 1, 2 (exactly the admitted
`SquareWriter.persistentBank r c bits`), all writer counters empty, the reversed threshold payload
`thr.bits.reverse` in extra stack 0, and every other stack empty. Five charged stages, sequenced by
the admitted `BitMachineRawSequence.runs`, each inlined by the admitted stack embedding
(`Unit4Post.embed_run`):

1. `ReadField` (a-square-owner-1, frozen) : slot 2 -> slot 0, leaving `r.bits.reverse`;
2. the admitted `MatrixBinaryAddress` program on (slot 0, x1, x2): Horner binary-to-unary,
   `valueFrom 0 r.bits.reverse = r` (`ReadField.valueFrom_reverse_bits`);
3. `ReadField` : slot 2 -> slot 1;  4. `MatrixBinaryAddress` on (slot 1, x1, x2);
5. `ReadField` : slot 2 -> x0 (the threshold payload, reversed).

No value is computed in finite control and no input is inserted. Does not close a ledger row.
-/

namespace Paper2.ASquare.Post

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post

abbrev WStack := MatrixTableWriter.Stack 10
/-- The ambient stacks: the admitted writer's 20 stacks and 8 extra stacks. -/
abbrev Stack := WStack ⊕ Fin 8

/-- Writer slot `i` (persistent bank of the square writer). -/
abbrev slot (i : Fin 10) : Stack := .inl (.inl (.inl i))
/-- Extra stack `i`. -/
abbrev xs (i : Fin 8) : Stack := .inr i

/-- A persistent bank with three words (the other seven slots empty). A flat case split on the
index value (as `Unit4Post.Exponent.bank13`), so that kernel checks never compare two different
vector literals. -/
def pb (a b c : List Bool) (i : Fin 10) : List Bool :=
  match i.val with
  | 0 => a | 1 => b | 2 => c | _ => []

theorem pb_eq (m n : ℕ) (source : List Bool) :
    pb (List.replicate m true) (List.replicate n true) source =
      Unit4Shell.SquareWriter.persistentBank m n source := by
  funext i
  fin_cases i <;> rfl

/-- Eight extra words (flat case split). -/
def ext (a b c d e f g h : List Bool) (i : Fin 8) : List Bool :=
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h

/-- The ambient bank: writer data and the eight extra stacks. -/
def bank (d : MatrixTableWriter.Data 10) (x : Fin 8 → List Bool) : Stack → List Bool :=
  Sum.elim d.contents x

/-- The parser-phase bank: three persistent words, every writer counter empty. -/
def pbank (a b c : List Bool) (x : Fin 8 → List Bool) : Stack → List Bool :=
  bank (MatrixTableWriter.ready (pb a b c) 0 0 0 0 0 0 [] []) x

def ext0 : Fin 8 → List Bool := ext [] [] [] [] [] [] [] []

/-! ## Embeddings of the component programs -/

def ιRF0 : Fin 2 ↪ Stack := ⟨![slot 2, slot 0], by decide⟩
def ιRF1 : Fin 2 ↪ Stack := ⟨![slot 2, slot 1], by decide⟩
def ιRFx : Fin 2 ↪ Stack := ⟨![slot 2, xs 0], by decide⟩
def ιBA0 : Fin 3 ↪ Stack := ⟨![slot 0, xs 1, xs 2], by decide⟩
def ιBA1 : Fin 3 ↪ Stack := ⟨![slot 1, xs 1, xs 2], by decide⟩

def sRF0 := fun l => BitMachineStackEmbedding.stackStmt ιRF0 (ReadField.program l)
def sRF1 := fun l => BitMachineStackEmbedding.stackStmt ιRF1 (ReadField.program l)
def sRFx := fun l => BitMachineStackEmbedding.stackStmt ιRFx (ReadField.program l)
def sBA0 := fun l => BitMachineStackEmbedding.stackStmt ιBA0 (MatrixBinaryAddress.program l)
def sBA1 := fun l => BitMachineStackEmbedding.stackStmt ιBA1 (MatrixBinaryAddress.program l)

/-! ## The sequenced parser -/

abbrev PL4 := BitMachineRawSequence.Label MatrixBinaryAddress.Label ReadField.Label
abbrev PV4 := BitMachineRawSequence.Control (Bool × Bool) Bool
def pseq4 := BitMachineRawSequence.program sBA1 sRFx .read (false, false) false
def pstart4 : PL4 := BitMachineRawSequence.leftLabel .readBit
def pinit4 : PV4 := ((false, false), false)

abbrev PL3 := BitMachineRawSequence.Label ReadField.Label PL4
abbrev PV3 := BitMachineRawSequence.Control Bool PV4
def pseq3 := BitMachineRawSequence.program sRF1 pseq4 pstart4 false pinit4
def pstart3 : PL3 := BitMachineRawSequence.leftLabel .read
def pinit3 : PV3 := (false, pinit4)

abbrev PL2 := BitMachineRawSequence.Label MatrixBinaryAddress.Label PL3
abbrev PV2 := BitMachineRawSequence.Control (Bool × Bool) PV3
def pseq2 := BitMachineRawSequence.program sBA0 pseq3 pstart3 (false, false) pinit3
def pstart2 : PL2 := BitMachineRawSequence.leftLabel .readBit
def pinit2 : PV2 := ((false, false), pinit3)

abbrev PLabel := BitMachineRawSequence.Label ReadField.Label PL2
abbrev PControl := BitMachineRawSequence.Control Bool PV2
/-- **The parser**: read `r`, expand, read `c`, expand, read `thr`. -/
def parser := BitMachineRawSequence.program sRF0 pseq2 pstart2 false pinit2
def pstart : PLabel := BitMachineRawSequence.leftLabel .read
def pinit : PControl := (false, pinit2)

/-- The embedding side condition over all 28 ambient stacks. -/
macro "amb_out" : tactic => `(tactic| (
  intro j hj
  rcases j with ((k | k) | k) | k
  · fin_cases k <;> first
      | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
  · fin_cases k <;> first
      | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
  · cases k <;> first
      | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
  · fin_cases k <;> first
      | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)))

/-! ## The five stages -/

theorem stage_rf0 (bs rest b : List Bool) (x : Fin 8 → List Bool) (s : Bool) :
    ((advance sRF0)^[2 * bs.length + 1])
        ⟨some .read, s, pbank [] b (EncodedCommunication.field bs ++ rest) x⟩ =
      ⟨none, false, pbank bs.reverse b rest x⟩ := by
  have h := ReadField.read_field bs rest [] s
  rw [List.append_nil] at h
  exact embed_run ιRF0 ReadField.program .read s false
    ![EncodedCommunication.field bs ++ rest, []] ![rest, bs.reverse] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by amb_out)

theorem stage_rf1 (bs rest a : List Bool) (x : Fin 8 → List Bool) (s : Bool) :
    ((advance sRF1)^[2 * bs.length + 1])
        ⟨some .read, s, pbank a [] (EncodedCommunication.field bs ++ rest) x⟩ =
      ⟨none, false, pbank a bs.reverse rest x⟩ := by
  have h := ReadField.read_field bs rest [] s
  rw [List.append_nil] at h
  exact embed_run ιRF1 ReadField.program .read s false
    ![EncodedCommunication.field bs ++ rest, []] ![rest, bs.reverse] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by amb_out)

theorem stage_rfx (bs rest a b : List Bool) (s : Bool) :
    ((advance sRFx)^[2 * bs.length + 1])
        ⟨some .read, s, pbank a b (EncodedCommunication.field bs ++ rest) ext0⟩ =
      ⟨none, false, pbank a b rest (ext bs.reverse [] [] [] [] [] [] [])⟩ := by
  have h := ReadField.read_field bs rest [] s
  rw [List.append_nil] at h
  exact embed_run ιRFx ReadField.program .read s false
    ![EncodedCommunication.field bs ++ rest, []] ![rest, bs.reverse] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by amb_out)

theorem stage_ba0 (n : ℕ) (b rest : List Bool) (s : Bool × Bool) :
    ((advance sBA0)^[MatrixBinaryAddress.workFrom 0 n.bits.reverse])
        ⟨some .readBit, s, pbank n.bits.reverse b rest ext0⟩ =
      ⟨none, (false, false), pbank (List.replicate n true) b rest ext0⟩ := by
  have h := MatrixBinaryAddress.run_correct n.bits.reverse 0 s
  rw [ReadField.valueFrom_reverse_bits] at h
  exact embed_run ιBA0 MatrixBinaryAddress.program .readBit s (false, false)
    (MatrixBinaryAddress.stackContents n.bits.reverse [] [])
    (MatrixBinaryAddress.stackContents (List.replicate n true) [] []) _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by amb_out)

theorem stage_ba1 (n : ℕ) (a rest : List Bool) (s : Bool × Bool) :
    ((advance sBA1)^[MatrixBinaryAddress.workFrom 0 n.bits.reverse])
        ⟨some .readBit, s, pbank a n.bits.reverse rest ext0⟩ =
      ⟨none, (false, false), pbank a (List.replicate n true) rest ext0⟩ := by
  have h := MatrixBinaryAddress.run_correct n.bits.reverse 0 s
  rw [ReadField.valueFrom_reverse_bits] at h
  exact embed_run ιBA1 MatrixBinaryAddress.program .readBit s (false, false)
    (MatrixBinaryAddress.stackContents n.bits.reverse [] [])
    (MatrixBinaryAddress.stackContents (List.replicate n true) [] []) _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by amb_out)

theorem workFrom_le (n : ℕ) :
    MatrixBinaryAddress.workFrom 0 n.bits.reverse ≤ 4 * n + 3 * n.bits.length + 2 := by
  have h := MatrixBinaryAddress.workFrom_bound 0 n.bits.reverse
  rw [ReadField.valueFrom_reverse_bits, List.length_reverse] at h
  omega

/-- The explicit parser clock. -/
def parseBound (r c thr : ℕ) : ℕ :=
  (2 * r.bits.length + 1) + (4 * r + 3 * r.bits.length + 2) + (2 * c.bits.length + 1) +
    (4 * c + 3 * c.bits.length + 2) + (2 * thr.bits.length + 1) + 4

theorem word_split (r c thr : ℕ) (bits : List Bool) :
    EncodedCommunication.encodeInstance ⟨r, c, thr, bits⟩ =
      EncodedCommunication.field r.bits ++ (EncodedCommunication.field c.bits ++
        (EncodedCommunication.field thr.bits ++ bits)) := by
  simp only [EncodedCommunication.encodeInstance, EncodedCommunication.natField,
    List.append_assoc]

/-- **Segment 1 (the parser).** For EVERY `r, c, thr, bits` (no validity needed), the ONE fixed
parser program, started on the bank with the encoded word in writer slot 2 and every other stack
empty, halts within `parseBound r c thr` steps on the bank with `unary r`, `unary c`, `bits` in
writer slots 0, 1, 2, every writer counter empty, `thr.bits.reverse` in extra stack 0 and every
other stack empty. The exit bank is stated exactly; only the final control value is existential. -/
theorem parse_run (r c thr : ℕ) (bits : List Bool) :
    ∃ t ≤ parseBound r c thr, ∃ v,
      ((advance parser)^[t])
        ⟨some pstart, pinit,
          pbank [] [] (EncodedCommunication.encodeInstance ⟨r, c, thr, bits⟩) ext0⟩ =
      ⟨none, v, pbank (List.replicate r true) (List.replicate c true) bits
          (ext thr.bits.reverse [] [] [] [] [] [] [])⟩ := by
  rw [word_split]
  have h1 := stage_rf0 r.bits (EncodedCommunication.field c.bits ++
    (EncodedCommunication.field thr.bits ++ bits)) [] ext0 false
  have h2 := stage_ba0 r [] (EncodedCommunication.field c.bits ++
    (EncodedCommunication.field thr.bits ++ bits)) (false, false)
  have h3 := stage_rf1 c.bits (EncodedCommunication.field thr.bits ++ bits)
    (List.replicate r true) ext0 false
  have h4 := stage_ba1 c (List.replicate r true)
    (EncodedCommunication.field thr.bits ++ bits) (false, false)
  have h5 := stage_rfx thr.bits bits (List.replicate r true) (List.replicate c true) false
  obtain ⟨t4, ht4, e4⟩ := BitMachineRawSequence.runs sBA1 sRFx .readBit .read (false, false)
    (false, false) false false _ _ _ _ _ h4 h5
  obtain ⟨t3, ht3, e3⟩ := BitMachineRawSequence.runs sRF1 pseq4 .read pstart4 false false
    pinit4 _ _ _ _ _ _ h3 e4
  obtain ⟨t2, ht2, e2⟩ := BitMachineRawSequence.runs sBA0 pseq3 .readBit pstart3 (false, false)
    (false, false) pinit3 _ _ _ _ _ _ h2 e3
  obtain ⟨t1, ht1, e1⟩ := BitMachineRawSequence.runs sRF0 pseq2 .read pstart2 false false
    pinit2 _ _ _ _ _ _ h1 e2
  have w1 := workFrom_le r
  have w2 := workFrom_le c
  refine ⟨t1, ?_, _, e1⟩
  unfold parseBound
  omega

#print axioms parse_run

end Paper2.ASquare.Post
