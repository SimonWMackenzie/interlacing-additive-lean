import Paper2.ASquarePostParse
import Paper2.ASquareBits
import EthInapproximability.CurrentPaper.MatrixInstanceEncoding

/-!
# U17 segment 2: the header re-serialization of the square instance (lane owner:a-square-2)

Private, 26 September 2026. Paper A lock v12 (`06-reduction.tex:83-86`: rows = cols = the least
power of two `S = 2^E`, the public integer unchanged).

ONE fixed program `header` on the ambient stack type of `SqParse`. Started on the bank left by the
square writer (writer counters `rows = cols = unary 2^E`, the printed square table `out` on the
writer output stack, the reversed threshold payload in extra stack 0, all other non-persistent stacks
empty), it prepends exactly `natField (2^E) ++ natField (2^E) ++ natField thr` to `out`, in six
charged stages sequenced by the admitted `BitMachineRawSequence.runs`:

1. `Bits.Move` (a-square-owner-1, frozen): x0 -> x5, turning `thr.bits.reverse` into `thr.bits`;
2. `ULog` (a-square-owner-1, frozen) on the rows counter (scratch x1, accumulator x6):
   unary `clog₂ 2^E = E`;  3. `ULog` on the columns counter (scratch x1, accumulator x7);
4. `Bits.PowBits` x6 -> x3: `(2^E).bits`;  5. `Bits.PowBits` x7 -> x4;
6. the admitted serializer `MatrixInstanceEncoding.program` (`encode_run`) on the bank words
   x3, x4, x5, source x2, saved x1, output = the writer output stack.

The only existential scratch of the exit bank is the admitted serializer's consumed three-word bank
`S'` (extra stacks 3, 4, 5; `encode_run` states it existentially). Does not close a ledger row.
-/

namespace Paper2.ASquare.Post

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post

abbrev rowsS : Stack := .inl (.inr .rows)
abbrev colsS : Stack := .inl (.inr .cols)
abbrev outS : Stack := .inl (.inr .output)

/-- The header-phase bank: persistent bank `P`, counters `rw`, `cl`, output `out`. -/
def hbank (P : Fin 10 → List Bool) (rw cl : ℕ) (out : List Bool) (x : Fin 8 → List Bool) :
    Stack → List Bool :=
  bank (MatrixTableWriter.ready P rw cl 0 0 0 0 [] out) x

def ιMV : Fin 2 ↪ Stack := ⟨![xs 0, xs 5], by decide⟩
def ιLG0 : Fin 3 ↪ Stack := ⟨![rowsS, xs 1, xs 6], by decide⟩
def ιLG1 : Fin 3 ↪ Stack := ⟨![colsS, xs 1, xs 7], by decide⟩
def ιPB0 : Fin 2 ↪ Stack := ⟨![xs 6, xs 3], by decide⟩
def ιPB1 : Fin 2 ↪ Stack := ⟨![xs 7, xs 4], by decide⟩
def ιSERfun : MatrixInstanceEncoding.Stack → Stack := Sum.elim ![xs 3, xs 4, xs 5] ![xs 2, xs 1, outS]

theorem ιSER_injective : Function.Injective ιSERfun := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    first | rfl | exact absurd h (by decide)

def ιSER : MatrixInstanceEncoding.Stack ↪ Stack := ⟨ιSERfun, ιSER_injective⟩

def sMV := fun l => BitMachineStackEmbedding.stackStmt ιMV (Bits.Move.program l)
def sLG0 := fun l => BitMachineStackEmbedding.stackStmt ιLG0 (ULog.program l)
def sLG1 := fun l => BitMachineStackEmbedding.stackStmt ιLG1 (ULog.program l)
def sPB0 := fun l => BitMachineStackEmbedding.stackStmt ιPB0 (Bits.PowBits.program l)
def sPB1 := fun l => BitMachineStackEmbedding.stackStmt ιPB1 (Bits.PowBits.program l)
def sSER := fun l => BitMachineStackEmbedding.stackStmt ιSER (MatrixInstanceEncoding.program l)

abbrev HL5 := BitMachineRawSequence.Label Bits.PowBits.Label MatrixInstanceEncoding.Label
abbrev HV5 := BitMachineRawSequence.Control Bool (Option Bool)
def hseq5 := BitMachineRawSequence.program sPB1 sSER (.emit 0) false none
def hstart5 : HL5 := BitMachineRawSequence.leftLabel .init
def hinit5 : HV5 := (false, none)

abbrev HL4 := BitMachineRawSequence.Label Bits.PowBits.Label HL5
abbrev HV4 := BitMachineRawSequence.Control Bool HV5
def hseq4 := BitMachineRawSequence.program sPB0 hseq5 hstart5 false hinit5
def hstart4 : HL4 := BitMachineRawSequence.leftLabel .init
def hinit4 : HV4 := (false, hinit5)

abbrev HL3 := BitMachineRawSequence.Label ULog.Label HL4
abbrev HV3 := BitMachineRawSequence.Control Bool HV4
def hseq3 := BitMachineRawSequence.program sLG1 hseq4 hstart4 false hinit4
def hstart3 : HL3 := BitMachineRawSequence.leftLabel .check
def hinit3 : HV3 := (false, hinit4)

abbrev HL2 := BitMachineRawSequence.Label ULog.Label HL3
abbrev HV2 := BitMachineRawSequence.Control Bool HV3
def hseq2 := BitMachineRawSequence.program sLG0 hseq3 hstart3 false hinit3
def hstart2 : HL2 := BitMachineRawSequence.leftLabel .check
def hinit2 : HV2 := (false, hinit3)

abbrev HLabel := BitMachineRawSequence.Label Bits.Move.Label HL2
abbrev HControl := BitMachineRawSequence.Control (Option Bool) HV2
/-- **The header program**: move, log, log, powbits, powbits, serialize. -/
def header := BitMachineRawSequence.program sMV hseq2 hstart2 none hinit2
def hstart : HLabel := BitMachineRawSequence.leftLabel .mv
def hinit : HControl := (none, hinit2)

theorem bank_inl (d : MatrixTableWriter.Data 10) (x : Fin 8 → List Bool) (k : WStack) :
    bank d x (.inl k) = d.contents k := rfl

theorem bank_inr (d : MatrixTableWriter.Data 10) (x : Fin 8 → List Bool) (i : Fin 8) :
    bank d x (.inr i) = x i := rfl

/-- The embedding side condition over all 28 ambient stacks, without ever unifying two different
extra-stack vectors (the ambient bank is first split by `bank_inl` / `bank_inr`). -/
macro "hdr_out" : tactic => `(tactic| (
  intro j hj
  rcases j with ((k | k) | k) | k <;> simp only [hbank, bank_inl, bank_inr] <;>
    (first | fin_cases k | cases k) <;> first
      | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)))

macro "hdr_out2" : tactic => `(tactic| (
  intro j hj
  rcases j with ((k | k) | k) | k <;> simp only [hbank, bank_inl, bank_inr] <;>
    (first | fin_cases k | cases k) <;> first
      | rfl | exact absurd rfl (hj (.inl 0)) | exact absurd rfl (hj (.inl 1))
      | exact absurd rfl (hj (.inl 2)) | exact absurd rfl (hj (.inr 0))
      | exact absurd rfl (hj (.inr 1)) | exact absurd rfl (hj (.inr 2))))

/-! ## The six stages -/

theorem stage_mv (P : Fin 10 → List Bool) (rw cl : ℕ) (out bs : List Bool) (s : Option Bool) :
    ((advance sMV)^[bs.reverse.length + 1])
        ⟨some .mv, s, hbank P rw cl out (ext bs.reverse [] [] [] [] [] [] [])⟩ =
      ⟨none, none, hbank P rw cl out (ext [] [] [] [] [] bs [] [])⟩ := by
  have h := Bits.Move.move_run bs.reverse [] s
  rw [List.append_nil, List.reverse_reverse] at h
  exact embed_run ιMV Bits.Move.program .mv s none
    ![bs.reverse, []] ![[], bs] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by hdr_out)

theorem stage_lg0 (P : Fin 10 → List Bool) (E cl : ℕ) (out w : List Bool) (s : Bool) :
    ∃ t ≤ (3 * 2 ^ E + 5) * (E + 1), ∃ v,
      ((advance sLG0)^[t])
        ⟨some .check, s, hbank P (2 ^ E) cl out (ext [] [] [] [] [] w [] [])⟩ =
      ⟨none, v, hbank P 0 cl out (ext [] [] [] [] [] w (List.replicate E true) [])⟩ := by
  obtain ⟨t, ht, v, h⟩ := ULog.log_run (2 ^ E) 0 s
  rw [Nat.zero_add, Nat.clog_pow 2 E (by norm_num)] at h
  rw [Nat.clog_pow 2 E (by norm_num)] at ht
  exact ⟨t, ht, v, embed_run ιLG0 ULog.program .check s v
    ![rp (2 ^ E), [], rp 0] ![[], [], rp E] _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by hdr_out)⟩

theorem stage_lg1 (P : Fin 10 → List Bool) (E : ℕ) (out w : List Bool) (s : Bool) :
    ∃ t ≤ (3 * 2 ^ E + 5) * (E + 1), ∃ v,
      ((advance sLG1)^[t])
        ⟨some .check, s, hbank P 0 (2 ^ E) out (ext [] [] [] [] [] w (List.replicate E true) [])⟩ =
      ⟨none, v, hbank P 0 0 out
        (ext [] [] [] [] [] w (List.replicate E true) (List.replicate E true))⟩ := by
  obtain ⟨t, ht, v, h⟩ := ULog.log_run (2 ^ E) 0 s
  rw [Nat.zero_add, Nat.clog_pow 2 E (by norm_num)] at h
  rw [Nat.clog_pow 2 E (by norm_num)] at ht
  exact ⟨t, ht, v, embed_run ιLG1 ULog.program .check s v
    ![rp (2 ^ E), [], rp 0] ![[], [], rp E] _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by hdr_out)⟩

theorem stage_pb0 (P : Fin 10 → List Bool) (E : ℕ) (out w : List Bool) (s : Bool) :
    ((advance sPB0)^[E + 2])
        ⟨some .init, s, hbank P 0 0 out
          (ext [] [] [] [] [] w (List.replicate E true) (List.replicate E true))⟩ =
      ⟨none, false, hbank P 0 0 out
        (ext [] [] [] (2 ^ E).bits [] w [] (List.replicate E true))⟩ := by
  have h := Bits.PowBits.powbits_run E [] s
  rw [List.append_nil] at h
  exact embed_run ιPB0 Bits.PowBits.program .init s false
    ![List.replicate E true, []] ![[], Nat.bits (2 ^ E)] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by hdr_out)

theorem stage_pb1 (P : Fin 10 → List Bool) (E : ℕ) (out w : List Bool) (s : Bool) :
    ((advance sPB1)^[E + 2])
        ⟨some .init, s, hbank P 0 0 out
          (ext [] [] [] (2 ^ E).bits [] w [] (List.replicate E true))⟩ =
      ⟨none, false, hbank P 0 0 out
        (ext [] [] [] (2 ^ E).bits (2 ^ E).bits w [] [])⟩ := by
  have h := Bits.PowBits.powbits_run E [] s
  rw [List.append_nil] at h
  exact embed_run ιPB1 Bits.PowBits.program .init s false
    ![List.replicate E true, []] ![[], Nat.bits (2 ^ E)] _ _ _ h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by hdr_out)

theorem stage_ser (P : Fin 10 → List Bool) (E thr : ℕ) (out : List Bool) :
    ∃ (t : ℕ) (S' : BitMachineBankSerialize.Bank 3),
      t ≤ 2 * (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
        EncodedCommunication.natField thr).length + 2 ∧
      ((advance sSER)^[t])
        ⟨some (.emit 0), none, hbank P 0 0 out
          (ext [] [] [] (2 ^ E).bits (2 ^ E).bits thr.bits [] [])⟩ =
      ⟨none, none, hbank P 0 0
        (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
          EncodedCommunication.natField thr ++ out)
        (ext [] [] [] (S' 0) (S' 1) (S' 2) [] [])⟩ := by
  obtain ⟨t, S', ht, h⟩ := MatrixInstanceEncoding.encode_run (2 ^ E) (2 ^ E) thr [] out []
  simp only [MatrixInstanceEncoding.run, MatrixInstanceEncoding.initial, List.append_nil] at h
  refine ⟨t, S', ht, ?_⟩
  exact embed_run ιSER MatrixInstanceEncoding.program (.emit 0) none none
    (BitMachineBankSerialize.contents (MatrixInstanceEncoding.binaryBank (2 ^ E) (2 ^ E) thr)
      [] [] out)
    (BitMachineBankSerialize.contents S' [] []
      (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
        EncodedCommunication.natField thr ++ out)) _ _ t h
    (by intro i; rcases i with i | i <;> fin_cases i <;> rfl)
    (by intro i; rcases i with i | i <;> fin_cases i <;> rfl) (by hdr_out2)

/-- The explicit header clock. -/
def headerBound (E thr : ℕ) : ℕ :=
  (thr.bits.length + 1) + 2 * ((3 * 2 ^ E + 5) * (E + 1)) + 2 * (E + 2) +
    (2 * (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
      EncodedCommunication.natField thr).length + 2) + 5

/-- **Segment 2 (the header).** For every persistent bank `P`, exponent `E`, threshold `thr` and
table word `out`, the ONE fixed header program, started with unary `2^E` in both writer counters,
`out` on the writer output stack and `thr.bits.reverse` in extra stack 0 (all other non-persistent
stacks empty), halts within `headerBound E thr` steps with exactly
`natField (2^E) ++ natField (2^E) ++ natField thr ++ out` on the output stack, `P` unchanged, both
counters empty, and the admitted serializer's consumed bank `S'` in extra stacks 3, 4, 5 (every
other stack empty). -/
theorem header_run (P : Fin 10 → List Bool) (E thr : ℕ) (out : List Bool) :
    ∃ t ≤ headerBound E thr, ∃ (v : HControl) (S' : BitMachineBankSerialize.Bank 3),
      ((advance header)^[t])
        ⟨some hstart, hinit, hbank P (2 ^ E) (2 ^ E) out (ext thr.bits.reverse [] [] [] [] [] [] [])⟩ =
      ⟨none, v, hbank P 0 0
        (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
          EncodedCommunication.natField thr ++ out)
        (ext [] [] [] (S' 0) (S' 1) (S' 2) [] [])⟩ := by
  have h1 := stage_mv P (2 ^ E) (2 ^ E) out thr.bits none
  obtain ⟨t2, ht2, v2, h2⟩ := stage_lg0 P E (2 ^ E) out thr.bits false
  obtain ⟨t3, ht3, v3, h3⟩ := stage_lg1 P E out thr.bits false
  have h4 := stage_pb0 P E out thr.bits false
  have h5 := stage_pb1 P E out thr.bits false
  obtain ⟨t6, S', ht6, h6⟩ := stage_ser P E thr out
  obtain ⟨u5, hu5, e5⟩ := BitMachineRawSequence.runs sPB1 sSER .init (.emit 0) false false
    none none _ _ _ _ _ h5 h6
  obtain ⟨u4, hu4, e4⟩ := BitMachineRawSequence.runs sPB0 hseq5 .init hstart5 false false
    hinit5 _ _ _ _ _ _ h4 e5
  obtain ⟨u3, hu3, e3⟩ := BitMachineRawSequence.runs sLG1 hseq4 .check hstart4 false v3
    hinit4 _ _ _ _ _ _ h3 e4
  obtain ⟨u2, hu2, e2⟩ := BitMachineRawSequence.runs sLG0 hseq3 .check hstart3 false v2
    hinit3 _ _ _ _ _ _ h2 e3
  obtain ⟨u1, hu1, e1⟩ := BitMachineRawSequence.runs sMV hseq2 .mv hstart2 none none
    hinit2 _ _ _ _ _ _ h1 e2
  refine ⟨u1, ?_, _, S', e1⟩
  have hl : thr.bits.reverse.length = thr.bits.length := List.length_reverse
  unfold headerBound
  omega

#print axioms header_run

end Paper2.ASquare.Post
