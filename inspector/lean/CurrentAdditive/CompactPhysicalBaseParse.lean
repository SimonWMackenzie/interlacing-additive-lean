import CurrentAdditive.CompactFinCodec
import CurrentAdditive.PhysicalBaseTableLookup
import Paper2.ASquarePostParse

/-! The checked compact index words are physically parsed by the existing
fixed three-field program.  The third field is zero and the untouched suffix
is the packet's row-major table.  The table callback is stated separately;
this file does not claim that the two programs have been joined. -/

namespace Paper2.CompactPhysicalBaseParse

open Paper2.CompactFinCodec Paper2.CompactRationalPacket
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing Turing.TM2.Stmt

def input {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) : List Bool :=
  (codec rows).encode i ++ (codec cols).encode j ++
    EncodedCommunication.field (0 : ℕ).bits ++ P.table.bits

theorem input_eq_instance {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    input P i j = EncodedCommunication.encodeInstance
      ⟨i.val, j.val, 0, P.table.bits⟩ := by
  simp only [input, codec, EncodedCommunication.encodeInstance,
    EncodedCommunication.natField]
  have h (bs : List Bool) : frame bs = EncodedCommunication.field bs := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [frame, EncodedCommunication.field, ih]
  simp only [h, List.append_assoc]

theorem parser_run {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    ∃ t ≤ Paper2.ASquare.Post.parseBound i.val j.val 0, ∃ v,
      ((advance Paper2.ASquare.Post.parser)^[t])
        ⟨some Paper2.ASquare.Post.pstart, Paper2.ASquare.Post.pinit,
          Paper2.ASquare.Post.pbank [] [] (input P i j)
            Paper2.ASquare.Post.ext0⟩ =
      ⟨none, v, Paper2.ASquare.Post.pbank
          (List.replicate i.val true) (List.replicate j.val true)
          P.table.bits (Paper2.ASquare.Post.ext [] [] [] [] [] [] [] [])⟩ := by
  rw [input_eq_instance]
  simpa using Paper2.ASquare.Post.parse_run i.val j.val 0 P.table.bits

#print axioms input_eq_instance
#print axioms parser_run

end Paper2.CompactPhysicalBaseParse
