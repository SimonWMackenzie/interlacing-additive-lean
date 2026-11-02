import EthInapproximability.CurrentPaper.DimensionNatUnary
import EthInapproximability.CurrentPaper.SourceListMachineFields

/-! A fixed physical machine reads the V2 outer count and writes unary
fuel. The suffix is ordinary input, not an uncharged predecoded count. -/

namespace CurrentAdditive.FeatureMapListCount

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

def tailProgram (_ : Unit) : TM2.Stmt (fun _ : Unit => Bool) Unit Unit :=
 .pop () (fun _ _ => ()) .halt

noncomputable def tailMachine : BitMachine.Machine :=
 ofFinite () () () () tailProgram

theorem tail_outputs (bits : List Bool) :
 tailMachine.OutputsWithin bits bits.tail 1 := by
 apply outputsWithin_of_raw_run () () () () tailProgram bits bits.tail 1 1 le_rfl
 · rfl
 · rfl

noncomputable def headerMachine : BitMachine.Machine :=
 BitMachineComposition.composition ProtocolBinaryHeader.machine tailMachine

noncomputable def machine : BitMachine.Machine :=
 BitMachineComposition.composition headerMachine DimensionNatUnary.bitsMachine

def bound (n : Nat) (source : List Bool) : Nat :=
 (2 * source.length + 2) + 2 * (n.bits.length + 1) + 2 + 1 +
  2 * n.bits.length + 2 + (4 * n + 6 * n.bits.length + 5)

theorem header_outputs (n : Nat) (suffix : List Bool) :
 headerMachine.OutputsWithin (EncodedCommunication.natField n ++ suffix) n.bits
   ((2 * (EncodedCommunication.natField n ++ suffix).length + 2) +
     2 * (n.bits.length + 1) + 2 + 1) := by
 have h := ProtocolBinaryHeader.outputs (EncodedCommunication.natField n ++ suffix)
 have he : ProtocolBinaryHeader.result (EncodedCommunication.natField n ++ suffix) =
     true :: n.bits := by
   simp [ProtocolBinaryHeader.result, SourceListMachineFields.readChecked_natField]
 rw [he] at h
 have ht := tail_outputs (true :: n.bits)
 have hc := BitMachineComposition.composition_outputsWithin
   ProtocolBinaryHeader.machine tailMachine h ht
 simpa [headerMachine] using hc

theorem outputs (n : Nat) (suffix : List Bool) :
 machine.OutputsWithin (EncodedCommunication.natField n ++ suffix)
   (List.replicate n true)
   (bound n (EncodedCommunication.natField n ++ suffix)) := by
 exact BitMachineComposition.composition_outputsWithin headerMachine
   DimensionNatUnary.bitsMachine (header_outputs n suffix)
   (DimensionNatUnary.bits_outputs n)

theorem bound_le (n : Nat) (source : List Bool) (L : Nat)
 (hn : n ≤ L) (hs : source.length ≤ L) : bound n source ≤ 20 * (L + 1) := by
 have hb := UnaryBinaryEncoding.bits_length_le n
 dsimp [bound]
 omega

#print axioms outputs
#print axioms bound_le

end CurrentAdditive.FeatureMapListCount
