import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.BitMachineBankCodec

namespace CurrentAdditive.CodeDPacketRouting
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open EthInapproximability.CurrentPaper
open PhysicalProducer

/-- Three actual field writers and two actual concatenators serialize a
fixed three-field packet, with all three producers reading the same input. -/
def bank3 (A B C : Producer) : Producer :=
  concat (compose A field) (concat (compose B field) (compose C field))

def bank2 (A B : Producer) : Producer :=
  concat (compose A field) (compose B field)

theorem bank3_result (A B C : Producer) (x : List Bool) :
    (bank3 A B C).result x =
      BitMachineBankCodec.encode ![A.result x,B.result x,C.result x] := by
  simp only [bank3,concat,compose,field,Function.comp_apply,
    BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.ofFn_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem bank2_result (A B : Producer) (x : List Bool) :
    (bank2 A B).result x =
      BitMachineBankCodec.encode ![A.result x,B.result x] := by
  simp only [bank2,concat,compose,field,Function.comp_apply,
    BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.ofFn_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

def nested (i : Fin 3) : Producer := compose (projection (0 : Fin 2)) (projection i)
def last : Producer := projection (1 : Fin 2)

/-- Input `[original three-field packet,new source]`; output the original
first two fields followed by the newly computed source. -/
def replaceLast : Producer := bank3 (nested 0) (nested 1) last

/-- Input `[original three-field packet,coefficient vector]`; output the
original source and computed coefficients, ready for the real ratio branch. -/
def sourceCoefficients : Producer := bank2 (nested 2) last

theorem nested_result (i : Fin 3) (w : Fin 3 → List Bool) (bits : List Bool) :
    (nested i).result (BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits]) = w i := by
  simp only [nested,compose,projection,Function.comp_apply,BankFieldProjection.result_encode,
    Matrix.cons_val_zero]

theorem last_result (w : List Bool) (bits : List Bool) :
    last.result (BitMachineBankCodec.encode ![w,bits]) = bits := by
  simp only [last,projection,BankFieldProjection.result_encode,Matrix.cons_val_one,Matrix.cons_val_zero]

theorem replaceLast_outputs (w : Fin 3 → List Bool) (bits : List Bool) :
    replaceLast.machine.OutputsWithin
      (BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits])
      (BitMachineBankCodec.encode ![w 0,w 1,bits])
      (replaceLast.coefficient *
        ((BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits]).length+1)^replaceLast.degree) := by
  have h := replaceLast.outputs (BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits])
  simpa only [replaceLast,bank3_result,nested_result,last_result] using h

theorem sourceCoefficients_outputs (w : Fin 3 → List Bool) (bits : List Bool) :
    sourceCoefficients.machine.OutputsWithin
      (BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits])
      (BitMachineBankCodec.encode ![w 2,bits])
      (sourceCoefficients.coefficient *
        ((BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits]).length+1)^sourceCoefficients.degree) := by
  have h := sourceCoefficients.outputs (BitMachineBankCodec.encode ![BitMachineBankCodec.encode w,bits])
  simpa only [sourceCoefficients,bank2_result,nested_result,last_result] using h

#print axioms replaceLast_outputs
#print axioms sourceCoefficients_outputs
end
end CurrentAdditive.CodeDPacketRouting
