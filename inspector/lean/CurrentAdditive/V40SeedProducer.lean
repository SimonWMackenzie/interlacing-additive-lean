import CurrentAdditive.PhysicalProducer
import CurrentAdditive.CodeDTargetV2
import EthInapproximability.CurrentPaper.DimensionNatUnary

/-! Fixed physical primitives used by the uniform indexed law writer.
Constant bytes are literal program syntax; numerical inputs are counted by
the actual unary-to-binary machine. -/
namespace CurrentAdditive.V40SeedProducer
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 Turing Turing.TM2.Stmt EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineBankCodec EncodedCommunication
open PhysicalProducer

def pushWord (q : List Bool) : TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit :=
  q.foldr (fun b rest => push 1 (fun _ => b) rest) halt

theorem pushWord_step (q : List Bool) (S : Fin 2 → List Bool) :
    TM2.stepAux (pushWord q) () S=
      (⟨none,(),Function.update S 1 (q.reverse++S 1)⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Unit) := by
  induction q generalizing S with
  | nil => simp [pushWord,TM2.stepAux]
  | cons b q ih =>
      simp only [pushWord,List.foldr_cons,TM2.stepAux]
      rw [show q.foldr (fun b rest => push (1:Fin 2) (fun _ : Unit => b) rest) halt=pushWord q from rfl,ih]
      congr 1
      funext j
      by_cases h : j=1
      · subst j; simp [List.reverse_cons,List.append_assoc]
      · simp [h]

def constantProgram (q : List Bool) (_ : Unit) := pushWord q.reverse
def constantMachine (q : List Bool) : BitMachine.Machine :=
  ofFinite (0:Fin 2) 1 () () (constantProgram q)

theorem constant_outputs (q input : List Bool) :
    (constantMachine q).OutputsWithin input q 1 := by
  have h : ((advance (constantProgram q))^[1])
      (rawInit (0:Fin 2) () () input)=
      (⟨none,(),Function.update (rawInit (0:Fin 2) () () input).stk 1 q⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) Unit Unit) := by
    simp only [Function.iterate_one,advance,rawInit,TM2.step,Option.getD_some,constantProgram]
    rw [pushWord_step]
    simp [List.reverse_reverse]
  apply outputsWithin_of_raw_run (0:Fin 2) 1 () () (constantProgram q) input q 1 1 (by omega)
  · rw [h]
  · rw [h]; simp

def constant (q : List Bool) : Producer where
  machine := constantMachine q
  result := fun _ => q
  coefficient := 1
  degree := 0
  outputs x := by simpa using constant_outputs q x

def unaryBinary : Producer where
  machine := UnaryBinaryEncoding.machine
  result := fun x => x.length.bits
  coefficient := UnaryBinaryEncoding.coefficient
  degree := 2
  outputs := UnaryBinaryEncoding.outputs

def reverse : Producer where
  machine := DimensionNatUnary.reverseMachine
  result := List.reverse
  coefficient := 1
  degree := 1
  outputs x := by simpa using DimensionNatUnary.reverse_outputs x

def inverseRaw : Producer :=
  concat (constant (field []++field [true]))
    (compose (compose unaryBinary reverse) PhysicalProducer.field)

theorem raw_inverse (n : Nat) (hn : 0<n) :
    CodeDCanonicalSourceV2.rawOfRat ((n:ℚ)⁻¹)=
      (⟨false,[true],n.bits.reverse⟩ : CodeDCodec.RawRat) := by
  simp [CodeDCanonicalSourceV2.rawOfRat,Rat.inv_natCast_num_of_pos hn,Rat.inv_natCast_den_of_pos hn]

theorem inverse_result (n : Nat) (hn : 0<n) :
    inverseRaw.result (List.replicate n true)=
      CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat ((n:ℚ)⁻¹)) := by
  rw [raw_inverse n hn]
  simp [inverseRaw,concat,constant,compose,unaryBinary,reverse,PhysicalProducer.field,
    CodeDCodec.encodeRawRat,CodeDCodec.rawRatBank,encode,encodeFrom]

def entry : Producer :=
  concat (compose (compose (projection (0:Fin 2)) unaryBinary) PhysicalProducer.field)
    (compose (compose (projection (1:Fin 2)) inverseRaw) PhysicalProducer.field)

theorem entry_result (i n : Nat) (hn : 0<n) :
    entry.result (encode ![List.replicate i true,List.replicate n true])=
      CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹) := by
  simp only [entry,concat,compose,projection,unaryBinary,PhysicalProducer.field,
    Function.comp_apply,BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [List.length_replicate,inverse_result n hn]
  simp [CodeDTargetV2.alphabetEntry,encode,encodeFrom]

#print axioms constant_outputs
#print axioms inverse_result
#print axioms entry_result
end
end CurrentAdditive.V40SeedProducer
