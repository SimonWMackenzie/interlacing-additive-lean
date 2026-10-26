import CurrentAdditive.DynamicGetterOrdinary
import CurrentAdditive.ContextualInvokePolynomial
import CurrentAdditive.PhysicalProducer

/-! A physically loaded list selection retains the entire original request.
Only the decoded list and the in-range binary index are premises. No desired
machine run or all-input totality of the partial getter is assumed. -/

namespace CurrentAdditive.StoredRetainedGetter

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.PhysicalProducer
noncomputable section

def identityProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 1 => Bool) Unit Unit := .halt
def identityMachine : BitMachine.Machine := ofFinite (0 : Fin 1) 0 () () identityProgram

theorem identity_outputs (x : List Bool) : identityMachine.OutputsWithin x x 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 1) 0 () () identityProgram x x 1 1 le_rfl
  · rfl
  · rfl

def identity : Producer where
  machine := identityMachine
  result := id
  coefficient := 1
  degree := 0
  outputs x := by simpa using identity_outputs x

def bank2 (A B : Producer) : Producer :=
  concat (compose A field) (compose B field)

theorem bank2_result (A B : Producer) (x : List Bool) :
    (bank2 A B).result x = BitMachineBankCodec.encode ![A.result x,B.result x] := by
  simp [bank2,concat,compose,field,BitMachineBankCodec.encode_eq_list]

def router (source index : Producer) := bank2 identity (bank2 source index)

theorem router_result (source index : Producer) (x : List Bool) :
    (router source index).result x = ContextualInvoke.packet x
      (BitMachineBankCodec.encode ![source.result x,index.result x]) := by
  simp only [router,bank2_result,identity,ContextualInvoke.packet,id_eq]

def getterCoefficient : Nat := Classical.choose DynamicGetterOrdinary.uniform_bits
def getterDegree : Nat := Classical.choose (Classical.choose_spec DynamicGetterOrdinary.uniform_bits)

theorem getter_outputs (xs : List (List Bool)) (bits : List Bool)
    (hi : EncodedCommunication.bitsValue bits < xs.length) :
    DynamicGetterOrdinary.machine.OutputsWithin (DynamicGetterOrdinary.packet xs bits)
      xs[EncodedCommunication.bitsValue bits]
      (getterCoefficient*((DynamicGetterOrdinary.packet xs bits).length+1)^getterDegree) :=
  Classical.choose_spec (Classical.choose_spec DynamicGetterOrdinary.uniform_bits) xs bits hi

def machine (source index : Producer) : BitMachine.Machine :=
  BitMachineComposition.composition (router source index).machine
    (ContextualInvoke.machine DynamicGetterOrdinary.machine)

def coefficient (source index : Producer) : Nat :=
  DynamicGetterOrdinary.composeCoefficient (router source index).machine
    (router source index).coefficient
    (ContextualInvoke.polynomialCoefficient DynamicGetterOrdinary.machine getterCoefficient)
    (getterDegree+1)

def degree (source index : Producer) : Nat :=
  DynamicGetterOrdinary.composeDegree (router source index).degree (getterDegree+1)

theorem outputs (source index : Producer) (x : List Bool) (xs : List (List Bool))
    (hsource : source.result x = SourceListEncoding.encode xs)
    (hi : EncodedCommunication.bitsValue (index.result x) < xs.length) :
    (machine source index).OutputsWithin x
      (BitMachineBankCodec.encode ![x,xs[EncodedCommunication.bitsValue (index.result x)]])
      (coefficient source index*(x.length+1)^degree source index) := by
  have hroute := (router source index).outputs x
  have hload : (router source index).result x =
      ContextualInvoke.packet x (DynamicGetterOrdinary.packet xs (index.result x)) := by
    rw [router_result,hsource]
    rfl
  have hcall := ContextualInvoke.outputs_polynomial DynamicGetterOrdinary.machine
    getterCoefficient getterDegree x (DynamicGetterOrdinary.packet xs (index.result x))
    xs[EncodedCommunication.bitsValue (index.result x)] (getter_outputs xs _ hi)
  have hcompose := DynamicGetterOrdinary.compose_outputs
    (router source index).machine (ContextualInvoke.machine DynamicGetterOrdinary.machine)
    x ((router source index).result x)
    (ContextualInvoke.output x xs[EncodedCommunication.bitsValue (index.result x)])
    (router source index).coefficient (router source index).degree
    (ContextualInvoke.polynomialCoefficient DynamicGetterOrdinary.machine getterCoefficient)
    (getterDegree+1) hroute (by simpa only [hload] using hcall)
  exact hcompose

end
end CurrentAdditive.StoredRetainedGetter

#print axioms CurrentAdditive.StoredRetainedGetter.outputs
