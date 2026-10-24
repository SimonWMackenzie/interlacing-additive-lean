import CurrentAdditive.StoredRoundUpdate
import CurrentAdditive.StoredRoundRoutes
import CurrentAdditive.V40LawPathsContextual
import CurrentAdditive.LawJobBitPrimitives

/-! The seven actual, sequential CodeD phases. Earlier sources remain in a
physically retained eight-field bank and supply the laws read by later calls.
No source array, successful call or generated law is supplied by the caller. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundStages
open EthInapproximability.CurrentPaper PhysicalProducer V40LawJobsClock StoredRoundData
noncomputable section

def routeBuilder (i : Fin 7) := pair identity (StoredRoundRoutes.request i)
def routeSource := pair identity
  (PhysicalProducer.compose (projection (1 : Fin 2)) (projection (1 : Fin 3)))

def w0 (a : Data) (i : Fin 7) := V40LawPacket.packet (state a i.val) (V40ActualSevenRequests.input a.parameters i)
def w1 (a : Data) (i : Fin 7) := V40LawPacket.packet (state a i.val) (V40ActualSevenRequests.output a.parameters i)
def w2 (a : Data) (i : Fin 7) := V40LawPacket.packet (w1 a i) (StoredSourcePhase.input (call a i))

def first (i : Fin 7) := BitMachineComposition.composition (routeBuilder i).machine (V40LawPathsContextual.seven i)
def second (i : Fin 7) := BitMachineComposition.composition (first i) routeSource.machine
def third (i : Fin 7) := BitMachineComposition.composition (second i) (V40LawBankMap.liftMachine StoredSourcePhase.machine)
def stage (i : Fin 7) := BitMachineComposition.composition (third i) (StoredRoundUpdate.implementation i).machine

theorem routeBuilder_result (a : Data) (i : Fin 7) : (routeBuilder i).result (state a i.val)=w0 a i := by
  simp [routeBuilder,w0,StoredRoundRoutes.request_result]

theorem routeSource_result (a : Data) (i : Fin 7) : routeSource.result (w1 a i)=w2 a i := by
  simp only [routeSource,pair_result,identity_result,PhysicalProducer.compose,Function.comp_apply,
    projection,w1,w2,packet_eq,BankFieldProjection.result_encode,Matrix.cons_val_one]
  exact congrArg (fun req=>BitMachineBankCodec.encode ![
    BitMachineBankCodec.encode ![state a i.val,V40ActualSevenRequests.output a.parameters i],req])
    (StoredRoundData.request_eq a i)

theorem stage_realizes (i : Fin 7) : Realizes (stage i)
    (fun a : Data=>state a i.val) (fun a=>state a (i.val+1)) := by
  have h0 := producer (routeBuilder i) (fun a : Data=>state a i.val)
  simp only [routeBuilder_result] at h0
  have hb : Realizes (V40ActualSevenRequests.machine i)
      (fun a : Data=>V40ActualSevenRequests.input a.parameters i)
      (fun a=>V40ActualSevenRequests.output a.parameters i) := by
    obtain ⟨C,E,h⟩ := V40ActualSevenRequests.requests_outputs
    exact ⟨C,E,fun a=>h a.parameters i⟩
  have h1 := bank_map (V40ActualSevenRequests.machine i) (fun a : Data=>state a i.val) _ _ hb
  have h2 := producer routeSource (fun a : Data=>w1 a i)
  simp only [routeSource_result] at h2
  have hp : Realizes StoredSourcePhase.machine
      (fun a : Data=>StoredSourcePhase.input (call a i))
      (fun a=>StoredSourcePhase.output (call a i)) := by
    obtain ⟨C,E,h⟩ := StoredSourcePhase.realizes
    exact ⟨C,E,fun a=>h (call a i)⟩
  have h3 := bank_map StoredSourcePhase.machine (fun a : Data=>w1 a i) _ _ hp
  have h4 := StoredRoundUpdate.realizes i
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4

def initialBank := DynamicGetterOrdinary.bankFields
  (List.ofFn (fun j : Fin 8 => if j.val=0 then identity else LawJobBitPrimitives.empty))

theorem initialize_result (a : Data) : initialBank.result (input a)=state a 0 := by
  simp [initialBank,DynamicGetterOrdinary.bankFields_result,state,
    BitMachineBankCodec.encode_eq_list,List.flatMap_def,List.map_ofFn,Function.comp_def,
    LawJobBitPrimitives.empty]

def index (n : Nat) : Fin 7 := ⟨n%7,Nat.mod_lt _ (by decide)⟩
def phases : Nat → BitMachine.Machine
  | 0 => initialBank.machine
  | n+1 => BitMachineComposition.composition (phases n) (stage (index n))

theorem prefix_realizes (k : Nat) (hk : k≤7) : Realizes (phases k) input (fun a=>state a k) := by
  induction k with
  | zero =>
    have h := producer initialBank input
    simpa only [initialize_result] using h
  | succ k ih =>
    have hi : (index k).val=k := Nat.mod_eq_of_lt (by omega)
    have hstage := stage_realizes (index k)
    simp only [hi] at hstage
    exact V40LawJobsClock.compose _ _ _ _ _ (ih (by omega)) hstage

def machine := phases 7

theorem realizes : Realizes machine input (fun a=>state a 7) := prefix_realizes 7 le_rfl

end
end CurrentAdditive.StoredRoundStages

#print axioms CurrentAdditive.StoredRoundStages.realizes
