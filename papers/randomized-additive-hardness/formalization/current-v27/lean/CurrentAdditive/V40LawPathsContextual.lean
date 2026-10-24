import CurrentAdditive.V40ActualSevenRequests

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawPathsContextual
open EthInapproximability.CurrentPaper V40LawJobsClock
noncomputable section

def sourceColumn := V40LawBankMap.liftMachine V40SourceColumnLaw.machine
def successorColumn := V40LawBankMap.liftMachine V40SuccessorColumnLaw.machine
def finalRequest := V40LawBankMap.liftMachine V40FinalSourceRequest.machine
def seven (i : Fin 7) := V40LawBankMap.liftMachine (V40ActualSevenRequests.machine i)

theorem sourceColumn_realizes : Realizes sourceColumn
    (fun a : List Bool × V40SourceColumnLaw.Data =>
      V40LawPacket.packet a.1 (V40SourceColumnLaw.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40SourceColumnLaw.output a.2)) := by
  have h : Realizes V40SourceColumnLaw.machine
      (fun a : List Bool × V40SourceColumnLaw.Data => V40SourceColumnLaw.input a.2)
      (fun a => V40SourceColumnLaw.output a.2) := by
    obtain ⟨C,d,h⟩ := V40SourceColumnLaw.realizes
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

theorem successorColumn_realizes : Realizes successorColumn
    (fun a : List Bool × V40SuccessorColumnLaw.Data =>
      V40LawPacket.packet a.1 (V40SuccessorColumnLaw.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40SuccessorColumnLaw.output a.2)) := by
  have h : Realizes V40SuccessorColumnLaw.machine
      (fun a : List Bool × V40SuccessorColumnLaw.Data => V40SuccessorColumnLaw.input a.2)
      (fun a => V40SuccessorColumnLaw.output a.2) := by
    obtain ⟨C,d,h⟩ := V40SuccessorColumnLaw.realizes
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

theorem finalRequest_realizes : Realizes finalRequest
    (fun a : List Bool × V40FinalSourceRequest.Data =>
      V40LawPacket.packet a.1 (V40FinalSourceRequest.input a.2))
    (fun a => V40LawPacket.packet a.1 (V40FinalSourceRequest.output a.2)) := by
  have h : Realizes V40FinalSourceRequest.machine
      (fun a : List Bool × V40FinalSourceRequest.Data => V40FinalSourceRequest.input a.2)
      (fun a => V40FinalSourceRequest.output a.2) := by
    obtain ⟨C,d,h⟩ := V40FinalSourceRequest.realizes
    exact ⟨C,d,fun a => h a.2⟩
  exact bank_map _ Prod.fst _ _ h

/-- Every previous source packet may live in context. The same literal
context is restored after any one of the seven actual request builders,
with a common byte polynomial fixed before the context, data, and position. -/
theorem seven_outputs : ∃ C d : ℕ, ∀ (i : Fin 7) (context : List Bool)
    (a : V40ActualSevenRequests.Data),
    (seven i).OutputsWithin
      (V40LawPacket.packet context (V40ActualSevenRequests.input a i))
      (V40LawPacket.packet context (V40ActualSevenRequests.output a i))
      (C*((V40LawPacket.packet context (V40ActualSevenRequests.input a i)).length+1)^d) := by
  obtain ⟨c,d,h⟩ := V40ActualSevenRequests.requests_outputs
  let P := Finset.univ.sup (fun i : Fin 7 => (V40ActualSevenRequests.machine i).pushBound)
  refine ⟨10*(c+1)*(P+1)*3^(d+1),d+1,?_⟩
  intro i context a
  have hr := V40LawBankMap.outputs_polynomial (V40ActualSevenRequests.machine i) c d
    context (V40ActualSevenRequests.input a i) (V40ActualSevenRequests.output a i) (h a i)
  apply BitMachine.outputsWithin_mono _ hr
  have hP : (V40ActualSevenRequests.machine i).pushBound≤P := by
    dsimp only [P]
    exact Finset.le_sup (f := fun j : Fin 7 => (V40ActualSevenRequests.machine j).pushBound)
      (Finset.mem_univ i)
  have hsize : (V40LawPacket.packet context (V40ActualSevenRequests.input a i)).length+3 ≤
      3*((V40LawPacket.packet context (V40ActualSevenRequests.input a i)).length+1) := by omega
  calc
    _ ≤ 10*(c+1)*(P+1)*
        (3*((V40LawPacket.packet context (V40ActualSevenRequests.input a i)).length+1))^(d+1) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

#print axioms sourceColumn_realizes
#print axioms successorColumn_realizes
#print axioms seven_outputs
end
end CurrentAdditive.V40LawPathsContextual
