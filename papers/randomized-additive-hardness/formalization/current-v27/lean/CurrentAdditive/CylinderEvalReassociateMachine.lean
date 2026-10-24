import CurrentAdditive.CylinderEvalReassociate

/-! A fixed machine physically changes the order of nested Bank2 fields.
All payload words are arbitrary; the two parsers and two serializers are
executed and charged. -/
namespace CurrentAdditive.CylinderEvalReassociate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

noncomputable def final (q a b : List Bool) (T U : Bank 2) : Config :=
  emitFrame true (innerFinal q a b T).stk
    (BitMachineBankSerialize.cfg none none U [] [] (output q a b))

theorem final_halt (q a b : List Bool) (T U : Bank 2) :
    (final q a b T U).l=none := rfl

theorem final_output (q a b : List Bool) (T U : Bank 2) :
    (final q a b T U).stk 10=output q a b := by
  change BitMachineStackEmbedding.bank (emitStack true) (innerFinal q a b T).stk
    (BitMachineBankSerialize.contents U [] [] (output q a b)) 10=output q a b
  rw [emitBank_at]
  rfl

theorem assembled_run (q a b : List Bool) :
    ∃ (t : ℕ) (T U : Bank 2),
      t≤2*(encode ![q,b]).length+2*(output q a b).length+6 ∧
      run t ⟨some (.afterParse true),some true,loaded q a b⟩ = final q a b T U := by
  obtain ⟨u,T,hu,hU⟩ := emit_run false (loaded q a b) (![q,b])
  have h1 := (run_add (loaded_to_inner q a b) u).trans hU
  have h2 := (run_add h1 1).trans (inner_to_outer q a b T)
  obtain ⟨v,U,hv,hV⟩ := emit_run true (innerFinal q a b T).stk (![encode ![q,b],a])
  refine ⟨1+u+1+v,T,U,?_,(run_add h2 v).trans hV⟩
  change v≤2*(output q a b).length+2 at hv
  omega

theorem input_length (q a b : List Bool) :
    (input q a b).length=4*q.length+4*a.length+2*b.length+6 := by
  simp [input,encode_length,Fin.sum_univ_two]
  omega

theorem output_length (q a b : List Bool) :
    (output q a b).length=4*q.length+4*b.length+2*a.length+6 := by
  simp [output,encode_length,Fin.sum_univ_two]
  omega

theorem inner_length (q b : List Bool) :
    (encode ![q,b]).length=2*q.length+2*b.length+2 := by
  simp [encode_length,Fin.sum_univ_two]
  omega

theorem raw_run (q a b : List Bool) :
    ∃ (t : ℕ) (T U : Bank 2), t≤30*((input q a b).length+1) ∧
      run t (rawInit (0 : Stack) (.parse false (.scan 0) : Label) none (input q a b)) =
        final q a b T U := by
  obtain ⟨u,hu,hU⟩ := loaded_run q a b
  obtain ⟨v,T,U,hv,hV⟩ := assembled_run q a b
  refine ⟨u+v,T,U,?_,(run_add hU v).trans hV⟩
  rw [input_length] at hu ⊢
  rw [inner_length,output_length] at hv
  omega

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) 10 (.parse false (.scan 0) : Label) none program

theorem outputs (q a b : List Bool) :
    machine.OutputsWithin (input q a b) (output q a b)
      (30*((input q a b).length+1)) := by
  obtain ⟨t,T,U,ht,hr⟩ := raw_run q a b
  apply outputsWithin_of_raw_run (0 : Stack) 10 (.parse false (.scan 0) : Label)
    none program (input q a b) (output q a b) t _ ht
  · change (run t _).l=none
    rw [hr]; exact final_halt q a b T U
  · change (run t _).stk 10=output q a b
    rw [hr]; exact final_output q a b T U

end CurrentAdditive.CylinderEvalReassociate

#print axioms CurrentAdditive.CylinderEvalReassociate.raw_run
#print axioms CurrentAdditive.CylinderEvalReassociate.outputs
