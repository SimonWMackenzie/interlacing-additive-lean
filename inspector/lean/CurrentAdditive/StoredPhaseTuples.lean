import CurrentAdditive.StoredRoundData

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundProjection
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
noncomputable section

theorem tupleWords_ofFn {q : Nat} (arr : Array ((Fin q → Nat) × Rat)) :
    CylinderProductionProjection.tupleWords arr=
      List.ofFn (fun j : Fin arr.size => SourceListEncoding.encode
        (List.ofFn (fun p : Fin q => (arr[j].1 p).bits))) := by
  apply List.ext_getElem
  · simp [CylinderProductionProjection.tupleWords]
  · intro i hi hj
    simp [CylinderProductionProjection.tupleWords]

theorem run_tuples (q n : Nat) (μ : PositiveRationalLaw (Fin n)) :
    StoredSourcePhase.tupleBytes ⟨q,n,μ⟩=SourceListEncoding.encode
      (List.ofFn (fun j : Fin ((executableCodeD 8192).run q n μ).size =>
        SourceListEncoding.encode (List.ofFn (fun p : Fin q =>
          (((executableCodeD 8192).run q n μ).decode j p).val.bits)))) := by
  rw [StoredSourcePhase.tupleBytes,tupleWords_ofFn]
  rfl

theorem call_tuples {A : Type} [Fintype A] [DecidableEq A] (q n : Nat)
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A) :
    StoredSourcePhase.tupleBytes ⟨q,n,reindex e μ⟩=SourceListEncoding.encode
      (List.ofFn (fun j : Fin ((executableCodeD 8192).call q e μ).size =>
        SourceListEncoding.encode (List.ofFn (fun p : Fin q =>
          (e (((executableCodeD 8192).call q e μ).decode j p)).val.bits)))) := by
  rw [StoredSourcePhase.tupleBytes,tupleWords_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  congr 1
  apply congrArg List.ofFn
  funext p
  simp only [CodeD.call,ExactList.renumber,Equiv.apply_symm_apply]
  rfl

end
end CurrentAdditive.StoredRoundProjection

#print axioms CurrentAdditive.StoredRoundProjection.call_tuples
