import EthInapproximability.CurrentPaper.GenericPrefixAmbientSeed

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientWork

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix PrefixAmbientCopy PrefixAmbientSeed PrefixTransferFrame
open scoped Classical

theorem rawVertex_ne_workN {q : Nat} :
    (rawVertex : PrefixAmbientCopy.Stack q) ≠ workN := by
  simp [rawVertex,workN,rawEmbedding,workEmbedding]
theorem rawVertex_ne_scratch {q : Nat} :
    (rawVertex : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [rawVertex,rawEmbedding,scratch]
theorem workN_ne_scratch {q : Nat} :
    (workN : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [workN,workEmbedding,scratch]

noncomputable def nProgram (q : Nat) :=
  PrefixAmbientCopy.copyProgram (rawVertex (q := q)) (workN (q := q))
    (rawVertex_ne_workN (q := q)) (rawVertex_ne_scratch (q := q))
    (workN_ne_scratch (q := q))

theorem seed_run {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n : Nat)
    (hvertex : U (.inr SourceClauseRowWriterOperands.vertex) =
      List.replicate n true) :
    ((advance (nProgram q))^[2*n+2])
      (⟨some .scan,none,initial U⟩ :
        TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
      ⟨none,none,seed U n⟩ := by
  have hs : initial U rawVertex = List.replicate n true := by
    exact (initial_raw U _).trans hvertex
  have hd : initial U workN = [] := initial_work U _
  have ht : initial U (scratch q) = [] := initial_scratch U
  have hr := PrefixAmbientCopy.copy_run (rawVertex (q := q)) (workN (q := q))
    (rawVertex_ne_workN (q := q)) (rawVertex_ne_scratch (q := q))
    (workN_ne_scratch (q := q))
    (initial U) (List.replicate n true) hs hd ht
  simpa only [nProgram,seed,List.length_replicate] using hr

noncomputable def workProgram (a q : Nat) :=
  fun l => stackStmt (workEmbedding q) (PrefixComposite.program a q l)

noncomputable def worked {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) : PrefixAmbientCopy.Stack q → List Bool :=
  bank (workEmbedding q) (seed U n)
    (PrefixComposite.finalBank n a q [] [] [])

theorem work_run {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) :
    ∃ T ≤ PrefixComposite.cost n a q [] [] [],
      ((advance (workProgram a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .copyScan))),
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          seed U n⟩ :
          TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
        ⟨none,
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          worked U n a⟩ := by
  obtain ⟨T,hT,hr⟩ := PrefixCompositeEndpoint.run_source n a q [] []
  have hsim := BitMachineStackRun.run (workEmbedding q) (seed U n)
    (PrefixComposite.program a q)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inr .copyScan))),
      ((((AtLeastLoopCallback.callback a q).initial,none),
        ((none,none),none)),
        ((PairVertexLoopCallback.routine a q).initial,none)),
      framedAt (PrefixLoopMachine.blank n 0 [] [] [] [])⟩ :
      TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) T
  rw [hr] at hsim
  have hbank : bank (workEmbedding q) (seed U n)
      (framedAt (PrefixLoopMachine.blank n 0 [] [] [] [])) = seed U n := by
    apply bank_eq_self
    intro x
    exact (seed_work U n x).symm
  simp only [stackCfg,hbank] at hsim
  exact ⟨T,hT,by simpa only [workProgram,worked] using hsim⟩

theorem worked_raw {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) (x : SourceCSPFirstRowController.Stack q) :
    worked U n a (rawEmbedding q x) = U x := by
  rw [worked,bank_outside]
  · exact seed_raw U n x
  · rintro ⟨y,hy⟩
    cases hy

theorem worked_saved {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) :
    worked U n a workSaved =
      (PrefixCompositeEndpoint.sourceFields n a q).reverse := by
  change bank (workEmbedding q) (seed U n)
    (PrefixComposite.finalBank n a q [] [] [])
    (workEmbedding q pairSaved) = _
  rw [bank_at]
  rw [show pairSaved = PrefixCopy.pairEmbedding
      (.inl (.inl (.inl 2))) by rfl,
    PrefixCompositeEndpoint.final_pair_projection]
  simp only [List.append_nil]
  change PairUnitLift.pairBank n n 0
    (PrefixCompositeEndpoint.sourceFields n a q).reverse []
    (List.replicate ((3*a+2+8*(a*a))*n) true)
    (.inl (.inl 2)) = _
  rw [← show PairUnitLift.unitEmbedding (.inl 2) =
      (.inl (.inl 2) : PairUnitLift.Stack) by
        simp [PairUnitLift.unitEmbedding,PairUnitLift.ordinalCell],
      PairUnitLift.pairBank,bank_at]
  rfl

theorem worked_count {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) :
    worked U n a workCount =
      List.replicate ((3*a+2+8*(a*a))*n) true := by
  change bank (workEmbedding q) (seed U n)
    (PrefixComposite.finalBank n a q [] [] [])
    (workEmbedding q pairCount) = _
  rw [bank_at]
  rw [show pairCount = PrefixCopy.pairEmbedding
      (.inl (.inl (.inl 4))) by rfl,
    PrefixCompositeEndpoint.final_pair_projection]
  simp only [List.append_nil]
  change PairUnitLift.pairBank n n 0
    (PrefixCompositeEndpoint.sourceFields n a q).reverse []
    (List.replicate ((3*a+2+8*(a*a))*n) true)
    (.inl (.inl 4)) = _
  rw [← show PairUnitLift.unitEmbedding (.inl 4) =
      (.inl (.inl 4) : PairUnitLift.Stack) by
        simp [PairUnitLift.unitEmbedding,PairUnitLift.ordinalCell],
      PairUnitLift.pairBank,bank_at]
  rfl

#print axioms seed_run
#print axioms work_run
#print axioms worked_raw

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientWork
