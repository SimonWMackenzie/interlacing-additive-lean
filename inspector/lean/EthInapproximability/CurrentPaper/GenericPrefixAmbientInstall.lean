import EthInapproximability.CurrentPaper.GenericPrefixAmbientWork

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientInstall

open Turing BitMachineEncoding BitMachineStackEmbedding
open PrefixAmbientCopy PrefixAmbientSeed PrefixAmbientWork
open scoped Classical

theorem saved_ne {q : Nat} : (workSaved : PrefixAmbientCopy.Stack q) ≠ rawSaved := by
  simp [workSaved,rawSaved,workEmbedding,rawEmbedding]
theorem count_ne {q : Nat} : (workCount : PrefixAmbientCopy.Stack q) ≠ rawCount := by
  simp [workCount,rawCount,workEmbedding,rawEmbedding]
theorem workSaved_ne_scratch {q : Nat} :
    (workSaved : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [workSaved,workEmbedding,scratch]
theorem workCount_ne_scratch {q : Nat} :
    (workCount : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [workCount,workEmbedding,scratch]
theorem rawSaved_ne_scratch {q : Nat} :
    (rawSaved : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [rawSaved,rawEmbedding,scratch]
theorem rawCount_ne_scratch {q : Nat} :
    (rawCount : PrefixAmbientCopy.Stack q) ≠ scratch q := by
  simp [rawCount,rawEmbedding,scratch]
theorem rawSaved_ne_rawCount {q : Nat} :
    (rawSaved : PrefixAmbientCopy.Stack q) ≠ rawCount := by
  simp [rawSaved,rawCount,rawEmbedding,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.countCell]
theorem workCount_ne_rawSaved {q : Nat} :
    (workCount : PrefixAmbientCopy.Stack q) ≠ rawSaved := by
  simp [workCount,rawSaved,workEmbedding,rawEmbedding]

noncomputable def savedProgram (q : Nat) :=
  PrefixAmbientCopy.copyProgram (workSaved (q := q)) rawSaved
    saved_ne workSaved_ne_scratch rawSaved_ne_scratch
noncomputable def countProgram (q : Nat) :=
  PrefixAmbientCopy.copyProgram (workCount (q := q)) rawCount
    count_ne workCount_ne_scratch rawCount_ne_scratch
noncomputable def program (q : Nat) :=
  BitMachineRawSequence.program (savedProgram q) (countProgram q)
    BitMachineCopy.Label.scan none none

noncomputable def savedWord (n a q : Nat) : List Bool :=
  (PrefixCompositeEndpoint.sourceFields n a q).reverse
noncomputable def countWord (n a : Nat) : List Bool :=
  List.replicate ((3*a+2+8*(a*a))*n) true

noncomputable def installed {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) : PrefixAmbientCopy.Stack q → List Bool :=
  Function.update
    (Function.update (worked U n a) rawSaved (savedWord n a q))
    rawCount (countWord n a)

theorem worked_scratch {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) : worked U n a (scratch q) = [] := by
  rw [worked,bank_outside]
  · have h : scratch q ≠ workN := by
      simp [scratch,workN,workEmbedding]
    rw [seed,Function.update_of_ne h,initial_scratch]
  · rintro ⟨x,hx⟩
    cases hx

theorem installed_run {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat)
    (hsaved : U (.inr SourceClauseRowWriterCleanup.savedCell) = [])
    (hcount : U (.inr SourceClauseRowWriterCleanup.countCell) = []) :
    ∃ T ≤ 2*(savedWord n a q).length + 2 +
        (2*(countWord n a).length+2) + 1,
      ((advance (program q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,none),worked U n a⟩ :
          TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
        ⟨none,(none,none),installed U n a⟩ := by
  let W := worked U n a
  let B1 := Function.update W rawSaved (savedWord n a q)
  have hsrcS : W workSaved = savedWord n a q := worked_saved U n a
  have hdstS : W rawSaved = [] :=
    (worked_raw U n a (.inr SourceClauseRowWriterCleanup.savedCell)).trans hsaved
  have hwS : W (scratch q) = [] := worked_scratch U n a
  have hsrcC : B1 workCount = countWord n a :=
    (Function.update_of_ne workCount_ne_rawSaved _ _).trans (worked_count U n a)
  have hdstC : B1 rawCount = [] :=
    (Function.update_of_ne (Ne.symm rawSaved_ne_rawCount) _ _).trans
      ((worked_raw U n a (.inr SourceClauseRowWriterCleanup.countCell)).trans hcount)
  have hwC : B1 (scratch q) = [] :=
    (Function.update_of_ne (Ne.symm rawSaved_ne_scratch) _ _).trans hwS
  have hS := PrefixAmbientCopy.copy_run workSaved rawSaved
    saved_ne workSaved_ne_scratch rawSaved_ne_scratch
    W (savedWord n a q) hsrcS hdstS hwS
  have hC := PrefixAmbientCopy.copy_run workCount rawCount
    count_ne workCount_ne_scratch rawCount_ne_scratch
    B1 (countWord n a) hsrcC hdstC hwC
  obtain ⟨T,hT,hr⟩ := BitMachineRawSequence.runs
    (savedProgram q) (countProgram q)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none
    W B1 (installed U n a)
    (2*(savedWord n a q).length+2)
    (2*(countWord n a).length+2) hS hC
  exact ⟨T,by omega,by simpa only [program,W,B1,installed] using hr⟩

theorem installed_raw {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n a : Nat) (x : SourceCSPFirstRowController.Stack q) :
    installed U n a (rawEmbedding q x) =
      Function.update
        (Function.update U (.inr SourceClauseRowWriterCleanup.savedCell)
          (savedWord n a q))
        (.inr SourceClauseRowWriterCleanup.countCell) (countWord n a) x := by
  by_cases hc : x = (.inr SourceClauseRowWriterCleanup.countCell :
      SourceCSPFirstRowController.Stack q)
  · subst x
    simp [installed,rawCount,rawEmbedding]
  · by_cases hs : x = (.inr SourceClauseRowWriterCleanup.savedCell :
        SourceCSPFirstRowController.Stack q)
    · subst x
      simp [installed,rawSaved,rawCount,rawEmbedding,
        SourceClauseRowWriterCleanup.savedCell,
        SourceClauseRowWriterCleanup.countCell]
    · have h1 : rawEmbedding q x ≠ rawCount := fun h =>
        hc ((rawEmbedding q).injective h)
      have h2 : rawEmbedding q x ≠ rawSaved := fun h =>
        hs ((rawEmbedding q).injective h)
      rw [installed,Function.update_of_ne h1,Function.update_of_ne h2,
        worked_raw,Function.update_of_ne hc,Function.update_of_ne hs]

#print axioms installed_run
#print axioms installed_raw

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientInstall
