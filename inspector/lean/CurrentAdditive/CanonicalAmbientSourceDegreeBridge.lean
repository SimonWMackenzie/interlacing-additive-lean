import CurrentAdditive.CanonicalAmbientDimensionsFull

/-! Public source cells and empty foreign cells after the degree stage. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceDegreeOutput {t : ℕ} (x : YaoSource t) :
    Cell t 16 → List Bool :=
  bank (degreeEmbed t 16) (sourceDegreeBank x)
    (YaoDegreeMachine.finalBank
      (fun i : Fin 16 => sourceDegreeBank x (.degree i))
      (paddedEdgeBits x.2.1) t)

theorem sourceDegreeOutput_degree {t : ℕ} (x : YaoSource t) :
    sourceDegreeOutput x (.degree 3) =
      List.replicate (publicFieldDegree (paddedEdgeBits x.2.1) t) true := by
  simpa [sourceDegreeOutput, degreeEmbed] using
    (bank_at (degreeEmbed t 16) (sourceDegreeBank x)
      (YaoDegreeMachine.finalBank
        (fun i : Fin 16 => sourceDegreeBank x (.degree i))
        (paddedEdgeBits x.2.1) t) (3 : Fin 16)).trans
      (YaoDegreeInterface.output_degree
        (fun i : Fin 16 => sourceDegreeBank x (.degree i))
        (paddedEdgeBits x.2.1) t)

theorem sourceDegreeOutput_foreign {t : ℕ} (x : YaoSource t)
    (j : Cell t 16) (h : ¬ ∃ i : Fin 16, degreeEmbed t 16 i = j) :
    sourceDegreeOutput x j = sourceBank x j := by
  rw [sourceDegreeOutput, bank_outside (degreeEmbed t 16) _ _ j h]
  have h0 : j ≠ .degree 0 := by
    intro he
    exact h ⟨0, by simpa [degreeEmbed] using he.symm⟩
  have h1 : j ≠ .degree 1 := by
    intro he
    exact h ⟨1, by simpa [degreeEmbed] using he.symm⟩
  have h2 : j ≠ .degree 2 := by
    intro he
    exact h ⟨2, by simpa [degreeEmbed] using he.symm⟩
  simp [sourceDegreeBank, degreeInputBank, h0, h1, h2]

theorem sourceDegreeOutput_source {t : ℕ} (x : YaoSource t)
    (i : Fin 40) :
    sourceDegreeOutput x (.source (sN i)) = sourceReady x (sN i) := by
  rw [sourceDegreeOutput_foreign x (.source (sN i)) (by
    intro ⟨j, hj⟩; cases hj)]
  exact sourceBank_source x (sN i)

theorem sourceDegreeOutput_public {t : ℕ} (x : YaoSource t) :
    sourceDegreeOutput x (.source (sN 3)) = List.replicate x.1 true ∧
    sourceDegreeOutput x (.source (sN 6)) =
      List.replicate (paddedEdgeCount x.2.1) true ∧
    sourceDegreeOutput x (.source (sN 9)) =
      List.replicate (arity t) true := by
  obtain ⟨_, hv, _, hH, hK⟩ := sourceReady_public_cells x
  simp [sourceDegreeOutput_source, hv, hH, hK]

theorem sourceDegreeOutput_foreign_blank {t : ℕ} (x : YaoSource t) :
    (∀ i : Fin 8, sourceDegreeOutput x (.width i) = []) ∧
    (∀ i : Fin 12, sourceDegreeOutput x (.selector i) = []) ∧
    (∀ i : Fin 9, sourceDegreeOutput x (.square i) = []) ∧
    (∀ i : Fin 11, sourceDegreeOutput x (.dimensions i) = []) ∧
    (∀ i : Fin 3, sourceDegreeOutput x (.threshold i) = []) ∧
    sourceDegreeOutput x (.copyScratch 0) = [] := by
  have hblank (j : Cell t 16)
      (hdegree : ¬ ∃ i : Fin 16, degreeEmbed t 16 i = j)
      (hsource : ¬ ∃ i : WStack t 0, sourceEmbed t 16 i = j) :
      sourceDegreeOutput x j = [] := by
    rw [sourceDegreeOutput_foreign x j hdegree]
    exact bank_outside (sourceEmbed t 16) (blank t 16)
      (sourceReady x) j hsource
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hblank (.width i) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)
  · intro i
    exact hblank (.selector i) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)
  · intro i
    exact hblank (.square i) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)
  · intro i
    exact hblank (.dimensions i) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)
  · intro i
    exact hblank (.threshold i) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)
  · exact hblank (.copyScratch 0) (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)

#print axioms sourceDegreeOutput_degree
#print axioms sourceDegreeOutput_source
#print axioms sourceDegreeOutput_foreign_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
