import CurrentAdditive.V38SourceFrontClock

noncomputable section
namespace CurrentAdditive.V38SourceFront

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

abbrev outputBank := @V38SourceWidths.outputBank

theorem source_value {t : ℕ} (x : YaoSource t) (k : WStack t 0) :
    outputBank x (.source k) = sourceReady x k := by
  change V38SourceWidths.outputBank x (.source k) = _
  rw [V38SourceWidths.output_foreign x (.source k)
    (by intro i h; cases h)]
  exact V38SourceDegree.output_source x k

theorem degree_value {t : ℕ} (x : YaoSource t) :
    outputBank x (.degree 3) =
      List.replicate (5*paddedEdgeBits x.2.1+14*t) true := by
  change V38SourceWidths.outputBank x (.degree 3) = _
  rw [V38SourceWidths.output_foreign x (.degree 3)
    (by intro i h; cases h)]
  exact V38SourceDegree.output_degree x

theorem blank_value {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hw : ∀ k : Fin 8, Cell.width k ≠ j)
    (hd : ∀ k : Fin 16, Cell.degree k ≠ j)
    (hs : ∀ k : WStack t 0, Cell.source k ≠ j) :
    outputBank x j = [] := by
  change V38SourceWidths.outputBank x j = []
  rw [V38SourceWidths.output_foreign x j hw]
  exact V38SourceDegree.output_blank x j hd hs

theorem source_public {t : ℕ} (x : YaoSource t) :
    outputBank x (.source (sN 1)) =
      Paper2.UnaryFieldListParserScratch.tokens (List.ofFn (flatten x.2.2)) ∧
    outputBank x (.source (sN 3)) = List.replicate x.1 true ∧
    outputBank x (.source (sN 5)) = List.replicate (paddedEdgeBits x.2.1) true ∧
    outputBank x (.source (sN 6)) = List.replicate (paddedEdgeCount x.2.1) true ∧
    outputBank x (.source (sN 9)) = List.replicate (arity t) true := by
  simp only [source_value]
  obtain ⟨h1,h3,_,h5,h6,h9⟩ := sourceReady_public_cells x
  exact ⟨h1,h3,h5,h6,h9⟩

theorem genuine_width_value {t : ℕ} (x : YaoSource t) :
    outputBank x (.width 5) =
      List.replicate (paddedEdgeCount x.2.1 * arity t) true :=
  V38SourceWidths.output_genuine x

theorem padded_width_value {t : ℕ} (x : YaoSource t) :
    outputBank x (.width 3) =
      List.replicate (paddedEdgeCount x.2.1 * (arity t + 1)) true :=
  V38SourceWidths.output_padded x

#print axioms source_public
#print axioms blank_value
#print axioms degree_value
#print axioms genuine_width_value
#print axioms padded_width_value
end CurrentAdditive.V38SourceFront
