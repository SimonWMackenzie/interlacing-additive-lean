import CurrentAdditive.V39WTable
import CurrentAdditive.V39PhysicalSampleBudget

/-! Exact byte-layout bridge from the current sampler to the current table
caller. This is a representation equality only; all distributional claims
remain with the current sampler. Coordinate order and duplicates remain. -/

namespace CurrentAdditive.V39WEntry
noncomputable section
open Paper2 EthInapproximability.CurrentPaper

theorem tupleWord_flatten {A : Type} (f : A → List Bool) (m : Nat)
    (x : Fin m → A) :
    V39GeneratorCode.tupleWord f m x = (List.ofFn (fun i => f (x i))).flatten := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [V39GeneratorCode.tupleWord, List.ofFn_succ, List.flatten_cons]
    exact congrArg (fun z => f (x 0) ++ z) (ih (Fin.tail x))

variable {p s q₁ q₂ w Q : Nat}
variable [NeZero p] [NeZero q₁] [NeZero q₂] [NeZero s]
  [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

/-- The forward sample bytes used by the entry program are literally the
current sampler's output bytes, without orientation or resampling. -/
theorem sampleWord_writer_layout (g : EncodedGraph.Graph) [NeZero g.vertices]
    (K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    V39GeneratorCode.sampleWord g.vertices p q₁ q₂ s w Q K m (xs,ys) =
      (rowWords g K m xs).flatten ++ (colWords g K m ys).flatten := by
  rw [V39PhysicalSample.sampleWord_parser_layout,
    tupleWord_flatten,tupleWord_flatten]
  rfl

theorem bankA_forward_sample (g : EncodedGraph.Graph) [NeZero g.vertices]
    (r K m x y : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K)
    (out : List Bool) :
    bankA g r K m m xs ys x y out fwA =
      V39GeneratorCode.sampleWord g.vertices p q₁ q₂ s w Q K m (xs,ys) := by
  rw [sampleWord_writer_layout]
  rfl

#print axioms tupleWord_flatten
#print axioms sampleWord_writer_layout
#print axioms bankA_forward_sample
end
end CurrentAdditive.V39WEntry
