import CurrentAdditive.V39DeadRecursiveCode

namespace CurrentAdditive.V39DeadGenericCode

open Paper2.GeneratorCode Paper2.GeneratorSource
open CurrentAdditive.V39DeadTaggedCompiler

def recursiveCodes (n s q₁ q₂ w Q : ℕ) (row₀ col₀ : Code) : ℕ → Code × Code
  | 0 => (row₀, col₀)
  | k + 1 =>
    let previous := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    (copies Q (.append (.ticket w) (deadTaggedCode q₁ q₂ s previous.2)),
      .append (.ticket Q) (copies w (graphRowsCode (V := Fin n) q₁ q₂ s previous.1)))

theorem seed_eq (n p₀ q₁ q₂ s w Q k : ℕ) :
    recursiveCodes n s q₁ q₂ w Q (copies p₀ .bit) (.ticket p₀) k =
      deadCodes n p₀ q₁ q₂ s w Q k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [recursiveCodes, deadCodes, ih]

end CurrentAdditive.V39DeadGenericCode
