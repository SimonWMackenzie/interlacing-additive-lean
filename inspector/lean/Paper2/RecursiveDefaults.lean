import Paper2.RecursiveEntries

/-!
# Public default labels for the recursive construction

Frozen v12, Appendix D, the canonical fixed tail generated recursively with
fixed choices. Positive public widths and one public seed/item label give
explicit row and column defaults at every level. Thus the family of fixed
tails used by `RecursiveEntries` is constructed without a coloring, optimum,
source promise or enumeration of complete carrier sets.
-/

namespace Paper2.RecursiveEntries

open SourceMatrix

variable {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ}

/-- One public pair of valid labels at every level. The diagonal tag and
source-row summand are fixed constructor choices, not promise tests. -/
def defaultLabels (x₀ : X₀) (y₀ : Y₀) (item : I)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) :
    (k : ℕ) → Row X₀ Y₀ I s q₁ q₂ w Q k × Column X₀ Y₀ I s q₁ q₂ w Q k
  | 0 => (x₀, y₀)
  | k + 1 =>
      let previous := defaultLabels x₀ y₀ item hq₂ hw hQ k
      ((fun _ => (⟨0, hw⟩, .diagonal (⟨0, hq₂⟩, fun _ => previous.2))),
        (⟨0, hQ⟩, fun _ => .inr (item, previous.1)))

/-- The actual fixed tails consist of repeated canonical column labels. -/
def defaultTails (x₀ : X₀) (y₀ : Y₀) (item : I)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) : Tails X₀ Y₀ I s q₁ q₂ w Q :=
  fun k _ => (defaultLabels x₀ y₀ item hq₂ hw hQ k).2

theorem carriers_nonempty (x₀ : X₀) (y₀ : Y₀) (item : I)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) (k : ℕ) :
    Nonempty (Row X₀ Y₀ I s q₁ q₂ w Q k) ∧
      Nonempty (Column X₀ Y₀ I s q₁ q₂ w Q k) :=
  ⟨⟨(defaultLabels x₀ y₀ item hq₂ hw hQ k).1⟩,
    ⟨(defaultLabels x₀ y₀ item hq₂ hw hQ k).2⟩⟩

/-- Fixing these public defaults produces a total Boolean matrix at every
iteration. It is definitionally the same complete-product construction. -/
def defaultMatrix [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (x₀ : X₀) (y₀ : Y₀) (item : I)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) (k : ℕ) :
    Row X₀ Y₀ I s q₁ q₂ w Q k → Column X₀ Y₀ I s q₁ q₂ w Q k → Bool :=
  matrix F activity (defaultTails x₀ y₀ item hq₂ hw hQ) k

theorem defaultMatrix_entry [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (x₀ : X₀) (y₀ : Y₀) (item : I)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (y : Column X₀ Y₀ I s q₁ q₂ w Q k) :
    evaluate F activity (defaultTails x₀ y₀ item hq₂ hw hQ) k x y =
      defaultMatrix F activity x₀ y₀ item hq₂ hw hQ k x y :=
  evaluate_eq_matrix F activity _ k x y

end Paper2.RecursiveEntries
