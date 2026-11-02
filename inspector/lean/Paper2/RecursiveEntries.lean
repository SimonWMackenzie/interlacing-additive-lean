import Paper2.SourceMatrix
import Paper2.IndexedMatrices

/-!
# Recursive entries of the actual full-product construction

Frozen v12, `appendices/D-implementation.tex`, equation `eq:recursive-entry`
and the paragraph immediately following it (U11).

The carrier recursion below is the literal two-interlace successor, not a
sequence of matrices supplied with assumed gap properties. Its evaluator
follows one request to the preceding level and terminates at one seed entry.
Public fixed tails and the public activity map are parameters; neither a
coloring nor a communication protocol selects the constructor.

This file verifies entry identity and the number of recursive requests. It
does not regard access to a stored tuple as unit-cost machine computation,
and does not yet prove generation laws or a Turing-machine runtime bound.
-/

namespace Paper2.RecursiveEntries

open SourceMatrix

/-- Literal row/column carriers for repeated complete-product successors. -/
def Carriers (X₀ Y₀ I : Type) (s q₁ q₂ w Q : ℕ) : ℕ → Type × Type
  | 0 => (X₀, Y₀)
  | k + 1 =>
      let previous := Carriers X₀ Y₀ I s q₁ q₂ w Q k
      ((Fin Q → Fin w × TaggedColumn q₁ q₂ s previous.2),
        Fin Q × (Fin w → RawRow q₁ q₂ s previous.1 I))

variable {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ}

abbrev Row (X₀ Y₀ I : Type) (s q₁ q₂ w Q k : ℕ) :=
  (Carriers X₀ Y₀ I s q₁ q₂ w Q k).1

abbrev Column (X₀ Y₀ I : Type) (s q₁ q₂ w Q k : ℕ) :=
  (Carriers X₀ Y₀ I s q₁ q₂ w Q k).2

def carrierFintypes [Fintype X₀] [Fintype Y₀] [Fintype I] :
    (k : ℕ) → Fintype (Row X₀ Y₀ I s q₁ q₂ w Q k) ×
      Fintype (Column X₀ Y₀ I s q₁ q₂ w Q k)
  | 0 => (inferInstanceAs (Fintype X₀), inferInstanceAs (Fintype Y₀))
  | k + 1 =>
      let previous := carrierFintypes k
      letI : Fintype (Row X₀ Y₀ I s q₁ q₂ w Q k) := previous.1
      letI : Fintype (Column X₀ Y₀ I s q₁ q₂ w Q k) := previous.2
      (inferInstanceAs (Fintype (Fin Q → Fin w ×
        TaggedColumn q₁ q₂ s (Column X₀ Y₀ I s q₁ q₂ w Q k))),
        inferInstanceAs (Fintype (Fin Q × (Fin w →
          RawRow q₁ q₂ s (Row X₀ Y₀ I s q₁ q₂ w Q k) I))))

instance rowFintype [Fintype X₀] [Fintype Y₀] [Fintype I] (k : ℕ) :
    Fintype (Row X₀ Y₀ I s q₁ q₂ w Q k) := (carrierFintypes k).1

instance columnFintype [Fintype X₀] [Fintype Y₀] [Fintype I] (k : ℕ) :
    Fintype (Column X₀ Y₀ I s q₁ q₂ w Q k) := (carrierFintypes k).2

/-- The fixed tail for every level is independent of the source promise. -/
abbrev Tails (X₀ Y₀ I : Type) (s q₁ q₂ w Q : ℕ) :=
  (k : ℕ) → Tail s (Column X₀ Y₀ I s q₁ q₂ w Q k)

/-- First select the outer column index, then its row's inner bin, and
finally the one base entry requested by the raw source rule. -/
def request [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q (k + 1))
    (y : Column X₀ Y₀ I s q₁ q₂ w Q (k + 1)) :
    Row X₀ Y₀ I s q₁ q₂ w Q k × Column X₀ Y₀ I s q₁ q₂ w Q k :=
  baseRequest activity (y.2 (x y.1).1) (forgetTag (ξ k) (x y.1).2)

/-- Complete-product iteration using the already defined actual successor. -/
def matrix [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) :
    (k : ℕ) → Row X₀ Y₀ I s q₁ q₂ w Q k → Column X₀ Y₀ I s q₁ q₂ w Q k → Bool
  | 0 => F
  | k + 1 => successor (matrix F activity ξ k) activity (ξ k) w Q

/-- Evaluate by descending to a single preceding entry at each level. -/
def evaluate [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) :
    (k : ℕ) → Row X₀ Y₀ I s q₁ q₂ w Q k → Column X₀ Y₀ I s q₁ q₂ w Q k → Bool
  | 0 => F
  | k + 1 => fun x y =>
      let p := request activity ξ k x y
      evaluate F activity ξ k p.1 p.2

theorem matrix_succ_entry [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q (k + 1))
    (y : Column X₀ Y₀ I s q₁ q₂ w Q (k + 1)) :
    matrix F activity ξ (k + 1) x y =
      matrix F activity ξ k (request activity ξ k x y).1 (request activity ξ k x y).2 := rfl

/-- The evaluator computes the same entry of the recursively constructed
matrix, including all tags and repeated labels. -/
theorem evaluate_eq_matrix [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (y : Column X₀ Y₀ I s q₁ q₂ w Q k) :
    evaluate F activity ξ k x y = matrix F activity ξ k x y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih (request activity ξ k x y).1 (request activity ξ k x y).2

/-- The unique original input pair reached by the evaluator. -/
def seedRequest [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) :
    (k : ℕ) → Row X₀ Y₀ I s q₁ q₂ w Q k → Column X₀ Y₀ I s q₁ q₂ w Q k → X₀ × Y₀
  | 0 => fun x y => (x, y)
  | k + 1 => fun x y =>
      let p := request activity ξ k x y
      seedRequest activity ξ k p.1 p.2

theorem evaluate_eq_seed_entry [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (y : Column X₀ Y₀ I s q₁ q₂ w Q k) :
    evaluate F activity ξ k x y =
      F (seedRequest activity ξ k x y).1 (seedRequest activity ξ k x y).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih (request activity ξ k x y).1 (request activity ξ k x y).2

/-- Number of descents in that same evaluation. This counts recursive
requests only, not the cost of scanning any selected tuple. -/
def requestCount [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) :
    (k : ℕ) → Row X₀ Y₀ I s q₁ q₂ w Q k → Column X₀ Y₀ I s q₁ q₂ w Q k → ℕ
  | 0 => fun _ _ => 0
  | k + 1 => fun x y =>
      let p := request activity ξ k x y
      1 + requestCount activity ξ k p.1 p.2

theorem requestCount_eq [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (y : Column X₀ Y₀ I s q₁ q₂ w Q k) : requestCount activity ξ k x y = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change 1 + requestCount activity ξ k _ _ = k + 1
      rw [ih]
      omega

/-- Indexed output table. Sampled labels remain separate even when equal. -/
def table [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ) {m n : ℕ}
    (xs : Fin m → Row X₀ Y₀ I s q₁ q₂ w Q k)
    (ys : Fin n → Column X₀ Y₀ I s q₁ q₂ w Q k) : Fin m → Fin n → Bool :=
  fun i j => evaluate F activity ξ k (xs i) (ys j)

theorem table_eq_sampleMatrix [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (k : ℕ) {m n : ℕ}
    (xs : Fin m → Row X₀ Y₀ I s q₁ q₂ w Q k)
    (ys : Fin n → Column X₀ Y₀ I s q₁ q₂ w Q k) :
    table F activity ξ k xs ys = sampleMatrix (matrix F activity ξ k) xs ys := by
  funext i j
  exact evaluate_eq_matrix F activity ξ k (xs i) (ys j)

end Paper2.RecursiveEntries
