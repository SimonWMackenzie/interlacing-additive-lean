import Paper2.RankLeaves
import Workspace.ProofLemmas.SublemmaPrecompNoIncrease
import Workspace.ProofLemmas.SublemmaPrecompEq

/-!
# Indexed samples and duplicate input labels

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Section 2,
Definition `def:interlace`, the paragraph introducing positive rational laws,
and the every-tape upper-bound and rank-restriction steps of
Theorem `thm:compression`.

The sampled inputs are their indices, not the set of values appearing in the
sample. Thus repetitions remain distinct labels. This file reuses the concrete
deterministic protocol model and checked precomposition theorems; it introduces
neither an abstract communication-cost oracle nor a new protocol datatype.

These are deterministic facts about each particular sample. Probability,
rational-law duplication, source construction and running-time bounds are
separate obligations.
-/

namespace Paper2

open Workspace.Types.CommComplexity Workspace.Types.Protocol
open RankLeaves

variable {X Y A B : Type*}

/-- The matrix printed from two indexed input lists. Equal sampled values
remain different inputs when their indices differ. -/
def sampleMatrix {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) : Fin m → Fin n → Bool :=
  fun i j => F (xs i) (ys j)

@[simp] theorem sampleMatrix_apply {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) (i : Fin m) (j : Fin n) :
    sampleMatrix F xs ys i j = F (xs i) (ys j) := rfl

/-- A fixed ambient protocol becomes a protocol for every indexed sample,
with exactly the same syntactic depth. -/
theorem sample_protocol {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) (P : Protocol X Y Bool)
    (hP : P.Computes F) :
    (Workspace.UpperBound.Protocol.comap xs ys P).cost = P.cost ∧
      (Workspace.UpperBound.Protocol.comap xs ys P).Computes
        (sampleMatrix F xs ys) := by
  refine ⟨Workspace.UpperBound.Protocol.comap_cost xs ys P, ?_⟩
  intro i j
  rw [Workspace.UpperBound.Protocol.comap_eval]
  exact hP (xs i) (ys j)

/-- Every-tape upper-bound preservation. No injectivity or nonemptiness of
the sample lists is needed. -/
theorem sample_D_le [Fintype X] [Fintype Y] {m n : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y) :
    D (sampleMatrix F xs ys) ≤ D F :=
  Workspace.ProofLemmas.SublemmaPrecompNoIncrease F xs ys

theorem sample_D_le_of_le [Fintype X] [Fintype Y] {m n c : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y)
    (hF : D F ≤ c) : D (sampleMatrix F xs ys) ≤ c :=
  (sample_D_le F xs ys).trans hF

/-- Duplicating labels without omitting any original row or column preserves
communication complexity exactly. This alone does not identify probability
laws with uniform measures on a duplication. -/
theorem pullback_D_eq_of_surjective [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (F : X → Y → Bool)
    (xs : A → X) (ys : B → Y)
    (hxs : Function.Surjective xs) (hys : Function.Surjective ys) :
    D (fun a b => F (xs a) (ys b)) = D F :=
  Workspace.ProofLemmas.SublemmaPrecompEq F xs ys hxs hys

theorem sample_D_eq_of_surjective [Fintype X] [Fintype Y] {m n : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y)
    (hxs : Function.Surjective xs) (hys : Function.Surjective ys) :
    D (sampleMatrix F xs ys) = D F :=
  pullback_D_eq_of_surjective F xs ys hxs hys

/-- The exact same input maps select the corresponding real matrix. -/
theorem realMatrix_pullback (F : X → Y → Bool)
    (xs : A → X) (ys : B → Y) :
    realMatrix (fun a b => F (xs a) (ys b)) =
      (realMatrix F).submatrix xs ys := rfl

/-- Rank cannot increase under arbitrary input maps, including repeated
labels. The statement is about the ordinary real zero--one matrix. -/
theorem pullback_rank_le [Fintype Y] [Fintype B] (F : X → Y → Bool)
    (xs : A → X) (ys : B → Y) :
    (realMatrix (fun a b => F (xs a) (ys b))).rank ≤
      (realMatrix F).rank := by
  rw [realMatrix_pullback]
  exact Matrix.rank_submatrix_le (realMatrix F) xs ys

theorem sample_rank_le [Fintype Y] {m n : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y) :
    (realMatrix (sampleMatrix F xs ys)).rank ≤ (realMatrix F).rank :=
  pullback_rank_le F xs ys

theorem sample_rank_le_of_le [Fintype Y] {m n r : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y)
    (hF : (realMatrix F).rank ≤ r) :
    (realMatrix (sampleMatrix F xs ys)).rank ≤ r :=
  (sample_rank_le F xs ys).trans hF

/-- Surjective duplication changes neither the real rank nor communication
complexity; the rank part follows by choosing right inverses. -/
theorem pullback_rank_eq_of_surjective [Fintype Y] [Fintype B] (F : X → Y → Bool)
    (xs : A → X) (ys : B → Y)
    (hxs : Function.Surjective xs) (hys : Function.Surjective ys) :
    (realMatrix (fun a b => F (xs a) (ys b))).rank =
      (realMatrix F).rank := by
  apply le_antisymm (pullback_rank_le F xs ys)
  have h := pullback_rank_le (fun a b => F (xs a) (ys b))
    (Function.surjInv hxs) (Function.surjInv hys)
  simpa only [Function.surjInv_eq] using h

theorem sample_rank_eq_of_surjective [Fintype Y] {m n : ℕ}
    (F : X → Y → Bool) (xs : Fin m → X) (ys : Fin n → Y)
    (hxs : Function.Surjective xs) (hys : Function.Surjective ys) :
    (realMatrix (sampleMatrix F xs ys)).rank = (realMatrix F).rank :=
  pullback_rank_eq_of_surjective F xs ys hxs hys

/-- Exchanging the two parties preserves deterministic communication cost. -/
theorem transpose_D [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    D (fun y x => F x y) = D F :=
  (Workspace.UpperBound.D_swap F).symm

theorem realMatrix_transpose (F : X → Y → Bool) :
    realMatrix (fun y x => F x y) = (realMatrix F).transpose := rfl

/-- Rank preservation needed before sampling the second side. -/
theorem transpose_rank [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    (realMatrix (fun y x => F x y)).rank = (realMatrix F).rank := by
  rw [realMatrix_transpose]
  exact Matrix.rank_transpose (realMatrix F)

@[simp] theorem sampleMatrix_transpose {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) :
    sampleMatrix (fun y x => F x y) ys xs =
      fun j i => sampleMatrix F xs ys i j := rfl

theorem sample_transpose_D {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) :
    D (sampleMatrix (fun y x => F x y) ys xs) =
      D (sampleMatrix F xs ys) :=
  transpose_D (sampleMatrix F xs ys)

theorem sample_transpose_rank {m n : ℕ} (F : X → Y → Bool)
    (xs : Fin m → X) (ys : Fin n → Y) :
    (realMatrix (sampleMatrix (fun y x => F x y) ys xs)).rank =
      (realMatrix (sampleMatrix F xs ys)).rank :=
  transpose_rank (sampleMatrix F xs ys)

end Paper2
