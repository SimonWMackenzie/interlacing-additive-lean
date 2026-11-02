import Paper2.A4Definitions

/-!
# Paper A (lock v12), lane `owner:a-model-1`, segment 4a: uniform-tape lemmas for D-A1

Author decision D-A1 (27 September 2026, `AUTHOR_DECISIONS_2026-09-27.md`, option (c)): "a
deterministic `BitMachine` on `pair input tape`; the tape is uniform over a fixed polynomial length
R(|input|), and the machine reads a prefix. Lemma 'a prefix or segment of a uniform tape is uniform
and independent' to be proved."

Lock v12 `sections/01-introduction.tex:74` ("A randomized estimator must succeed with probability at
least $2/3$ on every input") and `:90` ("Time, random-bit count, and output length are polynomial in
the encoding length of $\Phi$ on every tape").

This file proves exactly that lemma, for the admitted DRAFT law
`Paper2.Unit4Shell.Definitions.uniformTape` (reused by exact name, never edited):
* `uniformTape_split_prob`: the pushforward of `uniformTape (r0 + r * r1)` under splitting into a
  prefix of length `r0` and `r` consecutive blocks of length `r1` is `uniformTape r0` times
  `(uniformTape r1).iid r` (the admitted `FiniteLaw.prod` / `FiniteLaw.iid`), on every event;
* `uniformTape_append_prob`: prefix and suffix of a uniform tape are uniform and independent;
* `uniformTape_prefix_prob`, `uniformTape_take_prob`: a prefix of a uniform tape is uniform;
* `uniformTape_prob_ofFn_congr`: events of the tape WORD depend only on the length.

No ledger row is closed.
-/

namespace Paper2.AModel

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

/-- A bijection that transports weights transports every event probability. -/
theorem prob_equiv {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (ν : FiniteLaw β)
    (e : α ≃ β) (hw : ∀ a, ν.weight (e a) = μ.weight a) (E : β → Prop) :
    μ.prob (fun a => E (e a)) = ν.prob E := by
  classical
  unfold FiniteLaw.prob
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : E (e a) <;> simp [h, hw]

@[simp] theorem uniformTape_weight (r : ℕ) (t : Fin r → Bool) :
    (uniformTape r).weight t = (1 / 2 : ℝ) ^ r := rfl

/-- Events of the tape word `List.ofFn t` depend only on the tape length. -/
theorem uniformTape_prob_ofFn_congr {n m : ℕ} (h : n = m) (F : List Bool → Prop) :
    (uniformTape n).prob (fun t => F (List.ofFn t)) =
      (uniformTape m).prob (fun t => F (List.ofFn t)) := by
  subst h; rfl

/-- The prefix/suffix split of an `r0 + r1` tape (`Fin.castAdd` / `Fin.natAdd` coordinates). -/
def appendEquiv (r0 r1 : ℕ) : (Fin (r0 + r1) → Bool) ≃ (Fin r0 → Bool) × (Fin r1 → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin r0) (Fin r1) Bool)

@[simp] theorem appendEquiv_fst (r0 r1 : ℕ) (t : Fin (r0 + r1) → Bool) (i : Fin r0) :
    (appendEquiv r0 r1 t).1 i = t (Fin.castAdd r1 i) := by
  simp [appendEquiv, Equiv.sumArrowEquivProdArrow]

@[simp] theorem appendEquiv_snd (r0 r1 : ℕ) (t : Fin (r0 + r1) → Bool) (j : Fin r1) :
    (appendEquiv r0 r1 t).2 j = t (Fin.natAdd r0 j) := by
  simp [appendEquiv, Equiv.sumArrowEquivProdArrow]

/-- **Prefix and suffix of a uniform tape are uniform and independent** (D-A1 tape lemma). -/
theorem uniformTape_append_prob (r0 r1 : ℕ)
    (E : (Fin r0 → Bool) × (Fin r1 → Bool) → Prop) :
    (uniformTape (r0 + r1)).prob (fun t => E (appendEquiv r0 r1 t)) =
      ((uniformTape r0).prod (uniformTape r1)).prob E := by
  apply prob_equiv
  intro t
  simp [FiniteLaw.prod, pow_add]

/-- The split of an `r0 + r * r1` tape into a prefix of length `r0` followed by `r` consecutive
blocks of length `r1`; block `i`, position `j` is tape position `r0 + (j + r1 * i)`
(Mathlib's `finProdFinEquiv`). -/
def splitEquiv (r0 r r1 : ℕ) :
    (Fin (r0 + r * r1) → Bool) ≃ (Fin r0 → Bool) × (Fin r → Fin r1 → Bool) :=
  (appendEquiv r0 (r * r1)).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.curry (Fin r) (Fin r1) Bool)))

@[simp] theorem splitEquiv_fst (r0 r r1 : ℕ) (t : Fin (r0 + r * r1) → Bool) (i : Fin r0) :
    (splitEquiv r0 r r1 t).1 i = t (Fin.castAdd (r * r1) i) := by
  simp [splitEquiv]

@[simp] theorem splitEquiv_snd (r0 r r1 : ℕ) (t : Fin (r0 + r * r1) → Bool) (i : Fin r)
    (j : Fin r1) :
    (splitEquiv r0 r r1 t).2 i j = t (Fin.natAdd r0 (finProdFinEquiv (i, j))) := by
  simp [splitEquiv, Equiv.arrowCongr, Equiv.curry]

/-- The block coordinate is the literal position `r0 + (j + r1 * i)`. -/
theorem splitEquiv_snd_val (r0 r r1 : ℕ) (i : Fin r) (j : Fin r1) :
    (Fin.natAdd r0 (finProdFinEquiv (i, j)) : Fin (r0 + r * r1)).val = r0 + (j.val + r1 * i.val) := by
  simp [finProdFinEquiv]

/-- **The pushforward of `uniformTape (r0 + r * r1)` under splitting equals
`uniformTape r0` times `(uniformTape r1)^r`** (D-A1 tape lemma: a prefix and `r` disjoint segments
of a uniform tape are uniform and independent), on every event. -/
theorem uniformTape_split_prob (r0 r r1 : ℕ)
    (E : (Fin r0 → Bool) × (Fin r → Fin r1 → Bool) → Prop) :
    (uniformTape (r0 + r * r1)).prob (fun t => E (splitEquiv r0 r r1 t)) =
      ((uniformTape r0).prod ((uniformTape r1).iid r)).prob E := by
  apply prob_equiv
  intro t
  simp only [FiniteLaw.prod, FiniteLaw.iid, uniformTape_weight, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add, Nat.mul_comm r1 r]

/-- Pointwise form of the same pushforward identity (weights agree along the bijection). -/
theorem uniformTape_split_weight (r0 r r1 : ℕ) (t : Fin (r0 + r * r1) → Bool) :
    ((uniformTape r0).prod ((uniformTape r1).iid r)).weight (splitEquiv r0 r r1 t) =
      (uniformTape (r0 + r * r1)).weight t := by
  simp only [FiniteLaw.prod, FiniteLaw.iid, uniformTape_weight, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add, Nat.mul_comm r1 r]

/-- An event of the first factor of a product law has its marginal probability. -/
theorem prod_prob_fst {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (ν : FiniteLaw β)
    (F : α → Prop) : (μ.prod ν).prob (fun x => F x.1) = μ.prob F := by
  classical
  rw [FiniteLaw.prod_prob μ ν (fun a _ => F a)]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : F a
  · simp [h, ν.total]
  · simp [h]

/-- **A prefix of a uniform tape is uniform** (Fin form). -/
theorem uniformTape_prefix_prob (r0 r1 : ℕ) (F : (Fin r0 → Bool) → Prop) :
    (uniformTape (r0 + r1)).prob (fun t => F (fun i => t (Fin.castAdd r1 i))) =
      (uniformTape r0).prob F := by
  have h := uniformTape_append_prob r0 r1 (fun x => F x.1)
  rw [prod_prob_fst] at h
  rw [← h]
  congr 1

/-- The tape word of a split tape is the prefix word followed by the suffix word. -/
theorem ofFn_append_split (r0 r1 : ℕ) (t : Fin (r0 + r1) → Bool) :
    List.ofFn t = List.ofFn (appendEquiv r0 r1 t).1 ++ List.ofFn (appendEquiv r0 r1 t).2 := by
  rw [List.ofFn_add]
  congr 1

/-- **Prefix and suffix WORDS of a uniform tape are uniform and independent** (list form). -/
theorem uniformTape_take_drop_prob (r0 r1 : ℕ) (F : List Bool → List Bool → Prop) :
    (uniformTape (r0 + r1)).prob
        (fun t => F ((List.ofFn t).take r0) ((List.ofFn t).drop r0)) =
      ((uniformTape r0).prod (uniformTape r1)).prob
        (fun x => F (List.ofFn x.1) (List.ofFn x.2)) := by
  rw [← uniformTape_append_prob r0 r1 (fun x => F (List.ofFn x.1) (List.ofFn x.2))]
  congr 1
  funext t
  rw [ofFn_append_split r0 r1 t]
  have hl : (List.ofFn (appendEquiv r0 r1 t).1).length = r0 := List.length_ofFn
  rw [List.take_left' hl, List.drop_left' hl]

/-- **Reading a prefix of length `r ≤ R` of a uniform length-`R` tape gives the uniform law on
length-`r` words** (list form: the machine's view `List.take r` of its tape word). -/
theorem uniformTape_take_prob {r R : ℕ} (h : r ≤ R) (F : List Bool → Prop) :
    (uniformTape R).prob (fun t => F ((List.ofFn t).take r)) =
      (uniformTape r).prob (fun t => F (List.ofFn t)) := by
  obtain ⟨s, rfl⟩ : ∃ s, R = r + s := ⟨R - r, by omega⟩
  have h1 := uniformTape_take_drop_prob r s (fun a _ => F a)
  simp only at h1
  rw [h1]
  exact prod_prob_fst (uniformTape r) (uniformTape s) (fun a => F (List.ofFn a))

end Paper2.AModel

#print axioms Paper2.AModel.prob_equiv
#print axioms Paper2.AModel.uniformTape_append_prob
#print axioms Paper2.AModel.uniformTape_split_prob
#print axioms Paper2.AModel.uniformTape_split_weight
#print axioms Paper2.AModel.uniformTape_prefix_prob
#print axioms Paper2.AModel.uniformTape_take_drop_prob
#print axioms Paper2.AModel.uniformTape_take_prob
