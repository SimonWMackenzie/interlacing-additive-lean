import Paper2.AModelTape

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial, 4e ingredient): the two tape blocks are uniform and independent

Carrier-free law lemmas for the composite decider's tape layout (reduction block = the first `I` bits, classifier block =
the `s` bits after position `L ≥ I`), from the ADMITTED `AModel.uniformTape_take_prob` and
`AModel.uniformTape_take_drop_prob` (reused by exact name) and the admitted `FiniteLaw.prod` weights.
No ledger row is closed. Nothing here is admitted.
-/

namespace Paper2.AEth4

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

open scoped BigOperators

/-- Product probability as a sum over the SECOND coordinate (the admitted `prod_prob` sums over the first). -/
theorem prod_prob_snd {α β : Type*} [Fintype α] [Fintype β] (μ : FiniteLaw α) (ν : FiniteLaw β)
    (E : α → β → Prop) :
    (μ.prod ν).prob (fun x => E x.1 x.2) = ∑ b, ν.weight b * μ.prob (fun a => E a b) := by
  classical
  simp only [FiniteLaw.prob, FiniteLaw.prod, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- **The reduction block and the classifier block of a uniform tape are uniform and independent.**
For `I ≤ L` and `L + s ≤ R`, the pair (first `I` bits, the `s` bits after position `L`) of a uniform length-`R`
tape has the product of the uniform laws. -/
theorem uniform_split_take_prob {I L s R : ℕ} (hIL : I ≤ L) (h : L + s ≤ R)
    (F : List Bool → List Bool → Prop) :
    (uniformTape R).prob (fun t =>
        F ((List.ofFn t).take I) (((List.ofFn t).drop L).take s)) =
      ((uniformTape I).prod (uniformTape s)).prob
        (fun x => F (List.ofFn x.1) (List.ofFn x.2)) := by
  have e : (fun t : Fin R → Bool =>
        F ((List.ofFn t).take I) (((List.ofFn t).drop L).take s)) =
      (fun t => (fun w : List Bool => F ((w.take L).take I) (w.drop L))
        ((List.ofFn t).take (L + s))) := by
    funext t
    simp only [List.take_take, List.drop_take]
    congr 2
    · omega
    · omega
  rw [e, Paper2.AModel.uniformTape_take_prob h (fun w => F ((w.take L).take I) (w.drop L))]
  have h2 := Paper2.AModel.uniformTape_take_drop_prob L s (fun a b => F (a.take I) b)
  simp only at h2
  have l1 := prod_prob_snd (uniformTape L) (uniformTape s)
    (fun a b => F ((List.ofFn a).take I) (List.ofFn b))
  have l2 := prod_prob_snd (uniformTape I) (uniformTape s)
    (fun a b => F (List.ofFn a) (List.ofFn b))
  simp only at l1 l2
  rw [h2, l1, l2]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact Paper2.AModel.uniformTape_take_prob hIL (fun w => F w (List.ofFn b))

end Paper2.AEth4

#print axioms Paper2.AEth4.prod_prob_snd
#print axioms Paper2.AEth4.uniform_split_take_prob
