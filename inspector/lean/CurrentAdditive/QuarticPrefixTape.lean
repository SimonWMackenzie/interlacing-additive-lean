import CurrentAdditive.QuarticJointSampler

/-!
# Exact typed v27 selector tape from a raw fair-bit prefix

This bridges the machine's raw tape to the literal selected tape in both
the scheduled and fallback branches. It leaves the physical prefix-cut
routine as a separate obligation.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor

theorem exists_tape_of_prefix27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (word : List Bool)
    (hlen : (select27 hn edge Δ γ k).inputBits ≤ word.length) :
    ∃ t : (select27 hn edge Δ γ k).Tape,
      (select27 hn edge Δ γ k).tapeBits t =
        word.take (select27 hn edge Δ γ k).inputBits := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select27_good hn edge Δ γ k hc] at hlen ⊢
    refine ⟨⟨word.take _, ?_⟩, rfl⟩
    rw [List.length_take]
    exact Nat.min_eq_left hlen
  · rw [select27_bad hn edge Δ γ k hc] at hlen ⊢
    exact ⟨(), rfl⟩

#print axioms exists_tape_of_prefix27

end Paper2.CurrentAdditive.QuarticClassEndpoint
