import CurrentAdditive.RestrictionBridge

/-! Private conversion from the prefix walk's blockwise row sets to the
actual indexed rectangle consumed by the deterministic suffix lemmas. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X S : Type*} [Fintype X] [Fintype S] {q : ℕ}

theorem rowRectangle_fiber (Q : Finset (Fin q))
    (R : Fin q → Set X) (i : Fin q) (hi : i ∈ Q)
    (μ : FiniteLaw X) :
    μ.prob (fun x => (i,x) ∈ rowRectangle Q R) =
      μ.prob (· ∈ R i) := by
  congr 1
  funext x
  simp [rowRectangle, hi]

theorem rowRectangle_mem (Q : Finset (Fin q))
    (R : Fin q → Set X) (i : Fin q) (x : X) :
    (i,x) ∈ rowRectangle Q R ↔ i ∈ Q ∧ x ∈ R i := by
  rfl

/-- The selected residual is a protocol for the exact indexed `K` and the
combined selected row set, at the recorded suffix cost. -/
theorem selected_suffix_upper
    (F : (Fin q × X) → S → Bool)
    (Q : Finset (Fin q)) (R : Fin q → Set X) (K : Set S)
    (P : Workspace.Types.Protocol.Protocol (Fin q × X) S Bool)
    (d : ℕ) (hcost : P.cost ≤ d)
    (heval : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F (i,x) s) :
    Paper2.Compression.restrictionD F (rowRectangle Q R) K ≤ d :=
  residual_restriction_upper F Q R K P d hcost heval

#print axioms CurrentAdditive.ArbitraryPrefix.rowRectangle_fiber
#print axioms CurrentAdditive.ArbitraryPrefix.selected_suffix_upper

end CurrentAdditive.ArbitraryPrefix
