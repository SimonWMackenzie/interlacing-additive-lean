import CurrentAdditive.SmallBiasPair

/-!
# The common early strategy retains all rows

Source: v27 `sections/07a-small-bias.tex`, proof of
`yao:small-bias-escape`, paragraph "Choose a common prefix".
This is a real path through the protocol: Alice's choices are common to the
fixed row set because her entire early response strategy is common, and each
Bob branch is selected by original-law mass.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- After `k+1` common early Alice turns, retain every row in `X` and at
least a `2^-k` fraction of original column mass. The resulting `Q` is an
actual Bob-starting suffix of depth `2a`. -/
theorem common_prefix_retains
    (μ : Paper2.FiniteLaw Λ) (k a : ℕ)
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P (2 * k + 1 + 2 * a)) (ha : Alternates .alice P)
    (X : Finset Ω) (Y : Λ → Prop)
    (σ : ResponseStrategy (k + 1))
    (hσ : ∀ x ∈ X, earlyStrategy (k + 1) P x = σ) :
    ∃ (Y' : Λ → Prop) (Q : Protocol Ω Λ Bool),
      (∀ ℓ, Y' ℓ → Y ℓ) ∧
      μ.prob Y ≤ (2 ^ k : ℝ) * μ.prob Y' ∧
      IsComplete Q (2 * a) ∧ Alternates .bob Q ∧
      (∀ x ∈ X, ∀ ℓ, Y' ℓ → P.eval x ℓ = Q.eval x ℓ) := by
  classical
  induction k generalizing P Y with
  | zero =>
      have hc' : IsComplete P (2 * a + 1) := by simpa [Nat.add_comm] using hc
      obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P (2 * a) hc' ha
      have hf : ∀ x ∈ X, f x = σ.1 := by
        intro x hx
        exact congrArg Prod.fst (hσ x hx)
      let Q : Protocol Ω Λ Bool := if σ.1 then r else l
      have hQ : IsComplete Q (2 * a) ∧ Alternates .bob Q := by
        cases hb : σ.1 <;> simp [Q, hb, hc'.1, hc'.2, ha.1, ha.2]
      refine ⟨Y, Q, (fun _ h => h), ?_, hQ.1, hQ.2, ?_⟩
      · simp
      · intro x hx ℓ _
        cases hb : σ.1 <;> simp [Q, hf x hx, hb, Protocol.eval]
  | succ k ih =>
      have hc' : IsComplete P ((2 * k + 2 + 2 * a) + 1) := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P _ hc' ha
      have hf : ∀ x ∈ X, f x = σ.1 := by
        intro x hx
        exact congrArg Prod.fst (hσ x hx)
      let T : Protocol Ω Λ Bool := if σ.1 then r else l
      have hT : IsComplete T (2 * k + 2 + 2 * a) ∧ Alternates .bob T := by
        cases hb : σ.1 <;> simp [T, hb, hc'.1, hc'.2, ha.1, ha.2]
      -- The selected Alice child is a genuine Bob node.
      obtain ⟨g, u, v, hshape⟩ : ∃ g u v, T = Protocol.bNode g u v := by
        cases hTshape : T with
        | leaf q =>
            have hh := hT.1
            rw [hTshape] at hh
            have hd : 2 * k + 2 + 2 * a = (2 * k + 1 + 2 * a) + 1 := by omega
            rw [hd] at hh
            exact False.elim hh
        | aNode g u v =>
            have hh := hT.2
            rw [hTshape] at hh
            exact False.elim hh
        | bNode g u v => exact ⟨g, u, v, rfl⟩
      obtain ⟨b, hbmass⟩ := exists_bob_half μ Y g
      let R : Protocol Ω Λ Bool := if b then v else u
      have hR : IsComplete R (2 * k + 1 + 2 * a) ∧ Alternates .alice R := by
        have hcu : IsComplete u (2 * k + 1 + 2 * a) ∧
            IsComplete v (2 * k + 1 + 2 * a) := by
          have hh := hT.1
          rw [hshape] at hh
          have hd : 2 * k + 2 + 2 * a = (2 * k + 1 + 2 * a) + 1 := by omega
          rw [hd] at hh
          exact hh
        have hau : Alternates .alice u ∧ Alternates .alice v := by
          have hh := hT.2
          rw [hshape] at hh
          exact hh
        cases b <;> simp [R, hcu.1, hcu.2, hau.1, hau.2]
      let Y₁ : Λ → Prop := fun ℓ => Y ℓ ∧ g ℓ = b
      let τ : ResponseStrategy (k + 1) := if b then σ.2.2 else σ.2.1
      have hround : ∀ x ∈ X, ∀ c : Bool,
          afterRound (Protocol.aNode f l r) x c = if c then v else u := by
        intro x hx c
        change afterBob (if f x then r else l) c = if c then v else u
        rw [hf x hx]
        change afterBob T c = if c then v else u
        rw [hshape]
        cases c <;> rfl
      have hτ : ∀ x ∈ X, earlyStrategy (k + 1) R x = τ := by
        intro x hx
        cases hb : b with
        | false =>
            have hh := congrArg
              (fun z : ResponseStrategy (k + 2) => z.2.1) (hσ x hx)
            change earlyStrategy (k + 1)
              (afterRound (Protocol.aNode f l r) x false) x = σ.2.1 at hh
            rw [hround x hx false] at hh
            simpa [R, τ, hb] using hh
        | true =>
            have hh := congrArg
              (fun z : ResponseStrategy (k + 2) => z.2.2) (hσ x hx)
            change earlyStrategy (k + 1)
              (afterRound (Protocol.aNode f l r) x true) x = σ.2.2 at hh
            rw [hround x hx true] at hh
            simpa [R, τ, hb] using hh
      obtain ⟨Y₂, Q, hY₂, hmass₂, hc₂, ha₂, heval₂⟩ :=
        ih R hR.1 hR.2 Y₁ τ hτ
      refine ⟨Y₂, Q, (fun ℓ h => (hY₂ ℓ h).1), ?_, hc₂, ha₂, ?_⟩
      · calc
          μ.prob Y ≤ 2 * μ.prob Y₁ := hbmass
          _ ≤ 2 * ((2 ^ k : ℝ) * μ.prob Y₂) :=
            mul_le_mul_of_nonneg_left hmass₂ (by norm_num)
          _ = (2 ^ (k + 1) : ℝ) * μ.prob Y₂ := by ring
      · intro x hx ℓ hℓ
        have hfirst : (Protocol.aNode f l r).eval x ℓ = R.eval x ℓ := by
          have hgb : g ℓ = b := (hY₂ ℓ hℓ).2
          have hA : (Protocol.aNode f l r).eval x ℓ = T.eval x ℓ := by
            cases hs : σ.1 <;> simp [T, Protocol.eval, hf x hx, hs]
          have hB : T.eval x ℓ = R.eval x ℓ := by
            rw [hshape]
            cases hb : b <;> simp [Protocol.eval, R, hgb, hb]
          exact hA.trans hB
        exact hfirst.trans (heval₂ x hx ℓ hℓ)

#print axioms CurrentAdditive.SmallBias.common_prefix_retains

end CurrentAdditive.SmallBias
