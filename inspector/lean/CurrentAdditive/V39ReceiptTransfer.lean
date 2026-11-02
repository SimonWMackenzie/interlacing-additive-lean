import CurrentAdditive.V39GraphStreamTransfer

/-! Non-strict current-source receipt selection and the full-product
supplier for its original flattened selector independence. -/

namespace CurrentAdditive.V39ReceiptTransfer

open Paper2

variable {M B S A : Type*} [Fintype M] [Fintype B] [Fintype S] [Fintype A]

/-- The actual retained event is selected first. Equality at theta is
allowed; only then are the two complete streams fixed. -/
theorem choose_complete_streams_from_actual_event_ge
    (ρ : PositiveRationalLaw M) (σ : PositiveRationalLaw B)
    (τ : PositiveRationalLaw S) (actual : FiniteLaw A)
    (draw : M × (B × S) → A)
    (hdraw : (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).PushesTo
      actual draw)
    (Ystar : Set A) (θ : ℝ)
    (hselected : θ ≤ actual.prob (· ∈ Ystar)) :
    ∃ m b,
      θ ≤ τ.toFiniteLaw.prob (fun t => draw (m,(b,t)) ∈ Ystar) ∧
      (∀ E : S → Prop,
        (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).prob
            (fun x => x.1 = m ∧ x.2.1 = b ∧ E x.2.2) /
          (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).prob
            (fun x => x.1 = m ∧ x.2.1 = b) = τ.toFiniteLaw.prob E) := by
  have hpull : θ ≤
      (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).prob
        (fun x => draw x ∈ Ystar) := by
    rw [hdraw (· ∈ Ystar)]
    exact hselected
  obtain ⟨m,b,hsection⟩ := V39StreamAveraging.exists_two_complete_sections_ge
    ρ σ τ.toFiniteLaw (fun x => draw x ∈ Ystar) θ hpull
  refine ⟨m,b,hsection,?_⟩
  intro E
  simpa only [PositiveRationalLaw.toFiniteLaw_prod] using
    V39CompleteStreams.fixed_complete_streams ρ σ τ m b E

theorem chosen_streams_flattened_ambient_ge
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (ρ : PositiveRationalLaw M) (σ : PositiveRationalLaw B)
    (τ : PositiveRationalLaw S) (actual : FiniteLaw A)
    (draw : M × (B × S) → A)
    (hdraw : (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).PushesTo actual draw)
    (selector : S → I → J) (marginal : FiniteLaw J)
    (hwise : IsDWise 8192 τ.toFiniteLaw selector marginal)
    (Ystar : Set A) (θ : ℝ)
    (hselected : θ ≤ actual.prob (· ∈ Ystar)) :
    ∃ m b,
      θ ≤ τ.toFiniteLaw.prob (fun t => draw (m,(b,t)) ∈ Ystar) ∧
      (∀ (C : Finset I), C.card ≤ 8192 → ∀ E : (C → J) → Prop,
        (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).prob
            (fun x => x.1 = m ∧ x.2.1 = b ∧
              E (fun c : C => selector x.2.2 c.val)) /
          (ρ.toFiniteLaw.prod (σ.toFiniteLaw.prod τ.toFiniteLaw)).prob
            (fun x => x.1 = m ∧ x.2.1 = b) =
          (FiniteLaw.pi (fun _ : C => marginal)).prob E) := by
  obtain ⟨m,b,hsection,hfixed⟩ :=
    choose_complete_streams_from_actual_event_ge ρ σ τ actual draw hdraw
      Ystar θ hselected
  refine ⟨m,b,hsection,?_⟩
  intro C hC E
  rw [hfixed (fun t => E (fun c : C => selector t c.val))]
  exact hwise C hC E

/-- Full products supply every requested independence order, with no
extra lower bound on the number of available coordinates. -/
theorem iid_dwise {Z : Type*} [Fintype Z]
    (μ : PositiveRationalLaw Z) (D n : ℕ) :
    IsDWise D (μ.iid n).toFiniteLaw (fun z i => z i) μ.toFiniteLaw := by
  classical
  intro C hC E
  rw [PositiveRationalLaw.toFiniteLaw_iid]
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin n => μ.toFiniteLaw)
    Subtype.val Subtype.val_injective E

/-- The full-product selector stream has the exact flattened marginals
required by the common receipt proof. This supplies, rather than assumes,
the full-product instance of the preceding generic theorem. -/
theorem full_selector_flattened_dwise {X : Type*} [Fintype X]
    {q₁ : ℕ} [NeZero q₁] (μ : PositiveRationalLaw X) (D w q₂ : ℕ) :
    IsDWise D ((SourceLaws.templateLaw μ q₁ q₂).iid w).toFiniteLaw
      (fun z (p : Fin w × Fin q₂) => z p.1 p.2)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw := by
  classical
  exact flatten_dwise D
    (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
    ((SourceLaws.templateLaw μ q₁ q₂).iid w).toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw
    (fun z i => z i) (fun z i => z i)
    (iid_dwise _ D q₂) (iid_dwise _ D w)

end CurrentAdditive.V39ReceiptTransfer

#print axioms CurrentAdditive.V39ReceiptTransfer.choose_complete_streams_from_actual_event_ge
#print axioms CurrentAdditive.V39ReceiptTransfer.chosen_streams_flattened_ambient_ge
#print axioms CurrentAdditive.V39ReceiptTransfer.iid_dwise
#print axioms CurrentAdditive.V39ReceiptTransfer.full_selector_flattened_dwise
