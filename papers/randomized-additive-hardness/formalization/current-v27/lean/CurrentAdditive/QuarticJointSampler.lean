import CurrentAdditive.QuarticUniformExact

/-!
# Splitting one fair bit tape into the actual v27 selector and estimator tapes

This is the probability identity used by the physical source decider. It
works for any extra padding between the selector prefix and estimator block,
and any unused suffix of the total tape.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem experiment_joint_split27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let exp := experiment27 hn edge Δ γ k
    letI : Fintype exp.output.Tape := exp.tapeFintype
    ∃ (r : ℕ) (dec : List Bool → exp.output.Tape),
      (∀ a : exp.output.Tape, (exp.output.tapeBits a).length = r) ∧
      (∀ a : exp.output.Tape, dec (exp.output.tapeBits a) = a) ∧
      ∀ {L s R : ℕ}, r ≤ L → L + s ≤ R →
        ∀ P : exp.output.Tape × (Fin s → Bool) → Prop,
          (uniformTape R).prob (fun t =>
            P (dec ((List.ofFn t).take r),
              Paper2.AEth5.vecOf (((List.ofFn t).drop L).take s) s)) =
          (exp.tapeLaw.prod (uniformTape s)).prob P := by
  intro exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  obtain ⟨r, hlen, hinj, hsurj, _⟩ := experiment_uniformExact27 hn edge Δ γ k
  obtain ⟨r₂, hlen₂, hF⟩ := experiment_prob_uniform27 hn edge Δ γ k
  obtain ⟨a₀⟩ := Paper2.FiniteLaw.nonempty exp.tapeLaw
  have hr₂ : r₂ = r := (hlen₂ a₀).symm.trans (hlen a₀)
  subst r₂
  let dec : List Bool → exp.output.Tape := fun w =>
    if h : ∃ a, exp.output.tapeBits a = w then Classical.choose h else a₀
  have hdec_spec : ∀ w, w.length = r → exp.output.tapeBits (dec w) = w := by
    intro w hw
    have h := hsurj w hw
    dsimp only [dec]
    split_ifs with hex
    · exact Classical.choose_spec hex
    · exact False.elim (hex h)
  have hdec : ∀ a : exp.output.Tape, dec (exp.output.tapeBits a) = a :=
    fun a => hinj (hdec_spec _ (hlen a))
  refine ⟨r, dec, hlen, hdec, ?_⟩
  intro L s R hrL hLR P
  exact Paper2.AEth5.split_law exp.tapeLaw exp.output.tapeBits r hF dec hdec hrL hLR P

#print axioms experiment_joint_split27

end Paper2.CurrentAdditive.QuarticClassEndpoint
