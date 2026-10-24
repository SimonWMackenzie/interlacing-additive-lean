import CurrentAdditive.GeneratedPairedConversation
import Paper2.PairedSelectorObstruction

/-! Appendix I `det:paired` for the actual indexed source pair. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- No protocol of source depth H+ell computes the actually retained
indexed paired matrix. The selector-pair law is the product of the two
complete inner-label laws; its decoded full word is not assumed iid. -/
theorem paired_short_protocol_impossible
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (K : Set (src.inner.Label × src.inner.Label))
    (O F : Set (Fin q₂ × src.gamma.Label)) (ε δ : ℝ)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (hO : 1-ε ≤ (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob (· ∈ F))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hsmall : 2*q₂*x ≤ 1/8)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ)
    (P : Protocol K (columns O F) Bool)
    (hP : P.Computes (fun z c => pairedIndexed src R₀ z.val
      (c.val.1.1, (c.val.1.2, c.val.2))))
    (hcost : P.cost ≤ H+ell) : False := by
  classical
  let t : ℝ := 2*q₂*x
  obtain ⟨_, ht, hexcess⟩ := pair_excess src.gamma.law O F t ε δ
    hO hF hδ (by simpa only [Fintype.card_fin] using hslack)
  obtain ⟨c, hc⟩ := Paper2.PairedSelectorInitial.columns_nonempty
    src.gamma.law O F δ hδpos hF
  let default : columns O F := ⟨c, hc⟩
  let init := Paper2.PairedSelectorInitial.initial
    src.gamma.law.toFiniteLaw O F t default P
  have hfloor : SourceSupportSchedule.floor q₂ x 0 < 1 := by
    have hs : t < 1 := by dsimp [t]; linarith only [hsmall]
    simpa only [SourceSupportSchedule.floor_zero, t] using hs
  apply paired_remaining_conversation_contradiction src R₀ H ell hH hq x hx
    hD hfloor hprofile K hK init
    ?_ ?_ ?_ (bad src.gamma.law.toFiniteLaw O t).card ?_ ?_ ?_ ?_
  · exact Paper2.PairedSelectorInitial.computesOn
      src.gamma.law.toFiniteLaw O F t default P
      (fun z c => pairedIndexed src R₀ z.val
        (c.1.1, (c.1.2, c.2))) hP
  · simpa only [init, Paper2.PairedSelectorInitial.cost] using hcost
  · exact Paper2.PairedSelectorInitial.valid
      src.gamma.law.toFiniteLaw O F t default P
  · exact Paper2.PairedSelectorInitial.count
      src.gamma.law.toFiniteLaw O F t default P
  · exact hexcess
  · simpa only [SourceSupportSchedule.floor_zero] using
      Paper2.PairedSelectorInitial.floors
        src.gamma.law.toFiniteLaw O F t default P
  · exact Paper2.PairedSelectorInitial.reaches
      src.gamma.law.toFiniteLaw O F t default P

/-- The generated paired-selector lower bound on the literal original
pair-label and tagged-column restriction. -/
theorem paired_restriction_lower
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (K : Set (src.inner.Label × src.inner.Label))
    (O F : Set (Fin q₂ × src.gamma.Label)) (ε δ : ℝ)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (hO : 1-ε ≤ (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob (· ∈ F))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hsmall : 2*q₂*x ≤ 1/8)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ) :
    H+ell+1 ≤ Compression.restrictionD
      (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
      K (columns O F) := by
  classical
  by_contra hn
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (z : K) (c : columns O F) =>
        pairedIndexed src R₀ z.val (c.val.1.1, (c.val.1.2, c.val.2))))
  apply paired_short_protocol_impossible src R₀ H ell hH hq x hx hD
    hprofile K O F ε δ hK hO hF hδpos hδ hsmall hslack P hP
  change P.cost = Compression.restrictionD
    (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
    K (columns O F) at hcost
  omega

#print axioms paired_short_protocol_impossible
#print axioms paired_restriction_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
