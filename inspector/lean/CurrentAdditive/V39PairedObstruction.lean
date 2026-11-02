import CurrentAdditive.V39PairedConversation
import CurrentAdditive.V39TaggedFibrePopulation
import Paper2.PairedSelectorInitial

/-! Current res:paired for the actual generated complete selector labels.
The source's strict delta>2*q*x+epsilon is used literally; zero ordinary
deletion is permitted. No Fin 3 profile or additive 2/q slack occurs. -/

namespace CurrentAdditive.V39PairedObstruction

open Paper2 Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem paired_short_protocol_impossible
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
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
    (hε : 0 ≤ ε) (hslack : 2*q₂*x + ε < δ)
    (P : Protocol K (columns O F) Bool)
    (hP : P.Computes (fun z c => pairedIndexed src R₀ z.val
      (c.val.1.1, (c.val.1.2, c.val.2))))
    (hcost : P.cost ≤ H+ell) : False := by
  classical
  let t : ℝ := 2*q₂*x
  have hcount : q₂ < (V39TaggedFibrePopulation.taggedGood
      src.gamma.law.toFiniteLaw O F t).card := by
    simpa only [Fintype.card_fin] using
      V39TaggedFibrePopulation.tagged_good_count_gt src.gamma.law O F t ε δ
        hO hF hε hδ hslack
  obtain ⟨c,hc⟩ := Paper2.PairedSelectorInitial.columns_nonempty
    src.gamma.law O F δ hδpos hF
  let default : columns O F := ⟨c,hc⟩
  let init : Paper2.SourceSupportFrontier.State K
      (Column q₂ src.gamma.Label) (Bool × Fin q₂) src.gamma.Label := {
    protocol := SourceSupportInitial.extendColumns (columns O F) default P
    columns := columns O F
    coordinates := V39TaggedFibrePopulation.taggedGood src.gamma.law.toFiniteLaw O F t
    attachments := ∅
    support := PairedSelectorPopulation.support O F }
  apply V39PairedConversation.paired_remaining_conversation_contradiction src R₀
    H ell hH hq x hx hD (by simpa [SourceSupportSchedule.floor_zero] using hsmall)
    hprofile K hK init
  · exact SourceSupportInitial.extendColumns_computesOn (columns O F) default P
      (fun (z : K) (c : Column q₂ src.gamma.Label) =>
        pairedIndexed src R₀ z.val (c.1.1,(c.1.2,c.2))) hP
  · simpa only [init,SourceSupportInitial.extendColumns_cost] using hcost
  · rfl
  · exact hcount
  · simpa only [init,SourceSupportSchedule.floor_zero] using
      V39TaggedFibrePopulation.tagged_good_floor src.gamma.law.toFiniteLaw O F t
  · intro a _ γ hγ
    exact PairedSelectorPopulation.initial_reaches O F a γ hγ

/-- The generated paired-selector lower bound on the literal original
pair-label and tagged-column restriction. -/
theorem paired_restriction_lower
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
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
    (hε : 0 ≤ ε) (hslack : 2*q₂*x + ε < δ) :
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
    hprofile K O F ε δ hK hO hF hδpos hδ hsmall hε hslack P hP
  change P.cost = Compression.restrictionD
    (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
    K (columns O F) at hcost
  omega

end CurrentAdditive.V39PairedObstruction

#print axioms CurrentAdditive.V39PairedObstruction.paired_short_protocol_impossible
#print axioms CurrentAdditive.V39PairedObstruction.paired_restriction_lower
