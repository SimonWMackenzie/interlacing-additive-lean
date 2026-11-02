import Paper2.PairedSelectorInitial
import Paper2.PairedSelectorConversation

/-!
# The retained paired-selector obstruction

Frozen v12 Section 5, `res:paired`. The final theorem starts with the
ordinary and foreign retained sets and their original masses. It constructs
the starting state, proves its population excess, and rules out a short
protocol through the actual paired-support conversation. No population,
frontier or communication-lower-bound certificate is a final premise.
-/

namespace Paper2.PairedSelectorObstruction

open PairedSelectorMatrix PairedSelectorPopulation
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {W J : Type*} [Fintype W] [Fintype J] {q : ℕ} [NeZero q]

theorem short_protocol_impossible
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q = 2 ^ ell) (x : ℝ) (hx : 0 < x)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (A : Set (Selector q J)) (O F : Set (Fin q × W)) (ε δ : ℝ)
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (hO : 1 - ε ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ)
    (P : Protocol A (columns O F) Bool)
    (hP : P.Computes (fun a c => matrix R a.val c.val))
    (hcost : P.cost ≤ H + ell) : False := by
  classical
  let t : ℝ := 2 * q * x
  obtain ⟨_, ht, hexcess⟩ := pair_excess μ O F t ε δ hO hF hδ
    (by simpa only [Fintype.card_fin] using hslack)
  obtain ⟨c, hc⟩ := PairedSelectorInitial.columns_nonempty μ O F δ hδpos hF
  let default : columns O F := ⟨c, hc⟩
  let s := PairedSelectorInitial.initial μ.toFiniteLaw O F t default P
  have hsmall : SourceSupportSchedule.floor q x 0 < 1 := by
    simpa only [SourceSupportSchedule.floor_zero] using ht
  apply PairedSelectorConversation.remaining_conversation_contradiction
    μ ν R H ell hH hq x hx hsmall hprofile A hA s
    ?_ ?_ ?_ (bad μ.toFiniteLaw O t).card ?_ ?_ ?_ ?_
  · exact PairedSelectorInitial.computesOn μ.toFiniteLaw O F t default P
      (fun a c => matrix R a.val c) hP
  · simpa only [s, PairedSelectorInitial.cost] using hcost
  · exact PairedSelectorInitial.valid μ.toFiniteLaw O F t default P
  · exact PairedSelectorInitial.count μ.toFiniteLaw O F t default P
  · exact hexcess
  · simpa only [SourceSupportSchedule.floor_zero] using
      PairedSelectorInitial.floors μ.toFiniteLaw O F t default P
  · exact PairedSelectorInitial.reaches μ.toFiniteLaw O F t default P

/-- The exact lower bound on the original retained matrix, including
zero ordinary deletions and arbitrarily correlated retained selector pairs. -/
theorem restriction_lower
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q = 2 ^ ell) (x : ℝ) (hx : 0 < x)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (A : Set (Selector q J)) (O F : Set (Fin q × W)) (ε δ : ℝ)
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (hO : 1 - ε ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ) :
    H + ell + 1 ≤ Compression.restrictionD (matrix R) A (columns O F) := by
  classical
  by_contra hn
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (a : A) (c : columns O F) => matrix R a.val c.val))
  apply short_protocol_impossible μ ν R H ell hH hq x hx hprofile A O F ε δ
    hA hO hF hδpos hδ hslack P hP
  change P.cost = Compression.restrictionD (matrix R) A (columns O F) at hcost
  omega

end Paper2.PairedSelectorObstruction

#print axioms Paper2.PairedSelectorObstruction.short_protocol_impossible
#print axioms Paper2.PairedSelectorObstruction.restriction_lower
