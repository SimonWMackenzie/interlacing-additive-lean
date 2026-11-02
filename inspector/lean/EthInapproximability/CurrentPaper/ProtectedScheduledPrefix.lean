import EthInapproximability.CurrentPaper.ProtectedDominantFamilies
import EthInapproximability.CurrentPaper.ProtectedDeletionGates
import EthInapproximability.CurrentPaper.AmplificationInnerProfiles

/-!
# Actual prefix families at the scheduled protected construction

Source: locked v8 `A-stage4-details.tex`, `lem:paper-protected-preparation`.
The original retained sets and the original unpruned protocol produce all
dominant indexed families simultaneously. Every numerical separation and
deletion gate is discharged from the public source parameters.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedScheduledPrefix

open scoped Classical
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity
open Construction JointTransfer ProtectedProfiles ProtectedPreparation
open ProtectedDominantFamilies Parameters AmplificationInnerProfiles ActualPrefix

universe u

/-- Membership and quotient identity recover the literal per-bin copy
label. The default value of the total quotient is never used. -/
theorem template_representation {X : Type u} [Fintype X]
    {s L nv nb : ℕ} (hs : 0 < s) (hL : 0 < L)
    (r : ProtectedRows s L nv nb X) (hr : r ∈ templateRows s L nv nb)
    (p : Fin s) (l : Fin L)
    (hval : templatePair s L nv nb hs hL r = (p, l)) :
    ∃ copy : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb p (l, copy) = r := by
  obtain ⟨⟨z, copy⟩, _, rfl⟩ := Finset.mem_image.mp hr
  rw [templatePair_embedding] at hval
  subst z
  exact ⟨copy, rfl⟩

/-- The literal scheduled protocol has the actual Alice prefix and one
large, physically represented indexed family in every prefix branch.
The density is the stronger `998/1000`, not merely the display's `49/50`. -/
theorem scheduled_prefix_families (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost)
    (Δ : ℕ) (γ δ : ℚ) (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ)
    (nv nb : ℕ) (hv : 0 < nv) (hb : 0 < nb)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)
    (A : Finset (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) (Fin i.columns)))
    (B : Finset (ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb (Fin i.rows)))
    (hA : (1 - (rowTolerance i : ℝ)) *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) (Fin i.columns)) ≤ A.card)
    (hB : (1 - (columnTolerance i : ℝ)) * Fintype.card (ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb (Fin i.rows)) ≤ B.card)
    (P : Protocol
      (ProtectedRows (bins i) (PrimeSampler.size (secondWidth i) (balanceOrder i)
        (firstWidth i * i.rows)) nv nb (Fin i.rows))
      (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) (Fin i.columns)) Bool)
    (hPcost : P.cost ≤ i.cost + firstExponent i + secondExponent i + binExponent i)
    (hcomp : ∀ r ∈ B, ∀ c ∈ A, P.eval r c =
      protectedMatrix f (firstExponent i) (bins i) (secondWidth i)
        (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
        nv nb (bins_pos i) (scheduledFamily i ha) order vectors cap c r) :
    AllAlice (binExponent i) P ∧
      ∃ p : Fin (bins i) → Fin (bins i), Function.Injective p ∧
        ∃ K : Fin (bins i) → Finset (Fin (PrimeSampler.size (secondWidth i)
            (balanceOrder i) (firstWidth i * i.rows))),
          (∀ j, (998 / 1000 : ℝ) * PrimeSampler.size (secondWidth i)
            (balanceOrder i) (firstWidth i * i.rows) ≤ (K j).card) ∧
          (∀ j, (Protocol.rowSubtreeAtRaw (binExponent i) P j).cost + binExponent i ≤ P.cost) ∧
          (∀ j, ∀ l ∈ K j, ∃ copy : TemplateLabels (bins i)
              (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb (Fin i.rows),
            templateEmbedding (bins i)
              (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
              (p j) (l, copy) ∈ B ∧
            Protocol.prefixCodeRaw (binExponent i) P
              (templateEmbedding (bins i)
                (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
                (p j) (l, copy)) = j) := by
  letI : NeZero i.rows := ⟨by have := ha.1; omega⟩
  letI : NeZero i.columns := ⟨by have := ha.2.1; omega⟩
  let L := PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)
  have hs : 0 < bins i := bins_pos i
  have hL : 0 < L := PrimeSampler.size_pos _ _ _
  have hdel := ProtectedDeletionGates.prefix_deletion_gates_parameters i Δ γ δ
    hΔ hγ hγone hsource hvertex (firstExponent i) (secondWidth i) L nv nb A B hA hB
  have hgap := threshold_separation_parameters i hc ha (le_refl (999 / 1000 : ℝ))
  have hgap' : bins i *
      ⌈(Fintype.card (Fin L) : ℝ) * (2 : ℝ) ^ (1 - (tailDepth i : ℝ))⌉₊ <
      ⌈(Fintype.card (Fin L) : ℝ) * (999 / 1000)⌉₊ := by
    simpa only [Fintype.card_fin] using hgap
  have hprofiles := scheduled_second_profiles i hc ha f hf hcost
  have hP' : P.cost ≤ D (scheduledSecond i ha f) + binExponent i := by
    rw [hprofiles.1]
    exact hPcost
  have hk : 1 ≤ binExponent i := by
    have hh := (ParameterGates.hard_seed_exponent_domains i).2.2.2
    omega
  obtain ⟨hpref, hbudget, _, phi, hphi, hnw⟩ := protected_prefix f
    (firstExponent i) (binExponent i) (secondWidth i) L nv nb hs (secondWidth_pos i)
    hL hv hb (scheduledFamily i ha) order vectors cap hprofiles.2.2 hk
    (by norm_num : (999 / 1000 : ℝ) ≤ 1) (by norm_num : (18 / 25 : ℝ) ≤ 99 / 100)
    hgap' A B hdel.1 hdel.2 P hP' hcomp
  let E := (B ∩ templateRows (bins i) L nv nb).image
    (templatePair (bins i) L nv nb hs hL)
  let lab := fun r => Protocol.prefixCodeRaw (binExponent i) P (phi r)
  let p := dominantBin E lab hnw
  let K := fun j => branchFamily E lab (p j) j
  have hbr := dense_template_bracket (firstExponent i) (bins i) (secondWidth i) L nv nb
    hs (secondWidth_pos i) hL hv hb A B hdel.1 hdel.2
  have hrows : ∀ p : Fin (bins i), ⌈(Fintype.card (Fin L) : ℝ) * (999 / 1000)⌉₊ ≤
      (E.filter (fun r => r.1 = p)).card := by
    intro p
    exact hbr.1 p (Finset.mem_univ _)
  refine ⟨hpref, p, dominantBin_injective E lab hnw hrows hgap', K, ?_, hbudget, ?_⟩
  · intro j
    have hcount := dominantFamily_card E lab hnw j
    apply dominant_count_density hs (ParameterGates.actualFamily_size_ge_9216_bins i hc ha)
      (ParameterGates.dense_tail_loss i).2 (le_refl (999 / 1000 : ℝ))
    simpa only [Fintype.card_fin, L, K, p] using hcount
  · intro j l hl
    obtain ⟨hE, hcode⟩ := (mem_branchFamily E lab (p j) j l).mp hl
    obtain ⟨hmem, hval⟩ := hphi (p j, l) hE
    obtain ⟨copy, heq⟩ := template_representation hs hL (phi (p j, l))
      (Finset.mem_inter.mp hmem).2 (p j) l hval
    refine ⟨copy, ?_, ?_⟩
    · rw [heq]
      exact (Finset.mem_inter.mp hmem).1
    · rw [heq]
      exact hcode

end EthInapproximability.CurrentPaper.ProtectedScheduledPrefix
