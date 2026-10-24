import EthInapproximability.CurrentPaper.ExactConstruction
import NPCC.Relaxed

/-!
# Sampler coordinates survive a small number of deleted labels

Trace: v8 `G-exact-control.tex`. The family remains indexed: distinct
labels carrying the same tuple are counted separately. The singleton
instance of balancedness supplies the fibre lower bound; deletion of fewer
labels than that lower bound leaves every coordinate value represented.
-/

namespace EthInapproximability.CurrentPaper.ExactSamplerSurvival

open NPCC

/-- The singleton-pattern instance of balancedness, as an unnormalised
lower bound on the number of indexed labels in a coordinate fibre. -/
theorem coordinate_fibre_lower {N q m t : ℕ} {ε : ℝ}
    (C : Fin N → Fin q → Fin m) (hbal : IsBalancedFamily t C ε)
    (ht : 1 ≤ t) (α : Fin q) (i : Fin m) :
    (1 - ε) * (N : ℝ) / (m : ℝ) ≤
      ((Finset.univ.filter (fun z : Fin N => C z α = i)).card : ℝ) := by
  classical
  have h := hbal.2 {α} (by simpa using ht) (fun _ => i)
  simp only [Finset.mem_singleton, forall_eq, Finset.card_singleton,
    Fintype.card_fin, pow_one] at h
  have hN : (0 : ℝ) < N := by exact_mod_cast hbal.1
  have hl : (1 - ε) / (m : ℝ) ≤
      ((Finset.univ.filter (fun z : Fin N => C z α = i)).card : ℝ) / (N : ℝ) := by
    rw [sub_div]
    linarith [(abs_le.mp h).1]
  have hh := (le_div_iff₀ hN).mp hl
  convert hh using 1
  ring

/-- Deleting at most `loss` family labels cannot remove any coordinate
value when `loss` is strictly below the balanced singleton-fibre bound. -/
theorem coordinate_survives {N q m t loss : ℕ} {ε : ℝ}
    (C : Fin N → Fin q → Fin m) (hbal : IsBalancedFamily t C ε)
    (ht : 1 ≤ t) (S : Finset (Fin N)) (hS : N - loss ≤ S.card)
    (hloss : (loss : ℝ) < (1 - ε) * (N : ℝ) / (m : ℝ)) :
    ∀ α i, ∃ z ∈ S, C z α = i := by
  classical
  intro α i
  by_contra hn
  push Not at hn
  let F := Finset.univ.filter (fun z : Fin N => C z α = i)
  have hsub : F ⊆ Finset.univ \ S := by
    intro z hz
    have he : C z α = i := (Finset.mem_filter.mp hz).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hzS => hn z hzS he⟩
  have hc := Finset.card_le_card hsub
  have hc' : F.card ≤ N - S.card := by
    simpa only [Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin] using hc
  have hScard : S.card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using S.card_le_univ
  have hF : F.card ≤ loss := by omega
  have hFreal : (F.card : ℝ) ≤ (loss : ℝ) := by exact_mod_cast hF
  have hlo := coordinate_fibre_lower C hbal ht α i
  change (1 - ε) * (N : ℝ) / (m : ℝ) ≤ (F.card : ℝ) at hlo
  linarith

/-- The three other bins in the exact reduction can delete at most
`3 * τB` labels. The literal second family therefore still supplies every
duplicated row label at each coordinate. -/
theorem second_family_survives {a d N₂ t τB : ℕ} {ε : ℝ}
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (hbal : IsBalancedFamily t C₂ ε) (ht : 1 ≤ t)
    (S : Finset (Fin N₂)) (hS : N₂ - 3 * τB ≤ S.card)
    (hloss : ((3 * τB : ℕ) : ℝ) <
      (1 - ε) * (N₂ : ℝ) / (ExactConstruction.width a : ℝ)) :
    ∀ α i, ∃ z ∈ S, C₂ z α = i :=
  coordinate_survives C₂ hbal ht S hS hloss

end EthInapproximability.CurrentPaper.ExactSamplerSurvival
