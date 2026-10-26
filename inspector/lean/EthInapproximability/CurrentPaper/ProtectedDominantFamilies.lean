import EthInapproximability.CurrentPaper.ProtectedPreparation
import EthInapproximability.CurrentPaper.ParameterGates

/-!
# Retained template families in the actual prefix branches

Source: frozen v8 `A-stage4-details.tex`, `lem:paper-protected-preparation`,
the paragraph deriving distinct dominant bins and retained restrictions.

Every family below is an explicit filter of the retained labelled template
set. Its representatives keep their original prefix code, and suffix costs
are charged to the original protocol. No communication lower-bound conclusion
is assumed as a field of the construction.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedDominantFamilies

open scoped BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction JointTransfer ProtectedProfiles ActualPrefix

/-- The retained second-family indices in one bin and one actual branch. -/
def branchFamily {s L : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s) (p j : Fin s) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun z => (p, z) ∈ E ∧ lab (p, z) = j

theorem mem_branchFamily {s L : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s) (p j : Fin s) (z : Fin L) :
    z ∈ branchFamily E lab p j ↔ (p, z) ∈ E ∧ lab (p, z) = j := by
  classical
  simp [branchFamily]

theorem branchFamily_card {s L : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s) (p j : Fin s) :
    (branchFamily E lab p j).card =
      (E.filter fun r => lab r = j ∧ r.1 = p).card := by
  classical
  symm
  apply Finset.card_bij (fun r _ => r.2)
  · intro r hr
    obtain ⟨hrE, hrj, hrp⟩ := Finset.mem_filter.mp hr
    rw [mem_branchFamily]
    simpa only [← hrp] using And.intro hrE hrj
  · intro r hr t ht hrt
    exact Prod.ext ((Finset.mem_filter.mp hr).2.2.trans
      (Finset.mem_filter.mp ht).2.2.symm) hrt
  · intro z hz
    obtain ⟨hzE, hzj⟩ := (mem_branchFamily E lab p j z).mp hz
    exact ⟨(p, z), Finset.mem_filter.mpr ⟨hzE, hzj, rfl⟩, rfl⟩

/-- The unique dominant bin already supplied by the actual no-waste proof. -/
def dominantBin {s L T0 T : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s)
    (hnw : NoWasteConclusion Finset.univ E lab T0 T) : Fin s → Fin s :=
  Protocol.dominantIndex Finset.univ E lab hnw

theorem dominantFamily_card {s L T0 T : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s)
    (hnw : NoWasteConclusion Finset.univ E lab T0 T) (j : Fin s) :
    T0 - (s - 1) * T ≤ (branchFamily E lab (dominantBin E lab hnw j) j).card := by
  rw [branchFamily_card]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Protocol.dominantIndex_spec Finset.univ E lab hnw j).2.1

/-- An absent bin would distribute its entire retained block among small
nondominant fibres. This uses the actual retained set, not full bin carriers. -/
theorem dominantBin_surjective {s L T0 T : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s)
    (hnw : NoWasteConclusion Finset.univ E lab T0 T)
    (hrows : ∀ p, T0 ≤ (E.filter fun r => r.1 = p).card)
    (hgap : s * T < T0) : Function.Surjective (dominantBin E lab hnw) := by
  classical
  intro p
  by_contra hmissing
  have hmiss : ∀ j, dominantBin E lab hnw j ≠ p := fun j hj => hmissing ⟨j, hj⟩
  have hsmall : ∀ j : Fin s, (E.filter fun r => lab r = j ∧ r.1 = p).card ≤ T := by
    intro j
    exact ((Protocol.dominantIndex_spec Finset.univ E lab hnw j).2.2
      p (Finset.mem_univ _) (Ne.symm (hmiss j))).le
  have hsum : (E.filter fun r => r.1 = p).card =
      ∑ j : Fin s, (E.filter fun r => lab r = j ∧ r.1 = p).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := E.filter fun r => r.1 = p) (t := (Finset.univ : Finset (Fin s)))
      (f := lab) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.filter_filter, and_comm] using h
  have hle := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hsmall j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  have hp := hrows p
  omega

theorem dominantBin_injective {s L T0 T : ℕ} (E : Finset (Fin s × Fin L))
    (lab : Fin s × Fin L → Fin s)
    (hnw : NoWasteConclusion Finset.univ E lab T0 T)
    (hrows : ∀ p, T0 ≤ (E.filter fun r => r.1 = p).card)
    (hgap : s * T < T0) : Function.Injective (dominantBin E lab hnw) :=
  (Finite.injective_iff_surjective).mpr (dominantBin_surjective E lab hnw hrows hgap)

/-- The source threshold is exactly twice the dyadic tail fraction. -/
theorem threshold_identity (L b : ℕ) :
    (L : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ)) =
      2 * (2 : ℝ) ^ (-(b : ℝ)) * L := by
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

/-- The same rounded thresholds satisfy the strict separation gate needed
to prove that dominant bins are all distinct. -/
theorem threshold_separation {s L b : ℕ} {x3 : ℝ}
    (hs : 0 < s) (hL : 9216 * s ≤ L)
    (hloss : (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ 4 / 25025)
    (hx3 : (999 / 1000 : ℝ) ≤ x3) :
    s * ⌈(L : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ < ⌈(L : ℝ) * x3⌉₊ := by
  rw [threshold_identity]
  apply (ParameterGates.dense_strict_separation hs hL (by positivity) hloss).trans_le
  apply Nat.ceil_mono
  nlinarith [show (0 : ℝ) ≤ L by positivity]

/-- Integer truncation and ceiling losses still leave the stronger `998/1000`
fraction. Consequently the paper's `49/50` target has strict slack. -/
theorem dominant_count_density {s L b n : ℕ} {x3 : ℝ}
    (hs : 0 < s) (hL : 9216 * s ≤ L)
    (hloss : (s : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ 4 / 25025)
    (hx3 : (999 / 1000 : ℝ) ≤ x3)
    (hcount : ⌈(L : ℝ) * x3⌉₊ -
      (s - 1) * ⌈(L : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ ≤ n) :
    (998 / 1000 : ℝ) * L ≤ n := by
  rw [threshold_identity] at hcount
  have hx : 0 ≤ (2 : ℝ) ^ (-(b : ℝ)) := by positivity
  have hg := ParameterGates.dense_strict_separation hs hL hx hloss
  have hinit : ⌈(999 / 1000 : ℝ) * L⌉₊ ≤ ⌈(L : ℝ) * x3⌉₊ := by
    apply Nat.ceil_mono
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  have hsub : (s - 1) * ⌈2 * (2 : ℝ) ^ (-(b : ℝ)) * L⌉₊ ≤
      ⌈(L : ℝ) * x3⌉₊ := by
    have hm := Nat.mul_le_mul_right ⌈2 * (2 : ℝ) ^ (-(b : ℝ)) * L⌉₊ (Nat.sub_le s 1)
    omega
  have hc : ((⌈(L : ℝ) * x3⌉₊ : ℕ) : ℝ) -
      ((s - 1 : ℕ) : ℝ) * ⌈2 * (2 : ℝ) ^ (-(b : ℝ)) * L⌉₊ ≤ n := by
    have hh : ((⌈(L : ℝ) * x3⌉₊ -
      (s - 1) * ⌈2 * (2 : ℝ) ^ (-(b : ℝ)) * L⌉₊ : ℕ) : ℝ) ≤ n :=
      Nat.cast_le.mpr hcount
    simpa only [Nat.cast_sub hsub, Nat.cast_mul] using hh
  have hd := ParameterGates.dense_fraction_lower hs hL hx hloss
  have hLpos : (0 : ℝ) < L := by
    have hh : (9216 : ℝ) * s ≤ L := by exact_mod_cast hL
    have hh' : (0 : ℝ) < s := by exact_mod_cast hs
    nlinarith
  unfold ParameterGates.denseFraction at hd
  have hd' := (le_div_iff₀ hLpos).mp hd
  have hi : (⌈(999 / 1000 : ℝ) * L⌉₊ : ℝ) ≤ ⌈(L : ℝ) * x3⌉₊ := by
    exact_mod_cast hinit
  linarith

/-- The actual parameter formulas discharge the scalar density gates for
the literal prime-sampler index set. -/
theorem dominant_count_density_parameters (i : Parameters.Input)
    (hc : 0 < i.sourceConstant) (ha : Parameters.Accepted i)
    {n : ℕ} {x3 : ℝ} (hx3 : (999 / 1000 : ℝ) ≤ x3)
    (hcount :
      ⌈(PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
        (Parameters.firstWidth i * i.rows) : ℝ) * x3⌉₊ -
      (Parameters.bins i - 1) *
        ⌈(PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
          (Parameters.firstWidth i * i.rows) : ℝ) *
          (2 : ℝ) ^ (1 - (Parameters.tailDepth i : ℝ))⌉₊ ≤ n) :
    (49 / 50 : ℝ) *
      PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
        (Parameters.firstWidth i * i.rows) ≤ n := by
  have h := dominant_count_density (Parameters.bins_pos i)
    (ParameterGates.actualFamily_size_ge_9216_bins i hc ha)
    (ParameterGates.dense_tail_loss i).2 hx3 hcount
  have hsize : (0 : ℝ) ≤ PrimeSampler.size (Parameters.secondWidth i)
      (Parameters.balanceOrder i) (Parameters.firstWidth i * i.rows) := by positivity
  nlinarith

/-- Strict separation at the actual accepted sampler size. -/
theorem threshold_separation_parameters (i : Parameters.Input)
    (hc : 0 < i.sourceConstant) (ha : Parameters.Accepted i)
    {x3 : ℝ} (hx3 : (999 / 1000 : ℝ) ≤ x3) :
    Parameters.bins i *
      ⌈(PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
        (Parameters.firstWidth i * i.rows) : ℝ) *
        (2 : ℝ) ^ (1 - (Parameters.tailDepth i : ℝ))⌉₊ <
      ⌈(PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
        (Parameters.firstWidth i * i.rows) : ℝ) * x3⌉₊ :=
  threshold_separation (Parameters.bins_pos i)
    (ParameterGates.actualFamily_size_ge_9216_bins i hc ha)
    (ParameterGates.dense_tail_loss i).2 hx3

section Physical

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

open Classical in
/-- The selected families belong to the actual prefix branches. Their
representatives are physical retained template rows; each suffix computes
the original second matrix there, on every original retained column. -/
theorem physical_dominant_families
    (base : X → Y → Bool) (a k q L nv nb T0 T : ℕ)
    (hs : 0 < 2 ^ k) (hL : 0 < L)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ k)
    (A : Finset (ProtectedColumns a (2 ^ k) q Y))
    (B : Finset (ProtectedRows (2 ^ k) L nv nb X))
    (P : Protocol (ProtectedRows (2 ^ k) L nv nb X)
      (ProtectedColumns a (2 ^ k) q Y) Bool)
    (hpref : AllAlice k P)
    (hcomp : ∀ r ∈ B, ∀ c ∈ A, P.eval r c =
      protectedMatrix base a (2 ^ k) q L nv nb hs family order vectors cap c r)
    (phi : ThirdRows (2 ^ k) L → ProtectedRows (2 ^ k) L nv nb X)
    (hphi : ∀ r ∈ (B ∩ templateRows (2 ^ k) L nv nb).image
        (templatePair (2 ^ k) L nv nb hs hL),
      phi r ∈ B ∩ templateRows (2 ^ k) L nv nb ∧
        templatePair (2 ^ k) L nv nb hs hL (phi r) = r)
    (hrows : ∀ p : Fin (2 ^ k), T0 ≤
      (((B ∩ templateRows (2 ^ k) L nv nb).image
        (templatePair (2 ^ k) L nv nb hs hL)).filter fun r => r.1 = p).card)
    (hgap : 2 ^ k * T < T0)
    (hnw : NoWasteConclusion Finset.univ
      ((B ∩ templateRows (2 ^ k) L nv nb).image (templatePair (2 ^ k) L nv nb hs hL))
      (fun r => Protocol.prefixCodeRaw k P (phi r)) T0 T) :
    let E := (B ∩ templateRows (2 ^ k) L nv nb).image (templatePair (2 ^ k) L nv nb hs hL)
    let lab := fun r => Protocol.prefixCodeRaw k P (phi r)
    let p := dominantBin E lab hnw
    Function.Injective p ∧ ∀ j : Fin (2 ^ k),
      T0 - (2 ^ k - 1) * T ≤ (branchFamily E lab (p j) j).card ∧
      (Protocol.rowSubtreeAtRaw k P j).cost + k ≤ P.cost ∧
      ∀ z ∈ branchFamily E lab (p j) j,
        phi (p j, z) ∈ B ∩ templateRows (2 ^ k) L nv nb ∧
        Protocol.prefixCodeRaw k P (phi (p j, z)) = j ∧
        templatePair (2 ^ k) L nv nb hs hL (phi (p j, z)) = (p j, z) ∧
        ∀ c ∈ A, (Protocol.rowSubtreeAtRaw k P j).eval (phi (p j, z)) c =
          secondMatrix base a (2 ^ k) q L family (selectorTuple c (p j)) z := by
  classical
  dsimp only
  let E := (B ∩ templateRows (2 ^ k) L nv nb).image (templatePair (2 ^ k) L nv nb hs hL)
  let lab := fun r => Protocol.prefixCodeRaw k P (phi r)
  let p := dominantBin E lab hnw
  refine ⟨dominantBin_injective E lab hnw hrows hgap, ?_⟩
  intro j
  refine ⟨dominantFamily_card E lab hnw j, hpref.subtree_cost j, ?_⟩
  intro z hz
  obtain ⟨hzE, hzj⟩ := (mem_branchFamily E lab (p j) j z).mp hz
  obtain ⟨hzmem, hzval⟩ := hphi (p j, z) hzE
  refine ⟨hzmem, hzj, hzval, ?_⟩
  intro c hc
  change (Protocol.rowSubtreeAtRaw k P j).eval (phi (p j, z)) c = _
  have heval := hpref.subtree_eval (phi (p j, z)) c
  rw [show Protocol.prefixCodeRaw k P (phi (p j, z)) = j from hzj] at heval
  rw [heval]
  rw [hcomp _ (Finset.mem_inter.mp hzmem).1 c hc]
  rw [template_entry_all base a (2 ^ k) q L nv nb hs hL family order vectors cap
    c (phi (p j, z)) (Finset.mem_inter.mp hzmem).2, hzval]
  rfl

end Physical

end EthInapproximability.CurrentPaper.ProtectedDominantFamilies
