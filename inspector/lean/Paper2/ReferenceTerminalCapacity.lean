import Paper2.ReferenceProjectionMass
import Paper2.ReferenceColumnStep
import Paper2.ReferenceCertificateProtocol

/-!
# Local terminal contradictions for actual reference certificates

Frozen v12 Section 5, `res:destinations`, lines 250--310. Each terminal
argument uses the original retained rows and correlated tuple-column event.
Certificate image floors are turned into row restrictions by reachability;
no lower-bound certificate or owner count is a premise.
-/

namespace Paper2.ReferenceTerminalCapacity

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open ReferenceCertificates ReferenceCapacity

variable {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw]
  {w : ℕ}

/-- An active original certificate supplies real mass in the actual
retained row rectangle, without replacing its labelled rows. -/
theorem row_mass_of_support (μ : FiniteLaw A)
    (S : Family (Fin w) A) (lift : Fin w → A → Rw) (R : Set Rw)
    (t : ℝ)
    (hfloor : ∀ i ∈ S.active, t ≤ μ.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (i : Fin w) (hi : i ∈ S.active) :
    t ≤ μ.prob (fun a => lift i a ∈ R) := by
  apply (hfloor i hi).trans
  apply μ.prob_mono
  intro a ha
  exact hreach i hi a ha

/-- Select labelled active coordinates without changing their original
indices.  The projection is still taken from the correlated full event. -/
theorem select_active (S : Family (Fin w) A) (n : ℕ)
    (hn : n ≤ S.active.card) :
    ∃ e : Fin n → Fin w, Function.Injective e ∧
      ∀ j, e j ∈ S.active := by
  classical
  obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hn
  let equiv : Fin n ≃ {i // i ∈ T} :=
    (Fintype.equivFinOfCardEq (by simpa using hT)).symm
  refine ⟨fun j => (equiv j).val, ?_, ?_⟩
  · intro i j hij
    exact equiv.injective (Subtype.ext hij)
  · intro j
    exact hTA (equiv j).property

/-- A valid family has at most two units per active coordinate. -/
theorem units_le_twice_active (S : Family (Fin w) A)
    (hvalid : S.unsplit ⊆ S.active) :
    units S ≤ 2 * S.active.card := by
  have hcard := Finset.card_le_card hvalid
  unfold units
  omega

/-- The half-weight bookkeeping converts a real weight threshold into a
cardinality of distinct original coordinates. -/
theorem active_card_ge_of_weight (S : Family (Fin w) A)
    (hvalid : S.unsplit ⊆ S.active) (κ n : ℕ)
    (hn : 0 < n) (hgap : 16 * (n - 1) < 9 * κ)
    (hweight : (9 : ℝ) * (κ : ℝ) / 8 ≤ (units S : ℝ)) :
    n ≤ S.active.card := by
  have hu := units_le_twice_active S hvalid
  have hnat : 9 * κ ≤ 8 * units S := by
    exact_mod_cast (show (9 * (κ : ℝ)) ≤ 8 * (units S : ℝ) by linarith)
  by_contra h
  have ha : S.active.card ≤ n - 1 := by omega
  omega

/-- Transfer a public cover statement on original coordinate sets to one
enumeration of the joint retained tuple image. -/
theorem selected_mass_of_cover (ν : FiniteLaw K)
    (O : Set (Fin w → K)) (E0 : Finset (Fin w))
    (n : ℕ) (ρ : ℝ) (e : Fin n → Fin w)
    (he : Function.Injective e)
    (havoid : ∀ j, e j ∉ E0)
    (hgood : ∀ T : Finset (Fin w), T.card = n → Disjoint T E0 →
      ρ ≤ ProductProjections.projectionMass (fun _ => ν) (· ∈ O) T) :
    ρ ≤ (ν.iid n).prob (· ∈ selectedColumns e O) := by
  classical
  let T : Finset (Fin w) := Finset.univ.image e
  have hcard : T.card = n := by
    simpa [T] using (Finset.card_image_of_injective Finset.univ he)
  have hdis : Disjoint T E0 := by
    apply Finset.disjoint_left.mpr
    intro i hi hE
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact havoid j hE
  have hmass := hgood T hcard hdis
  rw [ReferenceProjectionMass.projectionMass_eq_selectedColumns_of_injective
    ν O T e he rfl] at hmass
  exact hmass

/-- The public large-capacity cutoff gives the strong-seed threshold;
the latter is not an extra asymptotic assumption in the source wrapper. -/
theorem public_seed_guard (Q l : ℕ) (hQ : 0 < Q)
    (hl : RestorationCoverParameters.tExponent Q ≤ l) :
    (2 : ℝ) ^ (-((2 : ℝ) ^ l / 1024)) ≤
      RestorationCoverParameters.theta Q / 2 := by
  open RestorationCoverParameters in
  have hwidth : 1024 * (b Q + 1) ≤ 2 ^ l := by
    calc
      1024 * (b Q + 1) ≤ tStar Q := SourcePadding.le_powTwoCeil _
      _ = 2 ^ tExponent Q := tStar_pow Q
      _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  have hexp : -((2 : ℝ) ^ l / 1024) ≤ -((b Q + 1 : ℕ) : ℝ) := by
    have hw : (1024 * (b Q + 1) : ℝ) ≤ (2 : ℝ) ^ l := by
      exact_mod_cast hwidth
    push_cast at hw ⊢
    nlinarith
  calc
    (2 : ℝ) ^ (-((2 : ℝ) ^ l / 1024)) ≤
        (2 : ℝ) ^ (-((b Q + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (1 / 2 : ℝ) ^ b Q / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_succ]
      simp [one_div, inv_mul_eq_div, inv_pow]
    _ ≤ RestorationCoverParameters.theta Q / 2 := by
      exact div_le_div_of_nonneg_right
        (RestorationCoverParameters.two_neg_b_le_theta hQ) (by norm_num)

private theorem restriction_le_computing_protocol
    (M : Rw → (Fin w → K) → Bool)
    (R : Set Rw) (O : Set (Fin w → K))
    (P : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O, P.eval r y = M r y) :
    Compression.restrictionD M R O ≤ P.cost := by
  classical
  let Q := Workspace.UpperBound.Protocol.comap
    (fun r : R => r.val) (fun y : O => y.val) P
  have hQ : Q.Computes
      (fun (r : R) (y : O) => M r.val y.val) := by
    intro r y
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
      hcompute r.val r.property y.val y.property
  have hD : Compression.restrictionD M R O ≤ Q.cost :=
    Nat.sInf_le ⟨Q, rfl, hQ⟩
  simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using hD

private theorem two_selected_bob_impossible
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (H : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin 2 → Fin w)
    (hrow : ∀ j, 2 * x ≤ μ.toFiniteLaw.prob (fun a => lift (e j) a ∈ R))
    (hcol : (18 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (· ∈ selectedColumns e O))
    (hcost : (Protocol.bNode query left right).cost ≤ H + 1) : False := by
  obtain ⟨b, hb⟩ := ReferenceColumnStep.exists_dense_projected_child
    (ν.toFiniteLaw.iid 2) (fun y j => y (e j)) O query (18 / 25) hcol
  have hentry' : ∀ j a, lift (e j) a ∈ R →
      ∀ y ∈ ReferenceColumnStep.columnChild O query b,
        M (lift (e j) a) y = F a (y (e j)) := by
    intro j a ha y hy
    exact hentry (e j) a ha y hy.1
  have hchild : H + 1 ≤ Compression.restrictionD M R
      (ReferenceColumnStep.columnChild O query b) := by
    apply ReferenceCapacity.small_two μ ν F M lift e R
      (ReferenceColumnStep.columnChild O query b) hentry' H x hH hx hscale
      hprofile Finset.univ (by simp) (by simpa using hrow)
    simpa only [selectedColumns] using (show (9 / 25 : ℝ) ≤
      (ν.toFiniteLaw.iid 2).prob (· ∈ selectedColumns e
        (ReferenceColumnStep.columnChild O query b)) by
          dsimp only [selectedColumns]
          convert hb using 1; norm_num)
  have hbit := ReferenceColumnStep.restriction_add_one_le M R O query
    left right hcompute b
  omega

private theorem power_selected_bob_impossible
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (H l : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hl : 2 ≤ l) (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin (2 ^ (l - 1) + 1) → Fin w)
    (hrow : ∀ j, (2 : ℝ) ^ l * x ≤
      μ.toFiniteLaw.prob (fun a => lift (e j) a ∈ R))
    (hcol : (18 / 25 : ℝ) ≤
      (ν.toFiniteLaw.iid (2 ^ (l - 1) + 1)).prob (· ∈ selectedColumns e O))
    (hcost : (Protocol.bNode query left right).cost ≤ H + l) : False := by
  obtain ⟨b, hb⟩ := ReferenceColumnStep.exists_dense_projected_child
    (ν.toFiniteLaw.iid (2 ^ (l - 1) + 1))
    (fun y j => y (e j)) O query (18 / 25) hcol
  have hentry' : ∀ j a, lift (e j) a ∈ R →
      ∀ y ∈ ReferenceColumnStep.columnChild O query b,
        M (lift (e j) a) y = F a (y (e j)) := by
    intro j a ha y hy
    exact hentry (e j) a ha y hy.1
  have hchild : H + l ≤ Compression.restrictionD M R
      (ReferenceColumnStep.columnChild O query b) := by
    apply ReferenceCapacity.small_power μ ν F M lift e R
      (ReferenceColumnStep.columnChild O query b) hentry' H l x hH hx hl hscale
      hprofile Finset.univ (by simp) (by simpa using hrow)
    simpa only [selectedColumns] using (show (9 / 25 : ℝ) ≤
      (ν.toFiniteLaw.iid (2 ^ (l - 1) + 1)).prob (· ∈ selectedColumns e
        (ReferenceColumnStep.columnChild O query b)) by
          dsimp only [selectedColumns]
          convert hb using 1; norm_num)
  have hbit := ReferenceColumnStep.restriction_add_one_le M R O query
    left right hcompute b
  omega

private theorem seed_selected_bob_impossible
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (H l : ℕ) (x θ : ℝ) (hH : 3 ≤ H) (hx : 0 < x)
    (hl : 4 ≤ l) (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin (StrongSeed.copies l) → Fin w)
    (hrow : ∀ j, (2 : ℝ) ^ l * x ≤
      μ.toFiniteLaw.prob (fun a => lift (e j) a ∈ R))
    (hcol : θ ≤ (ν.toFiniteLaw.iid (StrongSeed.copies l)).prob
      (· ∈ selectedColumns e O))
    (hseed : (2 : ℝ) ^ (-((2 : ℝ) ^ l / 1024)) ≤ θ / 2)
    (hcost : (Protocol.bNode query left right).cost ≤ H + l) : False := by
  obtain ⟨b, hb⟩ := ReferenceColumnStep.exists_dense_projected_child
    (ν.toFiniteLaw.iid (StrongSeed.copies l))
    (fun (y : Fin w → K) (j : Fin (StrongSeed.copies l)) => y (e j))
    O query θ (by simpa only [selectedColumns] using hcol)
  have hentry' : ∀ j a, lift (e j) a ∈ R →
      ∀ y ∈ ReferenceColumnStep.columnChild O query b,
        M (lift (e j) a) y = F a (y (e j)) := by
    intro j a ha y hy
    exact hentry (e j) a ha y hy.1
  have hchild : H + l ≤ Compression.restrictionD M R
      (ReferenceColumnStep.columnChild O query b) := by
    apply ReferenceCapacity.strong_seed μ ν F M lift e R
      (ReferenceColumnStep.columnChild O query b) hentry'
      H x hH hl hx hscale hprofile hrow
    simpa only [selectedColumns] using hseed.trans hb
  have hbit := ReferenceColumnStep.restriction_add_one_le M R O query
    left right hcompute b
  omega

/-- At the final physical stopping level, two distinct active reference
coordinates force the original retained rectangle above its budget. -/
theorem final_active_le_one
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (P : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O, P.eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (E0 : Finset (Fin w))
    (H : ℕ) (x : ℝ)
    (havoid : Disjoint S.active E0)
    (hfloor : ∀ i ∈ S.active,
      2 * x ≤ μ.toFiniteLaw.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (hpair : ∀ T : Finset (Fin w), T.card = 2 → Disjoint T E0 →
      (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcost : P.cost ≤ H) : S.active.card ≤ 1 := by
  classical
  by_contra hn
  have htwo : 2 ≤ S.active.card := by omega
  obtain ⟨e, he, hmem⟩ := select_active S 2 htwo
  have hrow : ∀ j, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R) := by
    intro j
    exact row_mass_of_support μ.toFiniteLaw S lift R (2 * x)
      hfloor hreach (e j) (hmem j)
  have hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (· ∈ selectedColumns e O) := by
    have hmass := selected_mass_of_cover ν.toFiniteLaw O E0 2
      (99 / 100 : ℝ) e he
      (fun j => Finset.disjoint_left.mp havoid (hmem j)) hpair
    linarith
  have hlow : H + 1 ≤ Compression.restrictionD M R O := by
    apply ReferenceCapacity.small_two μ ν F M lift e R O
      (by intro j a ha y hy; exact hentry (e j) a ha y hy)
      H x hH hx hscale hprofile Finset.univ (by simp)
      (by simpa using hrow)
    exact hcol
  have hupp : Compression.restrictionD M R O ≤ P.cost := by
    classical
    let Q := Workspace.UpperBound.Protocol.comap
      (fun r : R => r.val) (fun y : O => y.val) P
    have hQ : Q.Computes
        (fun (r : R) (y : O) => M r.val y.val) := by
      intro r y
      simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
        hcompute r.val r.property y.val y.property
    have hD : Compression.restrictionD M R O ≤ Q.cost :=
      Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using hD
  omega

/-- The capacity-two first-Bob node cannot carry the threshold weight.
The 18/25 cover is evaluated before this actual Bob query. -/
theorem first_bob_two_units_lt
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (hvalid : S.unsplit ⊆ S.active)
    (E0 : Finset (Fin w)) (havoid : Disjoint S.active E0)
    (H : ℕ) (x : ℝ)
    (hfloor : ∀ i ∈ S.active,
      2 * x ≤ μ.toFiniteLaw.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (hpair : ∀ T : Finset (Fin w), T.card = 2 → Disjoint T E0 →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcost : (Protocol.bNode query left right).cost ≤ H + 1) :
    (units S : ℝ) < 9 * (2 : ℝ) / 8 := by
  classical
  by_contra hn
  have hweight : (9 : ℝ) * (2 : ℝ) / 8 ≤ (units S : ℝ) :=
    le_of_not_gt hn
  have htwo : 2 ≤ S.active.card :=
    active_card_ge_of_weight S hvalid 2 2 (by omega) (by norm_num) hweight
  obtain ⟨e, he, hmem⟩ := select_active S 2 htwo
  have hrow : ∀ j, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R) := by
    intro j
    exact row_mass_of_support μ.toFiniteLaw S lift R (2 * x)
      hfloor hreach (e j) (hmem j)
  have hcol : (18 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (· ∈ selectedColumns e O) :=
    selected_mass_of_cover ν.toFiniteLaw O E0 2 (18 / 25 : ℝ)
      e he (fun j => Finset.disjoint_left.mp havoid (hmem j)) hpair
  exact two_selected_bob_impossible μ ν F M lift R O query left right
    hcompute hentry H x hH hx hscale hprofile e hrow hcol hcost

/-- A small dyadic first-Bob node uses `2^(l-1)+1` distinct active
original coordinates from the actual family. -/
theorem first_bob_power_units_lt
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (hvalid : S.unsplit ⊆ S.active)
    (E0 : Finset (Fin w)) (havoid : Disjoint S.active E0)
    (H l : ℕ) (x : ℝ) (hl : 2 ≤ l)
    (hfloor : ∀ i ∈ S.active,
      (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (hgood : ∀ T : Finset (Fin w), T.card = 2 ^ (l - 1) + 1 →
      Disjoint T E0 →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcost : (Protocol.bNode query left right).cost ≤ H + l) :
    (units S : ℝ) < 9 * ((2 ^ l : ℕ) : ℝ) / 8 := by
  classical
  by_contra hn
  have hweight : (9 : ℝ) * ((2 ^ l : ℕ) : ℝ) / 8 ≤ (units S : ℝ) :=
    le_of_not_gt hn
  have hp : 2 ^ l = 2 * 2 ^ (l - 1) := by
    have he : l - 1 + 1 = l := by omega
    conv_lhs => rw [← he, pow_succ]
    omega
  have hgap : 16 * ((2 ^ (l - 1) + 1) - 1) < 9 * 2 ^ l := by
    have hpos : 0 < 2 ^ (l - 1) := by positivity
    omega
  have hcard : 2 ^ (l - 1) + 1 ≤ S.active.card :=
    active_card_ge_of_weight S hvalid (2 ^ l) (2 ^ (l - 1) + 1)
      (by omega) hgap hweight
  obtain ⟨e, he, hmem⟩ := select_active S (2 ^ (l - 1) + 1) hcard
  have hrow : ∀ j, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R) := by
    intro j
    exact row_mass_of_support μ.toFiniteLaw S lift R ((2 : ℝ) ^ l * x)
      hfloor hreach (e j) (hmem j)
  have hcol : (18 / 25 : ℝ) ≤
      (ν.toFiniteLaw.iid (2 ^ (l - 1) + 1)).prob (· ∈ selectedColumns e O) :=
    selected_mass_of_cover ν.toFiniteLaw O E0 (2 ^ (l - 1) + 1)
      (18 / 25 : ℝ) e he
      (fun j => Finset.disjoint_left.mp havoid (hmem j)) hgood
  exact power_selected_bob_impossible μ ν F M lift R O query left right
    hcompute hentry H l x hH hx hl hscale hprofile e hrow hcol hcost

/-- In the large-capacity range, selection of `9·2^l/16` active labels
and whole-event projection suffice.  No cover or coordinate-independence
premise is used. -/
theorem first_bob_seed_units_lt
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (hvalid : S.unsplit ⊆ S.active)
    (H l : ℕ) (x θ : ℝ) (hl : 4 ≤ l)
    (hfloor : ∀ i ∈ S.active,
      (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (hY : θ ≤ (ν.toFiniteLaw.iid w).prob (· ∈ O))
    (hseed : (2 : ℝ) ^ (-((2 : ℝ) ^ l / 1024)) ≤ θ / 2)
    (hH : 3 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcost : (Protocol.bNode query left right).cost ≤ H + l) :
    (units S : ℝ) < 9 * ((2 ^ l : ℕ) : ℝ) / 8 := by
  classical
  by_contra hn
  have hweight : (9 : ℝ) * ((2 ^ l : ℕ) : ℝ) / 8 ≤ (units S : ℝ) :=
    le_of_not_gt hn
  have hgap : 16 * (StrongSeed.copies l - 1) < 9 * 2 ^ l := by
    rw [StrongSeed.pow_split l hl]
    unfold StrongSeed.copies
    have hpos : 0 < 2 ^ (l - 4) := by positivity
    omega
  have hcard : StrongSeed.copies l ≤ S.active.card :=
    active_card_ge_of_weight S hvalid (2 ^ l) (StrongSeed.copies l)
      (by unfold StrongSeed.copies; positivity) hgap hweight
  obtain ⟨e, he, hmem⟩ := select_active S (StrongSeed.copies l) hcard
  have hrow : ∀ j, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R) := by
    intro j
    exact row_mass_of_support μ.toFiniteLaw S lift R ((2 : ℝ) ^ l * x)
      hfloor hreach (e j) (hmem j)
  have hcol : θ ≤ (ν.toFiniteLaw.iid (StrongSeed.copies l)).prob
      (· ∈ selectedColumns e O) :=
    hY.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he O)
  exact seed_selected_bob_impossible μ ν F M lift R O query left right
    hcompute hentry H l x θ hH hx hl hscale hprofile e hrow hcol hseed hcost

/-- All first-Bob capacities in the public schedule, on the original
retained matrix and one correlated column event. -/
theorem first_bob_units_lt
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (query : (Fin w → K) → Bool)
    (left right : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (hvalid : S.unsplit ⊆ S.active)
    (E0 : Finset (Fin w)) (havoid : Disjoint S.active E0)
    (Q H l : ℕ) (x : ℝ) (hQ : 0 < Q) (hl : 1 ≤ l)
    (hfloor : ∀ i ∈ S.active,
      (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (· ∈ (S.support i : Set A)))
    (hreach : ∀ i ∈ S.active, ∀ a ∈ S.support i, lift i a ∈ R)
    (hpair : ∀ T : Finset (Fin w), T.card = 2 → Disjoint T E0 →
      (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hdyadic : ∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
      ∀ T : Finset (Fin w), T.card = RestorationCovers.smallSize j.val →
        Disjoint T E0 →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => ν.toFiniteLaw) (· ∈ O) T)
    (hY : RestorationCoverParameters.theta Q ≤
      (ν.toFiniteLaw.iid w).prob (· ∈ O))
    (hH : 3 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcost : (Protocol.bNode query left right).cost ≤ H + l) :
    (units S : ℝ) < 9 * ((2 ^ l : ℕ) : ℝ) / 8 := by
  by_cases htwo : l = 1
  · subst l
    simpa only [pow_one, Nat.cast_ofNat] using
      first_bob_two_units_lt μ ν F M lift R O query left right
        hcompute hentry S hvalid E0 havoid H x
        (by simpa only [pow_one] using hfloor) hreach hpair
        (by omega) hx (by simpa only [pow_one] using hscale)
        hprofile (by simpa only [Nat.add_comm] using hcost)
  · have hl2 : 2 ≤ l := by omega
    by_cases hsmall : l < RestorationCoverParameters.tExponent Q
    · let j : Fin (RestorationCoverParameters.tExponent Q - 2) :=
        ⟨l - 2, by omega⟩
      have hsize : RestorationCovers.smallSize j.val = 2 ^ (l - 1) + 1 := by
        simp only [RestorationCovers.smallSize, j]
        congr 2
        omega
      have hgood : ∀ T : Finset (Fin w), T.card = 2 ^ (l - 1) + 1 →
          Disjoint T E0 →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => ν.toFiniteLaw) (· ∈ O) T := by
        intro T hcard hdis
        exact hdyadic j T (by rw [hsize]; exact hcard) hdis
      exact first_bob_power_units_lt μ ν F M lift R O query left right
        hcompute hentry S hvalid E0 havoid H l x hl2 hfloor hreach
        hgood (by omega) hx hscale hprofile hcost
    · have hlarge : RestorationCoverParameters.tExponent Q ≤ l := by omega
      have hl4 : 4 ≤ l := by
        have hge := RestorationCoverParameters.tStar_ge Q
        have hp := RestorationCoverParameters.tStar_pow Q
        by_contra hn
        have hle : RestorationCoverParameters.tExponent Q ≤ 3 := by omega
        have hpow : 2 ^ RestorationCoverParameters.tExponent Q ≤ 2 ^ 3 :=
          pow_le_pow_right₀ (by norm_num) hle
        omega
      exact first_bob_seed_units_lt μ ν F M lift R O query left right
        hcompute hentry S hvalid H l x (RestorationCoverParameters.theta Q)
        hl4 hfloor hreach hY (public_seed_guard Q l hQ hlarge)
        hH hx hscale hprofile hcost

/-- An original early physical leaf is impossible once an active source
coordinate retains its scalar row floor and singleton-good projection.
This argument does not use the padded runner's structural `NoEarlyLeaf`. -/
theorem original_early_leaf_impossible
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (R : Set Rw) (O : Set (Fin w → K))
    (P : Protocol Rw (Fin w → K) Bool)
    (hcompute : ∀ r ∈ R, ∀ y ∈ O, P.eval r y = M r y)
    (hentry : ∀ i a, lift i a ∈ R → ∀ y ∈ O,
      M (lift i a) y = F a (y i))
    (S : Family (Fin w) A) (i : Fin w) (hi : i ∈ S.active)
    (H : ℕ) (x eta : ℝ) (hH : 1 ≤ H) (heta : eta < 2 / 5)
    (hfloor : ∀ j ∈ S.active,
      x ≤ μ.toFiniteLaw.prob (· ∈ (S.support j : Set A)))
    (hreach : ∀ j ∈ S.active, ∀ a ∈ S.support j, lift j a ∈ R)
    (hgood : 1 - eta ≤ ProductProjections.projectionMass
      (fun _ => ν.toFiniteLaw) (· ∈ O) ({i} : Finset (Fin w)))
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hleaf : P.cost = 0) : False := by
  let U : Set A := {a | lift i a ∈ R}
  let V : Set K := (fun y : Fin w → K => y i) '' O
  have hrow : x ≤ μ.toFiniteLaw.prob (· ∈ U) := by
    apply (hfloor i hi).trans
    apply μ.toFiniteLaw.prob_mono
    intro a ha
    exact hreach i hi a ha
  have hcol : (3 / 5 : ℝ) ≤ ν.toFiniteLaw.prob (· ∈ V) := by
    have hh := ReferenceProjectionMass.singleton_image_mass_ge
      ν.toFiniteLaw O i (1 - eta) hgood
    dsimp only [V]
    linarith
  have hlow : H ≤ Compression.restrictionD F U V := by
    have hh := hprofile ⟨0, by omega⟩ U V hrow (by simpa using hcol)
    simp only [Nat.cast_zero, sub_zero] at hh
    exact_mod_cast hh
  have hproject : Compression.restrictionD F U V ≤
      Compression.restrictionD M R O := by
    apply SourceProjection.restrictionD_projected_le M F (lift i)
      (fun y : Fin w → K => y i) R O U
    · intro a ha
      exact ha
    · intro a ha y hy
      exact hentry i a ha y hy
  have hupp := restriction_le_computing_protocol M R O P hcompute
  omega

end Paper2.ReferenceTerminalCapacity

#print axioms Paper2.ReferenceTerminalCapacity.public_seed_guard
#print axioms Paper2.ReferenceTerminalCapacity.first_bob_units_lt
#print axioms Paper2.ReferenceTerminalCapacity.final_active_le_one
#print axioms Paper2.ReferenceTerminalCapacity.original_early_leaf_impossible
