import EthInapproximability.CurrentPaper.ReceivingCapacity
import EthInapproximability.CurrentPaper.ParameterGates

/-!
# Concrete gates for the protected receiving argument

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-capacity`,
and `F-parameter-choices.tex`, the several-copy stopping call.

The family is the literal indexed prime sampler, not a certificate of a
communication bound.  Its balance and the scalar stopping inequalities are
derived from the published parameter formulas.  These lemmas are upstream of
the actual-protocol receiving theorem in `ReceivingCapacity`.
-/

noncomputable section
open scoped Classical

namespace EthInapproximability.CurrentPaper.ConcreteRouting

open Parameters ParameterGates Construction NPCC

/-- The actual indexed second family used in the accepted construction. -/
def actualFamily (i : Input) (ha : Accepted i) :=
  PrimeSampler.secondFamily (firstExponent i) (secondWidth i) (balanceOrder i)
    (firstWidth i * i.rows)
    (lt_of_lt_of_le (by decide : 0 < 2) (samplerAlphabet_ge_two i ha.1))
    (PrimeSampler.canonicalFirstRowsEquiv (firstExponent i) i.rows)

/-- Arbitrarily many independent copies of the actual family retain a
uniform error of at most `1/50` at the required query order. -/
theorem actual_product_balanced (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (v : ℕ) :
    IsBalancedFamily (2 ^ balanceExponent i)
      (ProductBalancedness.productFamily v (actualFamily i ha)) (1 / 50) := by
  obtain ⟨hbal, herr⟩ := ProductBalancedness.product_balanced_small v
    (actualSecondFamily_balanced i hc ha) (balanceOrder_pos i)
    (by positivity) (le_refl _)
  exact ProductBalancedness.balanced_mono_error hbal herr.le

/-- Equality-decision implementations do not change a finite balance claim. -/
theorem balanced_change_decidable {Y : Type*} [Fintype Y]
    {d₁ d₂ : DecidableEq Y} {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (h : @IsBalancedFamily Y d₁ _ q L t S ε) :
    @IsBalancedFamily Y d₂ _ q L t S ε := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact h

theorem accepted_balance_exponent_le (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) : balanceExponent i ≤ secondExponent i := by
  have h := accepted_balance_four_le_second i hc ha
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  change balanceOrder i ≤ secondWidth i
  omega

/-- The loss of the selected common tuple set fits the one fixed budget,
including the actual Bob-child halving. -/
theorem packet_density_ge_budget (i : Input) (e : ℕ)
    (he : e ≤ outerExponent i) :
    (2 : ℝ) ^ (-(lossBudget i : ℝ)) ≤
      ((99 / 100 : ℝ) / 2) / 2 ^ (2 ^ e + 1) := by
  have hv : 2 ^ e ≤ outerWidth i := Nat.pow_le_pow_right (by decide) he
  have hd : 2 ^ e + 3 ≤ lossBudget i := by unfold lossBudget; omega
  have hr : (2 : ℝ) ^ (-(lossBudget i : ℝ)) ≤
      (2 : ℝ) ^ (-((2 ^ e + 3 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (by exact_mod_cast hd))
  apply hr.trans
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hp : (0 : ℝ) < 2 ^ (2 ^ e + 1) := by positivity
  rw [show 2 ^ e + 3 = (2 ^ e + 1) + 2 by omega, pow_add]
  norm_num only [pow_two]
  rw [← one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 ^ e + 1) * 4) hp).2
  nlinarith

/-- The paper's fixed projection-cover budget. -/
def coverBudget (i : Input) : ℕ := 100 * (retainedExponent i + 1)

theorem coverBudget_pos (i : Input) : 1 ≤ coverBudget i := by
  unfold coverBudget
  omega

/-- The chosen cover budget works for the actual retained column fraction. -/
theorem actual_cover_gate (i : Input) :
    (99 / 100 : ℝ) ^ coverBudget i < (retainedFraction i : ℚ) := by
  have hbase : (99 / 100 : ℝ) ^ 100 < 1 / 2 := by norm_num
  have hp : ((99 / 100 : ℝ) ^ 100) ^ (retainedExponent i + 1) <
      (1 / 2 : ℝ) ^ (retainedExponent i + 1) := by gcongr
  have hhalf : (1 / 2 : ℝ) ^ (retainedExponent i + 1) ≤
      (1 / 2 : ℝ) ^ retainedExponent i := by
    rw [pow_succ]
    nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ retainedExponent i by positivity]
  have hid : (1 / 2 : ℝ) ^ retainedExponent i =
      (2 : ℝ) ^ (-(retainedExponent i : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div, inv_pow]
  unfold coverBudget
  rw [pow_mul]
  exact hp.trans_le (hhalf.trans (hid ▸ retainedFraction_dyadic_lower i))

/-- Both analytic stopping hypotheses of the actual receiving theorem are
consequences of acceptance and the literal parameter formulas. -/
theorem actual_packet_stopping (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (H e : ℕ) (hH : H ≤ i.cost + firstExponent i)
    (he : e ≤ outerExponent i) :
    (3 / 5 : ℝ) ≤ yLoss (1 / 50) (2 ^ balanceExponent i)
      (((99 / 100 : ℝ) / 2) / 2 ^ (2 ^ e + 1))
      (H + ((e - 1 + secondExponent i - balanceExponent i) + balanceExponent i)) ∧
    HardSeed.columnDensity ((2 : ℝ) ^ balanceExponent i) ≤
      (((99 / 100 : ℝ) / 2) / 2 ^ (2 ^ e + 1)) *
        (2 : ℝ) ^ (-((H + balanceExponent i : ℕ) : ℝ)) / (1 + 1 / 50) := by
  have hmq := accepted_balance_exponent_le i hc ha
  have hadd : (e - 1 + secondExponent i - balanceExponent i) + balanceExponent i =
      e - 1 + secondExponent i := Nat.sub_add_cancel (by omega)
  have h := all_stopping_gates i hH
    (show e - 1 + secondExponent i ≤ outerExponent i + secondExponent i by omega)
    (packet_density_ge_budget i e he) (by norm_num : (0 : ℝ) ≤ 1 / 50)
    (by norm_num : (1 / 50 : ℝ) ≤ 1)
  simpa only [hadd, yLoss, balanceOrder, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The scalar donor-count gate is weaker than the checked inner-loss bound.
In particular it does not depend on a protocol or on a selected density bin. -/
theorem actual_packet_count_gate (i : Input) (B : ℕ) (hB : 1 ≤ B) :
    (2 : ℝ) ^ outerExponent i * (2 : ℝ) ^ secondExponent i *
      (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 8 * (B : ℝ) * (outerExponent i + 2 : ℕ) := by
  have h := inner_many_loss i
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hr : (2 : ℝ) ≤ (outerExponent i + 2 : ℕ) := by exact_mod_cast (Nat.le_add_left 2 _)
  simp only [outerWidth, secondWidth, Nat.cast_pow, Nat.cast_ofNat] at h
  nlinarith

open Workspace.Types.CommComplexity Workspace.Types.Interlace JointTransfer

/-- Exact multiplicity of each full-group template input. -/
theorem full_row_multiplicity (X : Type*) [Fintype X] (s L nv nb : ℕ) :
    fullRowMultiplicity (X := X) s L nv nb =
      (2 ^ 22 - 4) * (s * L) * (nv * Fintype.card X) * (nb * Fintype.card X) := by
  norm_num [fullRowMultiplicity, WeightedDuplication.copies,
    WeightedDuplication.card_rowSupport, WeightedDuplication.rowWeight,
    show (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} by decide,
    Finset.prod_insert, Finset.prod_singleton,
    Fin.prod_univ_succ, Finset.prod_filter, TemplateSupport, ThirdRows,
    VertexRows, AuxiliaryRows]
  simp
  ring

theorem extra_template_multiplicity (X : Type*) [Fintype X] (s L nv nb : ℕ) :
    extraTemplateMultiplicity (X := X) s L nv nb =
      2 * (s * L + (nv + nb) * Fintype.card X) *
        (nv * Fintype.card X) * (nb * Fintype.card X) := by
  norm_num [extraTemplateMultiplicity, WeightedDuplication.copies,
    WeightedDuplication.card_rowSupport, WeightedDuplication.rowWeight,
    show (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} by decide,
    Finset.prod_insert, Finset.prod_singleton,
    Fin.prod_univ_succ, Finset.prod_filter, TemplateSupport, ThirdRows,
    VertexRows, AuxiliaryRows, card_rawRows]
  simp
  ring

/-- Physical template density follows from the small raw source population.
The labels from BOTH the full and extra-template groups are counted. -/
theorem template_proportion_of_raw_count (X : Type*) [Fintype X]
    (s L nv nb : ℕ) (hs : 0 < s)
    (hsource : 1000 * ((nv + nb) * Fintype.card X) ≤ s * L) :
    (99 / 100 : ℝ) * Fintype.card (ProtectedRows s L nv nb X) ≤
      (ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card := by
  have hnum : 99 * (2 ^ 22 * (s * L + (nv + nb) * Fintype.card X)) ≤
      100 * ((2 ^ 22 - 2) * (s * L) + 2 * ((nv + nb) * Fintype.card X)) := by
    norm_num at *
    omega
  have hmul := Nat.mul_le_mul_right
    (s * L * (nv * Fintype.card X) * (nb * Fintype.card X)) hnum
  have hcount : 99 * Fintype.card (ProtectedRows s L nv nb X) ≤
      100 * (ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card := by
    rw [card_protectedRows, ReceivingCapacityTemplate.fullTemplate_card hs]
    simp only [TemplateLabels, Fintype.card_sum, Fintype.card_fin,
      full_row_multiplicity, extra_template_multiplicity]
    norm_num at hmul ⊢
    nlinarith only [hmul]
  have hreal : (99 : ℝ) * Fintype.card (ProtectedRows s L nv nb X) ≤
      100 * (ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card := by
    exact_mod_cast hcount
  linarith

/-- No-isolated-vertex graphs satisfy `v ≤ 2*edges`.  The actual sampler
then dominates every copied source and auxiliary row by the required factor.
This is a numeric consequence, not an extra acceptance condition. -/
theorem actual_raw_source_count (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (v : ℕ) (hv : v ≤ 2 * i.edges) :
    1000 * ((4 * bins i * v + 4 * bins i * (bins i - 3)) * i.rows) ≤
      bins i * PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  have hs := bins_pos i
  have hq := accepted_secondWidth_ge_9216_bins i hc ha
  have he0 : 12 * bins i * i.edges ≤ secondWidth i := Nat.le_pow_clog (by decide) _
  have he : 12 * i.edges ≤ secondWidth i := by
    calc
      12 * i.edges = 12 * 1 * i.edges := by ring
      _ ≤ 12 * bins i * i.edges := by gcongr; omega
      _ ≤ _ := he0
  have hq0 : 9216 ≤ secondWidth i := by nlinarith
  have hn : 4000 * (v + (bins i - 3)) ≤ secondWidth i ^ 2 := by
    have hsub : bins i - 3 ≤ bins i := Nat.sub_le _ _
    nlinarith
  have h1 : 1 ≤ firstWidth i := firstWidth_pos i
  have hn' : 4000 * (v + (bins i - 3)) ≤ firstWidth i * secondWidth i ^ 2 :=
    hn.trans (Nat.le_mul_of_pos_left _ h1)
  have hmul := Nat.mul_le_mul_right (bins i * i.rows) hn'
  have hsize := actualFamily_size_ge_alphabet_mul_square i hc ha
  calc
    _ ≤ bins i * ((firstWidth i * i.rows) * secondWidth i ^ 2) := by
      nlinarith only [hmul]
    _ ≤ _ := Nat.mul_le_mul_left _ hsize

/-- The fixed `99/100` template fraction holds for the literal sampler and
the copied graph-item counts. -/
theorem actual_template_proportion (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (v : ℕ) (hv : v ≤ 2 * i.edges) :
    (99 / 100 : ℝ) * Fintype.card (ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
      (4 * bins i * v) (4 * bins i * (bins i - 3)) (Fin i.rows)) ≤
      (ReceivingCapacityTemplate.fullTemplate (X := Fin i.rows) (bins i)
        (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
        (4 * bins i * v) (4 * bins i * (bins i - 3))).card := by
  exact template_proportion_of_raw_count (Fin i.rows) _ _ _ _ (bins_pos i)
    (by simpa only [Fintype.card_fin] using actual_raw_source_count i hc ha v hv)

-- Do not unfold the prime search merely to compare its index carriers.
attribute [local irreducible] ParameterizedNP.BalancedFamilyBuilder.balN
attribute [local irreducible] Parameters.scale Parameters.scaleBound
  PrimeSampler.secondFamily ProductBalancedness.productFamily actualFamily

/-- Actual accepted-family receiving lower bound.  All packet extraction,
product-balance, cover, count, width and stopping gates are proved here; the
two first-matrix restriction bounds and the physical template proportion
remain the stated upstream construction facts. -/
theorem incoming_child_cost_parameters
    (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
    (nv nb k : ℕ) (hv : 0 < nv) (hb : 0 < nb) (hk : 1 ≤ k)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)
    (A : Finset (Fin (outerWidth i) × ProtectedColumns (firstExponent i)
      (bins i) (secondWidth i) Y))
    (S : Finset (Fin (outerWidth i) → ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
      (Fin i.rows)))
    (J : Finset (Fin (outerWidth i)))
    (b : (Fin (outerWidth i) → ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
      (Fin i.rows)) → Bool)
    (hS : (retainedFraction i : ℚ) * (Fintype.card (ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
      (Fin i.rows)) : ℝ) ^ outerWidth i ≤ S.card)
    (hTemplate : (99 / 100 : ℝ) * Fintype.card (ProtectedRows (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
      (Fin i.rows)) ≤ (ReceivingCapacityTemplate.fullTemplate (X := Fin i.rows) (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb).card)
    (h1 : i.cost + firstExponent i ≤ Dfamily
      (interlaceFun (fun γ r => firstMatrix R (firstExponent i) (bins i) r γ) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 5)))
    (h2 : i.cost + firstExponent i - 1 ≤ Dfamily
      (interlaceFun (fun γ r => firstMatrix R (firstExponent i) (bins i) r γ) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 10)))
    (hmass : 64 * (coverBudget i : ℝ) * (outerExponent i + 2 : ℕ) * bins i * (2 : ℝ) ^ k *
      (diagonalRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)).card ≤
      (ReceivingCapacity.incomingRows A
        (diagonalRows (firstExponent i) (bins i) (secondWidth i)) J).card) :
    ∃ bit : Bool, i.cost + firstExponent i + (binExponent i + k + secondExponent i) ≤
      D (subgame (interlaceFun
        (protectedMatrix R (firstExponent i) (bins i) (secondWidth i)
          (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
          (bins_pos i) (actualFamily i ha) order vectors cap) (outerWidth i))
        A (S.filter (fun y => b y = bit))) := by
  letI : Nonempty (Fin i.rows) := ⟨⟨0, by have := ha.1; omega⟩⟩
  have hmq := accepted_balance_exponent_le i hc ha
  have hH : 2 ≤ i.cost + firstExponent i := by
    have h := (hard_seed_exponent_domains i).2.2.1
    omega
  apply ReceivingCapacity.incoming_child_cost R (firstExponent i) (bins i)
    (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)) nv nb
    (outerExponent i) (coverBudget i) (2 ^ k) (secondExponent i)
    (binExponent i + k + secondExponent i) (i.cost + firstExponent i) (balanceExponent i)
    (show 0 < qOne (firstExponent i) from firstWidth_pos i) (bins_pos i)
    (PrimeSampler.size_pos _ _ _) hv hb (coverBudget_pos i)
    (by simpa using Nat.pow_le_pow_right (n := 2) (by decide) hk) hmq (by omega)
    (by simp only [bins, pow_add]) (actualFamily i ha) order vectors cap A S J b
    (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) ≤ 1)
    (actual_cover_gate i) hS hTemplate
    (by norm_num : (1 : ℝ) - 99 / 100 ≤ ((99 / 100) / 2) / 8)
    hH (hard_seed_exponent_domains i).1 (by positivity)
    (by simpa only [balanceOrder, Nat.cast_pow, Nat.cast_ofNat] using sampling_row_request i)
    (by norm_num : (0 : ℝ) ≤ 1 / 50) h1 h2
    (fun e _ _ => balanced_change_decidable (actual_product_balanced i hc ha (2 ^ e / 2)))
    (fun e _ he => (actual_packet_stopping i hc ha _ e (le_refl _) he).1)
    (fun e _ he => (actual_packet_stopping i hc ha _ e (le_refl _) he).2)
    (actual_packet_count_gate i _ (coverBudget_pos i))
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmass

abbrev labelCount (i : Input) :=
  PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)

abbrev RoutingRow (i : Input) (Y : Type) [Fintype Y] :=
  Fin (outerWidth i) × ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y

abbrev RoutingCol (i : Input) (nv nb : ℕ) :=
  Fin (outerWidth i) → ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)

def routingGame (i : Input) (ha : Accepted i) {Y : Type} [Fintype Y]
    (R : Fin i.rows → Y → Bool) (nv nb : ℕ) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i) :
    RoutingRow i Y → RoutingCol i nv nb → Bool :=
  interlaceFun (protectedMatrix R (firstExponent i) (bins i) (secondWidth i)
    (labelCount i) nv nb (bins_pos i) (actualFamily i ha) order vectors cap) (outerWidth i)

/-- The literal per-unit receiving coefficient of the paper. -/
def capacityCoefficient (i : Input) : ℚ :=
  128 * (1 / 184 : ℚ) * coverBudget i * (outerExponent i + 2) * bins i

theorem capacityCoefficient_nonneg (i : Input) : 0 ≤ capacityCoefficient i := by
  unfold capacityCoefficient
  positivity

open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.DenseFrontierConservation
open EthInapproximability.ParameterizedNP.DenseWeightedCount

/-- Every node in the COMPLETE actual stopping collection satisfies the
required receiving capacity.  No reference-row condition appears, and the
local `hpacket` premise is discharged by the physical extraction theorem.
The only communication hypotheses are the two first-matrix profiles. -/
theorem all_nodes_receiving_capacity
    (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
    (nv nb : ℕ) (hv : 0 < nv) (hb : 0 < nb)
    (hraw : 1000 * ((nv + nb) * i.rows) ≤ bins i * labelCount i)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)
    (P : Protocol (RoutingRow i Y) (RoutingCol i nv nb) Bool)
    (retained : Finset (RoutingRow i Y)) (S : Finset (RoutingCol i nv nb))
    (J : Finset (Fin (outerWidth i)))
    (hS : (retainedFraction i : ℚ) *
      (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^
        outerWidth i ≤ S.card)
    (h1 : i.cost + firstExponent i ≤ Dfamily
      (interlaceFun (fun γ r => firstMatrix R (firstExponent i) (bins i) r γ) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 5)))
    (h2 : i.cost + firstExponent i - 1 ≤ Dfamily
      (interlaceFun (fun γ r => firstMatrix R (firstExponent i) (bins i) r γ) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 10)))
    (hP : ∀ z ∈ retained, ∀ y ∈ S,
      P.eval z y = routingGame i ha R nv nb order vectors cap z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1)
    (p : List Bool) (hp : p ∈ ProtocolFrontier.nodes P (outerExponent i) retained) :
    GlobalCount.mass (Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y))
      (GlobalCount.received
        (retained.filter (fun z => z.2 ∈ diagonalRows (firstExponent i) (bins i) (secondWidth i)))
        Prod.fst (ProtocolFrontier.rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) J p) <
      2 * capacityCoefficient i * (stoppingCapacity (outerExponent i) p.length : ℚ) := by
  let r := outerExponent i
  let m := Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y)
  let G := diagonalRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)
  let dest := ProtocolFrontier.rowStop r (completeNoBob r P)
  let additional := retained.filter (fun z => z.2 ∈ G)
  let A := RoutedClosure.rowsAt retained dest p
  have hm : 0 < m := (ReceivingCapacity.diagonalRows_card_pos (Y := Y)
    (firstExponent i) (bins i) (secondWidth i) (secondWidth_pos i)).trans_le
      (Finset.card_le_univ G)
  have hC : 1 ≤ certificateCost i := by unfold certificateCost; omega
  have hcoeff : ReceivingCapacity.receivingCoefficient m G r (coverBudget i) (bins i) =
      capacityCoefficient i := ReceivingCapacity.receivingCoefficient_eq_paper
        (Y := Y) _ _ _ _ _ (secondWidth_pos i)
  have ht := template_proportion_of_raw_count (Fin i.rows) (bins i) (labelCount i) nv nb
    (bins_pos i) (by simpa only [Fintype.card_fin] using hraw)
  have hchild (k : ℕ) (hk : 1 ≤ k) (b : RoutingCol i nv nb → Bool)
      (hmass : capacityCoefficient i * (2 : ℚ) ^ k ≤
        GlobalCount.mass m (GlobalCount.received additional Prod.fst dest J p)) :
      ∃ bit : Bool, i.cost + firstExponent i + (binExponent i + k + secondExponent i) ≤
        D (subgame (routingGame i ha R nv nb order vectors cap) A (S.filter (fun y => b y = bit))) := by
    have hm' : ReceivingCapacity.receivingCoefficient m G r (coverBudget i) (bins i) *
        (2 ^ k : ℕ) ≤ GlobalCount.mass m (ReceivingCapacity.incomingRows A G J) := by
      rw [hcoeff]
      simpa only [A, additional, ReceivingCapacity.incomingRows_at_destination,
        Nat.cast_pow, Nat.cast_ofNat] using hmass
    have hcard := ReceivingCapacity.incoming_mass_to_card A G J hm hm'
    exact incoming_child_cost_parameters i hc ha R nv nb k hv hb hk order vectors cap
      A S J b hS ht h1 h2 (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcard)
  rcases ProtocolFrontier.node_stops P r retained hp with hfirst | hfinal
  · have hdepth := hfirst.2.2
    obtain ⟨b, lo, hi, hnode⟩ : ∃ b lo hi, descend (completeNoBob r P) p = .bNode b lo hi := by
      have hbnode := hfirst.2.1
      cases hn : descend (completeNoBob r P) p with
      | leaf z => simp [hn, IsBobNode] at hbnode
      | aNode a lo hi => simp [hn, IsBobNode] at hbnode
      | bNode b lo hi => exact ⟨b, lo, hi, rfl⟩
    have hcap := RoutedClosure.firstBob_receiving_bound P r (certificateCost i) m
      retained additional S (routingGame i ha R nv nb order vectors cap) hP hC hcost
      Prod.fst J p hp hdepth b lo hi hnode (capacityCoefficient i * (2 : ℚ) ^ (r - p.length)) ?_
    · apply hcap.trans_le
      change capacityCoefficient i * (2 : ℚ) ^ (r - p.length) ≤
        2 * capacityCoefficient i * (stoppingCapacity r p.length : ℚ)
      simp only [stoppingCapacity, Nat.cast_pow, Nat.cast_ofNat]
      nlinarith [mul_nonneg (capacityCoefficient_nonneg i)
        (show (0 : ℚ) ≤ 2 ^ (r - p.length) by positivity)]
    intro hmass
    obtain ⟨bit, hbit⟩ := hchild (r - p.length) (by omega) b hmass
    refine ⟨bit, ?_⟩
    unfold certificateCost
    have heq : i.cost + firstExponent i + secondExponent i + binExponent i + 1 +
        (r - p.length) - 1 = i.cost + firstExponent i + (binExponent i + (r - p.length) + secondExponent i) := by omega
    rw [heq]
    exact hbit
  · have hdepth := hfinal.2
    have hcap := RoutedClosure.terminal_receiving_bound P r (certificateCost i) m
      retained additional S (routingGame i ha R nv nb order vectors cap) hP hC hcost
      Prod.fst J p hp hdepth (capacityCoefficient i) ?_
    · have hdepth' : p.length = outerExponent i := hdepth
      simpa only [m, additional, G, r, stoppingCapacity, hdepth', Nat.sub_self,
        pow_zero, Nat.cast_one, mul_one] using hcap
    intro hmass
    obtain ⟨bit, hbit⟩ := hchild 1 (by decide) (fun _ => false)
      (by simpa only [pow_one, mul_comm] using hmass)
    have hparent := ReceivingCapacity.child_cost_le_parent
      (routingGame i ha R nv nb order vectors cap) A S (fun _ => false) bit
    have hbound := hbit.trans hparent
    simpa only [certificateCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

end EthInapproximability.CurrentPaper.ConcreteRouting
