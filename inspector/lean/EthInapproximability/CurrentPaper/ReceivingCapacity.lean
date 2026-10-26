import EthInapproximability.CurrentPaper.EarlyProtectedClosure
import EthInapproximability.CurrentPaper.DensityBucket
import EthInapproximability.CurrentPaper.RoutedClosure
import EthInapproximability.CurrentPaper.ReceivingCapacitySelection
import EthInapproximability.CurrentPaper.ReceivingCapacityTemplate
import EthInapproximability.CurrentPaper.ReceivingCapacityNumerics

/-!
# Incoming additional rows at actual stopping rectangles

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-early-protected-closure` and `clm:paper-global-capacity`.

Donor densities are computed from actual retained physical rows. Their sum
is proved equal to the incoming row count divided by the size of one
diagonal reservoir. Later selection and communication bounds retain the
same actual outer column set.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ReceivingCapacity

open Construction JointTransfer

section DonorMass

variable {Z : Type*} [DecidableEq Z] {Q : ℕ}

/-- Physical additional rows of coordinate `j` retained at this rectangle. -/
def donorRows (A : Finset (Fin Q × Z)) (G : Finset Z) (j : Fin Q) : Finset Z :=
  G.filter fun z => (j, z) ∈ A

/-- All actual additional rows received from a specified set of donors. -/
def incomingRows (A : Finset (Fin Q × Z)) (G : Finset Z)
    (J : Finset (Fin Q)) : Finset (Fin Q × Z) :=
  A.filter fun r => r.1 ∈ J ∧ r.2 ∈ G

theorem donorRows_subset (A : Finset (Fin Q × Z)) (G : Finset Z) (j : Fin Q) :
    donorRows A G j ⊆ G := Finset.filter_subset _ _

theorem incomingRows_card (A : Finset (Fin Q × Z)) (G : Finset Z)
    (J : Finset (Fin Q)) :
    (incomingRows A G J).card = ∑ j ∈ J, (donorRows A G j).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := incomingRows A G J) (t := J) (f := Prod.fst)
    (fun r hr => (Finset.mem_filter.mp hr).2.1)
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (incomingRows A G J).filter (fun r => r.1 = j) =
      ({j} : Finset (Fin Q)) ×ˢ donorRows A G j := by
    ext ⟨i, z⟩
    simp only [incomingRows, donorRows, Finset.mem_filter, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hr, _, hg⟩, he⟩
      exact ⟨he, hg, by simpa only [he] using hr⟩
    · rintro ⟨he, hg, hr⟩
      exact ⟨⟨by simpa only [he] using hr, by simpa only [he] using hj, hg⟩, he⟩
  rw [heq, Finset.card_product, Finset.card_singleton, one_mul]

def donorDensity (A : Finset (Fin Q × Z)) (G : Finset Z) (j : Fin Q) : ℝ :=
  ((donorRows A G j).card : ℝ) / G.card

theorem donorDensity_nonneg (A : Finset (Fin Q × Z)) (G : Finset Z) (j : Fin Q) :
    0 ≤ donorDensity A G j := by unfold donorDensity; positivity

theorem donorDensity_le_one (A : Finset (Fin Q × Z)) (G : Finset Z) (j : Fin Q) :
    donorDensity A G j ≤ 1 := by
  unfold donorDensity
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card (donorRows_subset A G j))
    (by positivity)

/-- The normalization is an identity on the actual incoming finite set. -/
theorem sum_donorDensity (A : Finset (Fin Q × Z)) (G : Finset Z)
    (J : Finset (Fin Q)) :
    ∑ j ∈ J, donorDensity A G j = ((incomingRows A G J).card : ℝ) / G.card := by
  simp only [donorDensity, ← Finset.sum_div, ← Nat.cast_sum, ← incomingRows_card]

/-- A cardinal incoming-mass bound produces the paper's dyadic donor class. -/
theorem density_selection_of_incoming {r B s κ : ℕ}
    (A : Finset (Fin (2 ^ r) × Z)) (G : Finset Z) (J : Finset (Fin (2 ^ r)))
    (hG : 0 < G.card) (hB : 1 ≤ B) (hs : 1 ≤ s) (hκ : 2 ≤ κ)
    (hmass : 64 * (B : ℝ) * (r + 2 : ℕ) * s * κ * G.card ≤
      (incomingRows A G J).card) :
    Nonempty (DensityBucket.Selection J (donorDensity A G) B s κ) := by
  apply DensityBucket.exists_selection J (donorDensity A G) hB hs hκ
    (fun j _ => donorDensity_nonneg A G j) (fun j _ => donorDensity_le_one A G j)
  rw [sum_donorDensity]
  exact (le_div_iff₀ (by exact_mod_cast hG : (0 : ℝ) < G.card)).mpr hmass

/-- The incoming set is the literal received set for a stopping destination. -/
theorem incomingRows_at_destination {Node : Type*} [DecidableEq Node]
    (retained : Finset (Fin Q × Z)) (G : Finset Z)
    (J : Finset (Fin Q)) (destination : Fin Q × Z → Node) (p : Node) :
    incomingRows (RoutedClosure.rowsAt retained destination p) G J =
      GlobalCount.received (retained.filter fun r => r.2 ∈ G) Prod.fst
        destination J p := by
  ext r
  simp only [incomingRows, RoutedClosure.rowsAt, GlobalCount.received, Finset.mem_filter]
  tauto

/-- Capacity in units of the actual ambient row count. -/
def receivingCoefficient (m : ℕ) (G : Finset Z) (r B s : ℕ) : ℚ :=
  64 * B * (r + 2) * s * G.card / m

theorem incoming_mass_to_card (A : Finset (Fin Q × Z)) (G : Finset Z)
    (J : Finset (Fin Q)) {m r B s κ : ℕ} (hm : 0 < m)
    (hmass : receivingCoefficient m G r B s * κ ≤
      GlobalCount.mass m (incomingRows A G J)) :
    64 * (B : ℝ) * (r + 2 : ℕ) * s * κ * G.card ≤
      (incomingRows A G J).card := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hc : (64 * (B : ℚ) * (r + 2 : ℕ) * s * κ * G.card) / m ≤
      (incomingRows A G J).card / (m : ℚ) := by
    convert hmass using 1
    simp only [receivingCoefficient, Nat.cast_add, Nat.cast_ofNat]
    ring
  have hh := (div_le_div_iff_of_pos_right hmQ).mp hc
  exact_mod_cast hh

end DonorMass

section PhysicalCounts

universe u
variable {Y : Type u} [Fintype Y] [Nonempty Y]

theorem diagonalRows_card_pos (a s q : ℕ) (hq : 0 < q) :
    0 < (diagonalRows (Y := Y) a s q).card := by
  have hlabels := diagonal_labels_pos (Y := Y) a s q hq
  letI := secondRows_nonempty (Y := Y) a s q hq
  rw [diagonalRows, Finset.card_image_of_injective _ (diagonalEmbedding a s q).injective,
    Finset.card_univ, Fintype.card_prod]
  exact Nat.mul_pos Fintype.card_pos hlabels

/-- The current construction has exactly one additional reservoir of mass
`1/92 = 2*mu`, including its uniform duplication labels. -/
theorem diagonalRows_mass (a s q : ℕ) (hq : 0 < q) :
    ((diagonalRows (Y := Y) a s q).card : ℚ) /
      Fintype.card (ProtectedColumns a s q Y) = 1 / 92 := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  have h := WeightedDuplication.column_group_mass (RawColumns a s q Y)
    (SecondRows a s q Y) (uniformCopies (Y := Y) a s q)
    (uniformCopies_pos (Y := Y) a s q hq) 1
  norm_num only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  have hc : (diagonalRows (Y := Y) a s q).card =
      Fintype.card (WeightedDuplication.Group
        (WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y))
        WeightedDuplication.columnWeight 1 × Fin (uniformCopies (Y := Y) a s q)) := by
    rw [diagonalRows, Finset.card_image_of_injective _ (diagonalEmbedding a s q).injective,
      Finset.card_univ]
    change Fintype.card (SecondRows a s q Y ×
        (Fin (diagonalMultiplicity (Y := Y) a s q) × Fin (uniformCopies (Y := Y) a s q))) =
      Fintype.card ((SecondRows a s q Y × Fin (diagonalMultiplicity (Y := Y) a s q)) ×
        Fin (uniformCopies (Y := Y) a s q))
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hc]
  exact h

theorem receivingCoefficient_eq_paper (a s q r B : ℕ) (hq : 0 < q) :
    receivingCoefficient (Fintype.card (ProtectedColumns a s q Y))
      (diagonalRows (Y := Y) a s q) r B s =
      128 * (1 / 184 : ℚ) * B * (r + 2) * s := by
  unfold receivingCoefficient
  have h := diagonalRows_mass (Y := Y) a s q hq
  calc
    _ = (64 * B * (r + 2) * s) *
        (((diagonalRows (Y := Y) a s q).card : ℚ) /
          Fintype.card (ProtectedColumns a s q Y)) := by ring
    _ = _ := by rw [h]; ring

end PhysicalCounts

section Extraction

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- Actual finite witnesses extracted from incoming rows and an original Bob
child. Every field describes the selected sets or a scalar density; none is
a communication-complexity bound. This structure is produced below, not
assumed as the missing receiving-capacity conclusion. -/
structure ExtractedPacket (a s q L nv nb r B κ : ℕ)
    (A : Finset (Fin (2 ^ r) × ProtectedColumns a s q Y))
    (S : Finset (Fin (2 ^ r) → ProtectedRows s L nv nb X))
    (donors : Finset (Fin (2 ^ r)))
    (b : (Fin (2 ^ r) → ProtectedRows s L nv nb X) → Bool) (rho : ℝ) where
  selection : DensityBucket.Selection donors
    (donorDensity A (diagonalRows a s q)) B s κ
  bit : Bool
  coords : Fin (2 ^ selection.widthExponent / 2) → Fin (2 ^ r)
  bins : Fin (2 ^ selection.widthExponent / 2) → Fin s
  columns : Finset (Fin (2 ^ selection.widthExponent / 2) → ProtectedRows s L nv nb X)
  completion : (Fin (2 ^ selection.widthExponent / 2) → ProtectedRows s L nv nb X) →
    Fin (2 ^ r) → ProtectedRows s L nv nb X
  coordinates_injective : Function.Injective coords
  row_density : ∀ j, (1 / (2 : ℝ) ^ selection.classExponent) / 2 ≤
    donorDensity A (diagonalRows a s q) (coords j)
  column_density : ((rho / 2) / 2 ^ (2 ^ selection.widthExponent + 1)) *
    ((Fintype.piFinset (fun j => templateBin (X := X) s L nv nb (bins j))).card : ℝ) ≤
      columns.card
  columns_in_bins : ∀ t ∈ columns, ∀ j, t j ∈ templateBin s L nv nb (bins j)
  completion_mem : ∀ t ∈ columns, completion t ∈ S.filter (fun y => b y = bit) ∧
    ∀ j, completion t (coords j) = t j

/-- High actual incoming mass yields a physical packet in an actual Bob
child. The projections of different Bob children may overlap; their original
column sets, queries and all common completions are retained literally. -/
theorem extract_packet_of_incoming [Nonempty X] [Nonempty Y]
    (a s q L nv nb r B κ : ℕ) (hs : 0 < s) (hq : 0 < q) (hL : 0 < L)
    (hv : 0 < nv) (hb : 0 < nb) (hB : 1 ≤ B) (hκ : 2 ≤ κ)
    (A : Finset (Fin (2 ^ r) × ProtectedColumns a s q Y))
    (S : Finset (Fin (2 ^ r) → ProtectedRows s L nv nb X))
    (donors : Finset (Fin (2 ^ r)))
    (b : (Fin (2 ^ r) → ProtectedRows s L nv nb X) → Bool)
    {rho theta lam : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hcover : rho ^ B < theta)
    (hS : theta * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ (2 ^ r) ≤ S.card)
    (hTemplate : lam * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
      ((ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card : ℝ))
    (hgap : 1 - lam ≤ (rho / 2) / 8)
    (hmass : 64 * (B : ℝ) * (r + 2 : ℕ) * s * κ *
      (diagonalRows (Y := Y) a s q).card ≤
      (incomingRows A (diagonalRows a s q) donors).card) :
    Nonempty (ExtractedPacket a s q L nv nb r B κ A S donors b rho) := by
  classical
  obtain ⟨sel⟩ := density_selection_of_incoming A (diagonalRows a s q) donors
    (diagonalRows_card_pos a s q hq) hB hs hκ hmass
  have hC : 0 < Fintype.card (ProtectedRows s L nv nb X) := by
    have hc := Finset.card_le_univ (templateBin (X := X) s L nv nb ⟨0, hs⟩)
    rw [template_bin_card] at hc
    exact (Nat.mul_pos hL (template_labels_pos s L nv nb hs hL hv hb)).trans_le hc
  obtain ⟨J, bit, hJ, hJcard, hd, _, hchild⟩ :=
    ReceivingCapacitySelection.dense_bob_child_of_selection sel S b hC hB
      hrho hrho1 hcover hS
  let e : Fin (2 ^ sel.widthExponent) ≃ ↥J :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hJcard)).symm
  let S' := S.filter (fun y => b y = bit)
  let project : (Fin (2 ^ r) → ProtectedRows s L nv nb X) →
      Fin (2 ^ sel.widthExponent) → ProtectedRows s L nv nb X := fun y i => y (e i).val
  let P := ReceivingCapacitySelection.reindexedProjection J e S'
  have hP : (rho / 2) * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^
      (2 ^ sel.widthExponent) ≤ P.card := by
    simpa only [P, ReceivingCapacitySelection.reindexedProjection_card] using hchild
  obtain ⟨coords, bins, T, sigma, hinj, hT, hbins, hsigma⟩ :=
    ReceivingCapacityTemplate.physical_template_half_bin_extraction_fin
      hs P sel.four_dvd_width (by positivity) hC (by positivity) hP hTemplate hgap
  letI : Nonempty (ProtectedRows s L nv nb X) := Fintype.card_pos_iff.mp hC
  let pick := ParameterizedNP.TerminalStateRealization.imageSection
    (inferInstance : Nonempty (Fin (2 ^ r) → ProtectedRows s L nv nb X)) S' project
  let outerCoords : Fin (2 ^ sel.widthExponent / 2) → Fin (2 ^ r) :=
    fun i => (e (coords i)).val
  let completion := fun t => pick (sigma t)
  refine ⟨{
    selection := sel
    bit := bit
    coords := outerCoords
    bins := bins
    columns := T
    completion := completion
    coordinates_injective := ?_
    row_density := ?_
    column_density := ?_
    columns_in_bins := hbins
    completion_mem := ?_ }⟩
  · intro i j hij
    apply hinj
    apply e.injective
    exact Subtype.ext hij
  · intro j
    exact (hd (e (coords j)).val (e (coords j)).property).1.le
  · have hcard : (Fintype.piFinset
        (fun j => templateBin (X := X) s L nv nb (bins j))).card =
        (L * Fintype.card (TemplateLabels s L nv nb X)) ^ (2 ^ sel.widthExponent / 2) := by
      simp only [Fintype.card_piFinset, template_bin_card, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    simpa only [hcard, Nat.cast_pow, Nat.cast_mul] using hT
  · intro t ht
    have hmem : sigma t ∈ S'.image project := (hsigma t ht).1
    refine ⟨ParameterizedNP.TerminalStateRealization.imageSection_mem hmem, ?_⟩
    intro j
    have heq := ParameterizedNP.TerminalStateRealization.imageSection_apply
      (hA := (inferInstance : Nonempty (Fin (2 ^ r) → ProtectedRows s L nv nb X))) hmem
    exact (congrFun heq (coords j)).trans ((hsigma t ht).2 j)

end Extraction

section Communication

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace

/-- The communication conclusion of early protected closure, obtained from
actual incoming rows. The only remaining analytic inputs are the first
matrix's two restriction bounds, product balance and scalar stopping gates.
No lower bound for the packet or receiving rectangle is a hypothesis. -/
theorem incoming_child_cost
    (R : X → Y → Bool) (a s L nv nb r B κ qexp kexp H m : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (hB : 1 ≤ B) (hκ : 2 ≤ κ) (hmq : m ≤ qexp) (hmk : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp)
    (family : SecondFamily a (2 ^ qexp) L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (2 ^ qexp) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y))
    (S : Finset (Fin (2 ^ r) → ProtectedRows s L nv nb X))
    (donors : Finset (Fin (2 ^ r)))
    (b : (Fin (2 ^ r) → ProtectedRows s L nv nb X) → Bool)
    {rho theta lam x ε : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hcover : rho ^ B < theta)
    (hS : theta * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ (2 ^ r) ≤ S.card)
    (hTemplate : lam * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
      ((ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card : ℝ))
    (hgap : 1 - lam ≤ (rho / 2) / 8)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε)
    (h1 : H ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 10)))
    (hbalanced : ∀ e, 4 ≤ e → e ≤ r → IsBalancedFamily (2 ^ m)
      (ProductBalancedness.productFamily (2 ^ e / 2) family) ε)
    (hgateOne : ∀ e, 4 ≤ e → e ≤ r → (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m)
      ((rho / 2) / 2 ^ (2 ^ e + 1)) (H + ((e - 1 + qexp - m) + m)))
    (hgateSeed : ∀ e, 4 ≤ e → e ≤ r → HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      ((rho / 2) / 2 ^ (2 ^ e + 1)) *
        (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hcountGate : (2 : ℝ) ^ r * (2 : ℝ) ^ qexp * x ≤ 8 * (B : ℝ) * (r + 2 : ℕ))
    (hmass : 64 * (B : ℝ) * (r + 2 : ℕ) * s * κ *
      (diagonalRows (Y := Y) a s (2 ^ qexp)).card ≤
      (incomingRows A (diagonalRows a s (2 ^ qexp)) donors).card) :
    ∃ bit : Bool, H + kexp ≤ D (subgame
      (interlaceFun (protectedMatrix R a s (2 ^ qexp) L nv nb hs family order vectors cap)
        (2 ^ r)) A (S.filter (fun y => b y = bit))) := by
  obtain ⟨packet⟩ := extract_packet_of_incoming a s (2 ^ qexp) L nv nb r B κ
    hs (by positivity) hL hv hb hB hκ A S donors b hrho hrho1 hcover hS hTemplate hgap hmass
  have he4 := packet.selection.exponent_ge_four
  have her : packet.selection.widthExponent ≤ r :=
    (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp packet.selection.width_le_ambient
  obtain ⟨hwidth, he, hcount, hthreshold⟩ :=
    ReceivingCapacityNumerics.packet_stopping_numerics packet.selection hmq hmk hK hcountGate
  let rows := fun j => donorRows A (diagonalRows a s (2 ^ qexp)) (packet.coords j)
  have hlower := EarlyProtectedClosure.physical_packet_lower_bound
    (X := X) (Y := Y) R a s (2 ^ qexp) L nv nb (2 ^ r)
    (2 ^ packet.selection.widthExponent / 2)
    ha hs (by positivity) hL hv hb family order vectors cap packet.coords packet.bins
    A (S.filter (fun y => b y = packet.bit)) rows
    (fun j z hz => (Finset.mem_filter.mp hz).2)
    (fun j => donorRows_subset A _ (packet.coords j))
    packet.columns packet.columns_in_bins packet.completion packet.completion_mem
    (H := H) (m := m) (R₀ := packet.selection.widthExponent - 1 + qexp - m)
    (R' := kexp - m) (x := x)
    (d := (1 / (2 : ℝ) ^ packet.selection.classExponent) / 2)
    (h := (rho / 2) / 2 ^ (2 ^ packet.selection.widthExponent + 1)) (ε := ε)
    hwidth hH hm hx hrow hε (by positivity) h1 h2
    (hbalanced _ he4 her) (hgateOne _ he4 her) (hgateSeed _ he4 her) he (by positivity)
    (fun j => packet.row_density j)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcount) hthreshold packet.column_density
  exact ⟨packet.bit, by simpa only [Nat.sub_add_cancel hmk] using hlower⟩

/-- Restricting a child to one actual Bob bit cannot increase the complexity
above that of the same parent rectangle. -/
theorem child_cost_le_parent {U V : Type*} (F : U → V → Bool)
    (A : Finset U) (S : Finset V) (b : V → Bool) (bit : Bool) :
    D (subgame F A (S.filter (fun y => b y = bit))) ≤ D (subgame F A S) := by
  let colMap : {y // y ∈ S.filter (fun y => b y = bit)} → {y // y ∈ S} :=
    fun y => ⟨y.val, (Finset.mem_filter.mp y.property).1⟩
  exact D_mapNodes_le (subgame F A S) id colMap

section CapacityBounds

open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.DenseFrontierConservation
open EthInapproximability.ParameterizedNP.DenseWeightedCount

variable
    (R : X → Y → Bool) (a s L nv nb r B κ qexp kexp H m : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (hB : 1 ≤ B) (hκ : 2 ≤ κ) (hmq : m ≤ qexp) (hmk : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp)
    (family : SecondFamily a (2 ^ qexp) L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (2 ^ qexp) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (S : Finset (Fin (2 ^ r) → ProtectedRows s L nv nb X))
    (donors : Finset (Fin (2 ^ r)))
    {rho theta lam x ε : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hcover : rho ^ B < theta)
    (hS : theta * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ (2 ^ r) ≤ S.card)
    (hTemplate : lam * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
      ((ReceivingCapacityTemplate.fullTemplate (X := X) s L nv nb).card : ℝ))
    (hgap : 1 - lam ≤ (rho / 2) / 8)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε)
    (h1 : H ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 10)))
    (hbalanced : ∀ e, 4 ≤ e → e ≤ r → IsBalancedFamily (2 ^ m)
      (ProductBalancedness.productFamily (2 ^ e / 2) family) ε)
    (hgateOne : ∀ e, 4 ≤ e → e ≤ r → (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m)
      ((rho / 2) / 2 ^ (2 ^ e + 1)) (H + ((e - 1 + qexp - m) + m)))
    (hgateSeed : ∀ e, 4 ≤ e → e ≤ r → HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      ((rho / 2) / 2 ^ (2 ^ e + 1)) *
        (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hcountGate : (2 : ℝ) ^ r * (2 : ℝ) ^ qexp * x ≤ 8 * (B : ℝ) * (r + 2 : ℕ))

include ha hs hL hv hb hB hκ hmq hmk hK hrho hrho1 hcover hS hTemplate hgap
  hH hm hx hrow hε h1 h2 hbalanced hgateOne hgateSeed hcountGate

/-- Actual first-Bob receiving capacity. The `hpacket` premise of
`RoutedClosure.firstBob_receiving_bound` is proved from incoming finite rows,
the actual Bob query and the displayed analytic inputs. -/
theorem firstBob_receiving_capacity
    (P : Protocol (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y)
      (Fin (2 ^ r) → ProtectedRows s L nv nb X) Bool)
    (retained : Finset (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y))
    (C : ℕ)
    (hP : ∀ z ∈ retained, ∀ y ∈ S, P.eval z y =
      interlaceFun (protectedMatrix R a s (2 ^ qexp) L nv nb hs family order vectors cap)
        (2 ^ r) z y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1) (p : List Bool)
    (hp : p ∈ ProtocolFrontier.nodes P r retained) (hdepth : p.length < r)
    (b : (Fin (2 ^ r) → ProtectedRows s L nv nb X) → Bool)
    (lo hi : Protocol (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y)
      (Fin (2 ^ r) → ProtectedRows s L nv nb X) Bool)
    (hnode : descend (completeNoBob r P) p = .bNode b lo hi)
    (htarget : C + (r - p.length) - 1 ≤ H + kexp) :
    GlobalCount.mass (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
      (GlobalCount.received
        (retained.filter (fun z => z.2 ∈ diagonalRows a s (2 ^ qexp))) Prod.fst
        (ProtocolFrontier.rowStop r (completeNoBob r P)) donors p) <
      receivingCoefficient (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
        (diagonalRows (Y := Y) a s (2 ^ qexp)) r B s * κ := by
  apply RoutedClosure.firstBob_receiving_bound P r C _ retained _ S _
    hP hC hcost Prod.fst donors p hp hdepth b lo hi hnode
  intro hmass
  let A := RoutedClosure.rowsAt retained
    (ProtocolFrontier.rowStop r (completeNoBob r P)) p
  have hM : 0 < Fintype.card (ProtectedColumns a s (2 ^ qexp) Y) :=
    (diagonalRows_card_pos a s (2 ^ qexp) (by positivity)).trans_le
      (Finset.card_le_univ (diagonalRows (Y := Y) a s (2 ^ qexp)))
  have hmass' : receivingCoefficient (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
      (diagonalRows (Y := Y) a s (2 ^ qexp)) r B s * κ ≤
      GlobalCount.mass (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
        (incomingRows A (diagonalRows a s (2 ^ qexp)) donors) := by
    simpa only [A, incomingRows_at_destination] using hmass
  have hcard := incoming_mass_to_card A (diagonalRows a s (2 ^ qexp)) donors hM hmass'
  obtain ⟨bit, hlower⟩ := incoming_child_cost R a s L nv nb r B κ qexp kexp H m
    ha hs hL hv hb hB hκ hmq hmk hK family order vectors cap A S donors b
    hrho hrho1 hcover hS hTemplate hgap hH hm hx hrow hε h1 h2
    hbalanced hgateOne hgateSeed hcountGate hcard
  exact ⟨bit, htarget.trans hlower⟩

/-- Actual terminal receiving capacity, with no reference-row condition.
At the paper's formal value `kappa=2`, the threshold is `2*Fcap`.
The auxiliary constant Bob query merely selects a restriction of the same
terminal rectangle and does not remove a real message from its protocol. -/
theorem terminal_receiving_capacity
    (P : Protocol (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y)
      (Fin (2 ^ r) → ProtectedRows s L nv nb X) Bool)
    (retained : Finset (Fin (2 ^ r) × ProtectedColumns a s (2 ^ qexp) Y))
    (C : ℕ)
    (hP : ∀ z ∈ retained, ∀ y ∈ S, P.eval z y =
      interlaceFun (protectedMatrix R a s (2 ^ qexp) L nv nb hs family order vectors cap)
        (2 ^ r) z y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1) (p : List Bool)
    (hp : p ∈ ProtocolFrontier.nodes P r retained) (hdepth : p.length = r)
    (htarget : C ≤ H + kexp) :
    GlobalCount.mass (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
      (GlobalCount.received
        (retained.filter (fun z => z.2 ∈ diagonalRows a s (2 ^ qexp))) Prod.fst
        (ProtocolFrontier.rowStop r (completeNoBob r P)) donors p) <
      receivingCoefficient (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
        (diagonalRows (Y := Y) a s (2 ^ qexp)) r B s * κ := by
  let A := RoutedClosure.rowsAt retained
    (ProtocolFrontier.rowStop r (completeNoBob r P)) p
  let coefficient := receivingCoefficient (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
    (diagonalRows (Y := Y) a s (2 ^ qexp)) r B s
  have hcap := RoutedClosure.terminal_receiving_bound P r C
    (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y)) retained
    (retained.filter (fun z => z.2 ∈ diagonalRows a s (2 ^ qexp))) S _
    hP hC hcost Prod.fst donors p hp hdepth (coefficient * κ / 2) ?_
  · rw [show (2 : ℚ) * (coefficient * κ / 2) = coefficient * κ by ring] at hcap
    exact hcap
  intro hmass
  have hM : 0 < Fintype.card (ProtectedColumns a s (2 ^ qexp) Y) :=
    (diagonalRows_card_pos a s (2 ^ qexp) (by positivity)).trans_le
      (Finset.card_le_univ (diagonalRows (Y := Y) a s (2 ^ qexp)))
  have hmass' : coefficient * κ ≤
      GlobalCount.mass (Fintype.card (ProtectedColumns a s (2 ^ qexp) Y))
        (incomingRows A (diagonalRows a s (2 ^ qexp)) donors) := by
    rw [show (2 : ℚ) * (coefficient * κ / 2) = coefficient * κ by ring] at hmass
    simpa only [A, incomingRows_at_destination] using hmass
  have hcard := incoming_mass_to_card A (diagonalRows a s (2 ^ qexp)) donors hM hmass'
  obtain ⟨bit, hlower⟩ := incoming_child_cost R a s L nv nb r B κ qexp kexp H m
    ha hs hL hv hb hB hκ hmq hmk hK family order vectors cap A S donors (fun _ => false)
    hrho hrho1 hcover hS hTemplate hgap hH hm hx hrow hε h1 h2
    hbalanced hgateOne hgateSeed hcountGate hcard
  exact htarget.trans (hlower.trans (child_cost_le_parent _ A S (fun _ => false) bit))

end CapacityBounds

end Communication

end EthInapproximability.CurrentPaper.ReceivingCapacity
