import EthInapproximability.CurrentPaper.TerminalPhysicalSpecialization
import EthInapproximability.CurrentPaper.RoutedClosure
import EthInapproximability.CurrentPaper.ProtectedDefects

/-!
# Transfers between actual assigned terminal rectangles

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-transfer`,
using `lem:paper-terminal-two-stream`. The arriving additional rows, the
reference rows, and the common columns are the literal protocol inputs.
The two-stream lower bound is derived from primitive profiles and actual
joint projections, never passed as a terminal-hardness premise.
-/

noncomputable section
open scoped Classical BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace

namespace EthInapproximability.CurrentPaper.TerminalTransfer

open Construction JointTransfer TerminalOuterBound TerminalPhysicalSpecialization
open ParameterizedNP.WrapperProjectionCovers ParameterizedNP.TerminalStateRealization
open ParameterizedNP.RoutedCertificateConstruction

/-- Actual inputs from one group at one assigned terminal. -/
def slice {Z Node : Type*} [DecidableEq Z] [DecidableEq Node] {Q : ℕ}
    (A : Finset (Fin Q × Z)) (dest : Fin Q × Z → Node) (p : Node)
    (k : Fin Q) (group : Finset Z) : Finset Z :=
  group.filter fun z => (k, z) ∈ RoutedClosure.rowsAt A dest p

/-- Every transferred input has a distinct second component in the
destination's additional-input slice. No assignment injectivity is needed. -/
theorem transfer_card_le_slice {Z Node : Type*} [DecidableEq Z] [DecidableEq Node]
    {Q : ℕ} (A : Finset (Fin Q × Z)) (dest : Fin Q × Z → Node)
    (assigned : Fin Q → Node) (group : Finset Z) (j i : Fin Q) :
    (RoutedClosure.transferTo (A.filter fun z => z.2 ∈ group) Prod.fst dest assigned j i).card ≤
      (slice A dest (assigned i) j group).card := by
  classical
  let T := RoutedClosure.transferTo (A.filter fun z => z.2 ∈ group) Prod.fst dest assigned j i
  have hm : ∀ z ∈ T, z.1 = j ∧ z.2 ∈ slice A dest (assigned i) j group := by
    intro z hz
    obtain ⟨hz, hd⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, ho, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    refine ⟨ho, Finset.mem_filter.mpr ⟨hg, ?_⟩⟩
    have heq : (j, z.2) = z := by rw [← ho]
    rw [heq]
    exact Finset.mem_filter.mpr ⟨hz, hd⟩
  have hinj : Set.InjOn (fun z : Fin Q × Z => z.2) (T : Set (Fin Q × Z)) := by
    intro z hz z' hz' heq
    exact Prod.ext ((hm z hz).1.trans (hm z' hz').1.symm) heq
  calc
    T.card = (T.image Prod.snd).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact (hm w hw).2)

/-- Convert normalized transfer mass into the actual additional-group
fraction. The group normalization is stated as an exact cardinal identity. -/
theorem transfer_fraction_lt {Z Node : Type*} [DecidableEq Z] [DecidableEq Node]
    {Q : ℕ} (A : Finset (Fin Q × Z)) (dest : Fin Q × Z → Node)
    (assigned : Fin Q → Node) (group : Finset Z) (j i : Fin Q)
    (M : ℕ) (hM : 0 < M) (hgroup : 0 < group.card)
    (mu lambda eps : ℚ) (hnorm : (group.card : ℚ) = 2 * mu * M)
    (hexcess : 2 * mu * (lambda + eps) < GlobalCount.mass M
      (RoutedClosure.transferTo (A.filter fun z => z.2 ∈ group) Prod.fst dest assigned j i)) :
    (lambda : ℝ) + eps < (slice A dest (assigned i) j group).card / (group.card : ℝ) := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hg : (0 : ℝ) < group.card := by exact_mod_cast hgroup
  have hc : ((RoutedClosure.transferTo (A.filter fun z => z.2 ∈ group)
      Prod.fst dest assigned j i).card : ℚ) ≤ (slice A dest (assigned i) j group).card := by
    exact_mod_cast transfer_card_le_slice A dest assigned group j i
  have he := (lt_div_iff₀ hm).mp hexcess
  have he' : (lambda + eps) * (group.card : ℚ) <
      (slice A dest (assigned i) j group).card := by rw [hnorm]; nlinarith
  apply (lt_div_iff₀ hg).mpr
  exact_mod_cast he'

/-- The physical additional group has exactly one ninety-second of all
protected rows, hence twice the paper's `mu = 1/184`. -/
theorem diagonal_normalization {Y : Type*} [Fintype Y] (a s q : ℕ) :
    ((diagonalRows (Y := Y) a s q).card : ℚ) =
      2 * (1 / 184 : ℚ) * Fintype.card (ProtectedColumns a s q Y) := by
  have hc : (diagonalRows (Y := Y) a s q).card =
      q * Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y) := by
    rw [diagonalRows, Finset.card_image_of_injective _ (diagonalEmbedding a s q).injective]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [hc, ProtectedDefects.diagonal_group_card]
  push_cast
  ring

/-- Reset only the scalar additional-margin field of the primitive inputs.
The baseline `eps=0, delta=1` repeats `lambda_small` and contains no
two-stream hardness assertion. -/
theorem pairInputs_margin {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {q L H m ell : ℕ} (family : Fin L → Fin q → Y)
    {x ε eps delta : ℝ} (inputs : PairInputs f family H m ell x ε 0 1)
    (hmargin : (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x) + eps < delta) :
    PairInputs f family H m ell x ε eps delta :=
  ⟨inputs.qpos, inputs.width, inputs.cost, inputs.order, inputs.x_pos, inputs.row_scale,
    inputs.error_nonneg, inputs.error_small, inputs.first, inputs.half, inputs.balanced,
    inputs.stopping, inputs.seed, inputs.lambda_small, hmargin⟩

/-- The ordinary support quotient comes from the actual singleton
projection intersected with the actual physical template bin. -/
theorem ordinary_width_from_physical {X : Type*} [Fintype X] [Nonempty X]
    (s L nv nb Q r : ℕ) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (S : Finset (Fin Q → ProtectedRows s L nv nb X)) (i : Fin Q) (p : Fin s)
    {xT : ℝ}
    (hraw : (2 : ℝ) ^ (r + 1) * xT * (templateBin (X := X) s L nv nb p).card ≤
      (((S.image (fun y => y i)) ∩ templateBin s L nv nb p).card : ℝ)) :
    threshold L xT r ≤ (((ordinarySupport s L nv nb Q i S p).image
      (fun z => templateQuotient hL (z i))).card : ℝ) := by
  classical
  let B := (S.image (fun y => y i)) ∩ templateBin s L nv nb p
  have hB : B ⊆ templateBin s L nv nb p := Finset.inter_subset_right
  have hc := (template_regular (X := X) s L nv nb hL p).card_le_mul_image hB
  have heq : B.image (templateQuotient hL) =
      (ordinarySupport s L nv nb Q i S p).image (fun z => templateQuotient hL (z i)) := by
    ext ell
    constructor
    · intro hell
      obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hell
      obtain ⟨hzS, hzp⟩ := Finset.mem_inter.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzS
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hzp⟩, hzv⟩
    · intro hell
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hell
      obtain ⟨hyS, hyp⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨y i,
        Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y, hyS, rfl⟩, hyp⟩, hyv⟩
  rw [heq] at hc
  have hcR : (B.card : ℝ) ≤ (Fintype.card (TemplateLabels s L nv nb X) : ℝ) *
      ((ordinarySupport s L nv nb Q i S p).image (fun z => templateQuotient hL (z i))).card := by
    exact_mod_cast hc
  have hd : (0 : ℝ) < Fintype.card (TemplateLabels s L nv nb X) := by
    exact_mod_cast template_labels_pos (X := X) s L nv nb hs hL hv hb
  rw [template_bin_card] at hraw
  push_cast at hraw
  unfold threshold
  dsimp [B] at hcR
  nlinarith

/-- A dense singleton projection contains many physical symbols in each
template bin. Only the displayed scalar deletion budget is required. -/
theorem bin_count_from_singleton {C : Type*} [Fintype C] [DecidableEq C] {Q : ℕ}
    (S : Finset (Fin Q → C)) (i : Fin Q) (bin : Finset C) {eta tau : ℝ}
    (hdense : (1 - eta) * Fintype.card C ≤ ((S.image (fun y => y i)).card : ℝ))
    (hbudget : tau * bin.card ≤ (bin.card : ℝ) - eta * Fintype.card C) :
    tau * bin.card ≤ (((S.image (fun y => y i)) ∩ bin).card : ℝ) := by
  have hc := Finset.card_union_add_card_inter (S.image (fun y => y i)) bin
  have hu := Finset.card_le_univ ((S.image (fun y => y i)) ∪ bin)
  have hcR : (((S.image (fun y => y i)) ∪ bin).card : ℝ) +
      (((S.image (fun y => y i)) ∩ bin).card : ℝ) =
      ((S.image (fun y => y i)).card : ℝ) + bin.card := by exact_mod_cast hc
  have huR : (((S.image (fun y => y i)) ∪ bin).card : ℝ) ≤ Fintype.card C := by
    exact_mod_cast hu
  nlinarith

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The per-destination transfer bound for the literal protected matrix.
The only lower-bound premises are the original first- and second-level
one-copy profiles. All terminal geometry and the cost contradiction are
constructed from the actual retained inputs and original protocol. -/
theorem physical_terminal_transfer (base : X → Y → Bool)
    (a s q L nv nb Q H m ell D2 r depth M : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {x ε xT rho : ℝ}
    (inputs : PairInputs (Function.swap (firstMatrix base a s)) family H m ell x ε 0 1)
    (hsr : s = 2 ^ r) (hD2 : D2 + 1 = H + m + ell) (hD2pos : 2 ≤ D2)
    (hxT : 0 < xT) (hscale : (2 : ℝ) ^ (r + 1) * xT ≤ 1)
    (hsecond : D2 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix base a s q L family)) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 xT (3 / 5)))
    (hsecondHalf : D2 - 1 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix base a s q L family)) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 xT (3 / 10)))
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (P : Protocol (Fin Q × ProtectedColumns a s q Y)
      (Fin Q → ProtectedRows s L nv nb X) Bool)
    (hcomp : ∀ z ∈ A, ∀ y ∈ S, P.eval z y =
      interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q z y)
    (hcost : P.cost ≤ (D2 + r + 1) + depth - 1)
    (assigned : Fin Q → List Bool) (i j : Fin Q)
    (hp : assigned i ∈ ProtocolFrontier.nodes P depth A)
    (hdepth : (assigned i).length = depth)
    (mu lambda eps : ℚ) (hM : 0 < M)
    (hnorm : ((diagonalRows (Y := Y) a s q).card : ℚ) = 2 * mu * M)
    (hlambda : (lambda : ℝ) = (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x))
    (heps : (eps : ℝ) ≤ 1 / 5)
    (href : 1 - (eps : ℝ) ≤
      ((slice A (ProtocolFrontier.rowStop depth (completeNoBob depth P))
        (assigned i) i (referenceRows a s q)).card : ℝ) /
      (referenceRows (Y := Y) a s q).card)
    (hjoint : rho * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ 2 ≤
      ((jointPairs S i j).card : ℝ))
    (hmargin : (49 / 64 : ℝ) ≤
      (aMin rho (templateDensity (templateBin (X := X) s L nv nb)) -
        (2 : ℝ) ^ (r + 1) * xT) / (1 + ε) ^ 2)
    (hbins : ∀ p : Fin s,
      (2 : ℝ) ^ (r + 1) * xT * (templateBin (X := X) s L nv nb p).card ≤
        (((S.image (fun y => y i)) ∩ templateBin s L nv nb p).card : ℝ)) :
    GlobalCount.mass M (RoutedClosure.transferTo
      (A.filter fun z => z.2 ∈ diagonalRows a s q) Prod.fst
      (ProtocolFrontier.rowStop depth (completeNoBob depth P)) assigned j i) ≤
      2 * mu * (lambda + eps) := by
  classical
  letI : Nonempty (Fin (qOne a)) := Fin.pos_iff_nonempty.mp ha
  let dest := ProtocolFrontier.rowStop depth (completeNoBob depth P)
  let T := RoutedClosure.rowsAt A dest (assigned i)
  let Ao := slice A dest (assigned i) i (referenceRows a s q)
  let Af := slice A dest (assigned i) j (diagonalRows a s q)
  have hdiagPos : 0 < (diagonalRows (Y := Y) a s q).card := by
    letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp inputs.qpos
    letI : Nonempty (DiagonalLabels a s q Y) :=
      Fintype.card_pos_iff.mp (diagonal_labels_pos a s q inputs.qpos)
    apply Finset.card_pos.mpr
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  apply RoutedClosure.terminal_transfer_bound P depth (D2 + r + 1) M A
    (A.filter fun z => z.2 ∈ diagonalRows a s q) S
    (interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q)
    hcomp (by omega) hcost Prod.fst assigned j i hp hdepth mu lambda eps
  intro hexcess
  have hfrac : (lambda : ℝ) + eps < (Af.card : ℝ) / (diagonalRows a s q).card :=
    transfer_fraction_lt A dest assigned (diagonalRows a s q) j i M hM hdiagPos
      mu lambda eps hnorm hexcess
  have actualInputs : PairInputs (Function.swap (firstMatrix base a s)) family
      H m ell x ε (eps : ℝ) ((Af.card : ℝ) / (diagonalRows a s q).card) :=
    pairInputs_margin _ family inputs (by simpa only [hlambda] using hfrac)
  have hlabels := template_labels_pos (X := X) s L nv nb hs hL hv hb
  have hmBin : 0 < L * Fintype.card (TemplateLabels s L nv nb X) := Nat.mul_pos hL hlabels
  have hCarrier : 0 < Fintype.card (ProtectedRows s L nv nb X) := by
    have hbin := template_bin_card (X := X) s L nv nb ⟨0, hs⟩
    have hle := Finset.card_le_univ (templateBin (X := X) s L nv nb ⟨0, hs⟩)
    rw [hbin] at hle
    omega
  obtain ⟨po, pf, sigma, hdensity, hsigma⟩ := select_joint_pairs S i j
    (templateBin (X := X) s L nv nb) hs hmBin hCarrier
    (template_bins_disjoint s L nv nb) (template_bin_card s L nv nb) hjoint
  let pairs := jointPairs S i j ∩
    (templateBin (X := X) s L nv nb po ×ˢ templateBin s L nv nb pf)
  have hpairs : pairs ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf :=
    Finset.inter_subset_right
  have hsurplus := physical_pair_surplus s L nv nb r hs hL hv hb po pf pairs hpairs
    hdensity inputs.error_nonneg hmargin
  exact physical_outer_subgame_lower base a s q L nv nb Q H m ell D2 r
    ha hs hL family order vectors cap actualInputs hsr hD2 hD2pos hxT heps hscale
    hsecond hsecondHalf i j po pf T S Ao Af
    (by intro z hz; exact (Finset.mem_filter.mp hz).2)
    (by intro z hz; exact (Finset.mem_filter.mp hz).2)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) href (le_refl _)
    pairs hpairs sigma hsigma hsurplus
    (fun p _ => ordinary_width_from_physical s L nv nb Q r hs hL hv hb S i p (hbins p))

end EthInapproximability.CurrentPaper.TerminalTransfer
