import EthInapproximability.CurrentPaper.ReferenceAssignment
import EthInapproximability.CurrentPaper.Foundations
import EthInapproximability.CurrentPaper.AlignedProtectedProfiles
import EthInapproximability.CurrentPaper.ProductExtraction
import EthInapproximability.CurrentPaper.RoutedClosure

/-!
# Reference exclusions at actual stopping nodes

Source: locked v8 `A-stage4-details.tex`, the proof of
`clm:paper-global-assignment`. The reference matrix is a literal embedded
row submatrix of the ambient matrix. Supports follow the actual protocol's
Alice predicates, and column projections retain actual common tuples.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteReferenceExclusions

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol
open AlignedProtectedProfiles ProtocolFrontier ReferenceAssignment
open EthInapproximability.ParameterizedNP
open DenseWeightedCount DenseSynchronisation DenseWrapperFrontier
open RoutedCertificateSystem RoutingDynamics FrontierIndexing RoutedCertificateConstruction

variable {X Y Ref : Type*} {Coord : Type} [Fintype X] [Fintype Y] [Fintype Ref]
  [Fintype Coord] [DecidableEq X] [DecidableEq Y] [DecidableEq Ref] [DecidableEq Coord]
  {q : ℕ}

/-- Initially retained reference rows at one original outer coordinate. -/
def referenceSupport (e : Ref ↪ X) (retained : Finset (Fin q × X))
    (j : Fin q) : Finset (Fin q × X) :=
  retained.filter fun z => z.1 = j ∧ ∃ x, e x = z.2

theorem referenceSupport_subset (e : Ref ↪ X) (retained : Finset (Fin q × X))
    (j : Fin q) : referenceSupport e retained j ⊆ retained := Finset.filter_subset _ _

/-- The actual original coordinates represented at this address. -/
def represented (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (R : Coord → Finset (Fin q × X)) (loc : Coord ↪ Fin q)
    (A0 r : ℕ) (p : List Bool) : Finset (Fin q) :=
  (Finset.univ.filter fun i => p ∈ coordRoutes P R A0 r i).image loc

theorem weight_le_represented (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (R : Coord → Finset (Fin q × X)) (loc : Coord ↪ Fin q)
    (A0 r : ℕ) (p : List Bool) :
    weightAt P R A0 r p ≤ (represented P R loc A0 r p).card := by
  unfold weightAt represented
  rw [Finset.card_image_of_injective _ loc.injective, ← Finset.sum_filter]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => p ∈ coordRoutes P R A0 r i), (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => CertKind.weight_le_one _
    _ = _ := by simp

/-- Routed supports supply genuine row fibres of the actual stopping
rectangle. The initial support floor is not replaced by a density oracle. -/
theorem routed_reference_floor
    (e : Ref ↪ X) (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (retained : Finset (Fin q × X)) (loc : Coord ↪ Fin q)
    (A0 r : ℕ) (p : List Bool) (i : Coord)
    (hR : refRowFloor A0 r ≤ (referenceSupport e retained (loc i)).card)
    (hp : p ∈ coordRoutes (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) A0 r i) :
    refRowFloor A0 (r - p.length) ≤
      ((referencePullback e (RoutedClosure.rowsAt retained
        (rowStop r (completeNoBob r P)) p)).filter (fun z => z.1 = loc i)).card := by
  let R := referenceSupport e retained (loc i)
  let A := RoutedClosure.rowsAt retained (rowStop r (completeNoBob r P)) p
  let B := (referencePullback e A).filter fun z => z.1 = loc i
  have hf := coordRoutes_rows_floor (P := completeNoBob r P) hR hp
  have hlen := coordRoutes_length_le (completedNoBob_completeNoBob P r) hp
  have hstop := frontierRoutes_stop (completedNoBob_completeNoBob P r)
    (mem_frontierRoutes_of_mem_coordRoutes hp)
  have hs : IsBobNode (descend (completeNoBob r P) p) ∨ p.length = r := by
    rcases hstop with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2
  have hsub : rowsAt (completeNoBob r P) R p ⊆ B.image (referenceRowEmbedding e q) := by
    intro z hz
    obtain ⟨hzR, hza⟩ := Finset.mem_inter.mp hz
    obtain ⟨hzret, hzcoord, x, hx⟩ := Finset.mem_filter.mp hzR
    have hd := rowStop_eq_of_mem_aliceCols r _ p z (coordRoutes_isAlicePath hp)
      hza hlen hs
    refine Finset.mem_image.mpr ⟨(loc i, x), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_referencePullback e A _).mpr ?_, rfl⟩
      have heq : (loc i, e x) = z := by cases z; simp_all
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hzret, hd⟩
    · change (loc i, e x) = z
      cases z
      simp_all
  apply hf.trans
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ (referenceRowEmbedding e q).injective] using hc

/-- Reindexing one joint projection is a bijective renaming, not a product
of its marginal projections. -/
def selectedColumns {u : ℕ} (Q : Finset (Fin q)) (enum : Fin u ≃ Q)
    (S : Finset (Fin q → Y)) : Finset (Fin u → Y) :=
  (ProductExtraction.projection Q S).image (fun f j => f (enum j))

theorem selectedColumns_card {u : ℕ} (Q : Finset (Fin q)) (enum : Fin u ≃ Q)
    (S : Finset (Fin q → Y)) :
    (selectedColumns Q enum S).card = (ProductExtraction.projection Q S).card := by
  apply Finset.card_image_of_injective
  intro f g h
  funext j
  have := congrFun h (enum.symm j)
  simpa using this

theorem selectedColumns_mem {u : ℕ} (Q : Finset (Fin q)) (enum : Fin u ≃ Q)
    (S : Finset (Fin q → Y)) {f : Fin u → Y} (hf : f ∈ selectedColumns Q enum S) :
    ∃ s ∈ S, ∀ j, f j = s (enum j).val := by
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨s, hs, heq⟩ := ProductExtraction.mem_projection_iff.mp hg
  exact ⟨s, hs, fun j => (congrFun heq (enum j)).symm⟩

/-- A classical coordinate restriction is computed by a pullback of the
actual parent protocol; original row and column representatives are retained. -/
theorem selected_cost_le (N : X → Y → Bool) (e : Ref ↪ X)
    {u : ℕ} (Q : Finset (Fin q)) (enum : Fin u ≃ Q)
    (A : Finset (Fin q × X)) (S : Finset (Fin q → Y))
    (B : Finset (Fin u × Ref))
    (hB : ∀ z ∈ B, ((enum z.1).val, e z.2) ∈ A) :
    D (subgame (interlaceFun (fun x y => N (e x) y) u) B (selectedColumns Q enum S)) ≤
      D (subgame (interlaceFun N q) A S) := by
  let row : B → A := fun z => ⟨((enum z.val.1).val, e z.val.2), hB z.val z.property⟩
  let col : selectedColumns Q enum S → S := fun s =>
    ⟨(selectedColumns_mem Q enum S s.property).choose,
      (selectedColumns_mem Q enum S s.property).choose_spec.1⟩
  have heq : subgame (interlaceFun (fun x y => N (e x) y) u) B
      (selectedColumns Q enum S) =
      fun x y => subgame (interlaceFun N q) A S (row x) (col y) := by
    funext x y
    change N (e x.val.2) (y.val x.val.1) =
      N (e x.val.2) ((col y).val (enum x.val.1).val)
    rw [(selectedColumns_mem Q enum S y.property).choose_spec.2 x.val.1]
  rw [heq]
  exact D_mapNodes_le _ row col

/-- A lower bound for a fixed number of classical copies applies to actual
represented row fibres and their actual common column projection. -/
theorem lower_of_reference_projection [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X) {u K : ℕ} {x z : ℝ}
    (hu : 0 < u) (Q : Finset (Fin q)) (hQ : Q.card = u)
    (A : Finset (Fin q × X)) (S : Finset (Fin q → Y))
    (hrows : IsEquipartitionedGE (referencePullback e A) Q
      ⌈(Fintype.card Ref : ℝ) * x⌉₊)
    (hcols : z * (Fintype.card Y : ℝ) ^ u ≤ (ProductExtraction.projection Q S).card)
    (hbound : K ≤ Dfamily (interlaceFun (fun a b => N (e a) b) u)
      (bracketGE Ref Y u x z)) :
    K ≤ D (subgame (interlaceFun N q) A S) := by
  let enum : Fin u ≃ Q := (Q.orderIsoOfFin hQ).toEquiv
  have hfull : ⌈(Fintype.card Y : ℝ) ^ q * 1⌉₊ ≤
      (Finset.univ : Finset (Fin q → Y)).card := by
    simp only [mul_one, ← Nat.cast_pow, Nat.ceil_natCast, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
    exact le_rfl
  obtain ⟨BC, hBC, hrowprov, _⟩ := InheritedContracts.coordProjection q u hu Q enum
    (referencePullback e A) Finset.univ ⌈(Fintype.card Ref : ℝ) * x⌉₊ x 1
    hrows hfull le_rfl
  have hmem : (BC.1, selectedColumns Q enum S) ∈ bracketGE Ref Y u x z := by
    refine ⟨hBC.1, ?_⟩
    rw [selectedColumns_card, Nat.ceil_le]
    simpa [mul_comm] using hcols
  have hfamily := hbound.trans (Nat.sInf_le (show
      D (subgame (interlaceFun (fun a b => N (e a) b) u) BC.1 (selectedColumns Q enum S)) ∈
        {d : ℕ | ∃ RC ∈ bracketGE Ref Y u x z,
          d = D (subgame (interlaceFun (fun a b => N (e a) b) u) RC.1 RC.2)}
      from ⟨_, hmem, rfl⟩))
  exact hfamily.trans (selected_cost_le N e Q enum A S BC.1 (fun a ha =>
    (mem_referencePullback e A _).mp (hrowprov a ha)))

/-- A subset of represented coordinates inherits the actual routed row
floors. The only numeric conversion is the displayed ceiling comparison. -/
theorem represented_row_floors
    (e : Ref ↪ X) (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (retained : Finset (Fin q × X)) (loc : Coord ↪ Fin q)
    (A0 r : ℕ) (p : List Bool) (Q : Finset (Fin q)) (T : ℕ)
    (hR : ∀ i, refRowFloor A0 r ≤ (referenceSupport e retained (loc i)).card)
    (hQ : Q ⊆ represented (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) loc A0 r p)
    (hT : T ≤ refRowFloor A0 (r - p.length)) :
    IsEquipartitionedGE (referencePullback e (RoutedClosure.rowsAt retained
      (rowStop r (completeNoBob r P)) p)) Q T := by
  intro j hj
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hQ hj)
  obtain ⟨_, hi⟩ := Finset.mem_filter.mp hi
  rw [← heq]
  exact hT.trans (routed_reference_floor e P retained loc A0 r p i (hR i) hi)

/-- The two-reference exclusion is derived from the two actual reference
profiles and the actual pair projection. No terminal uniqueness hypothesis
or communication certificate for the final rectangle is supplied. -/
theorem terminal_reference_unique [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X)
    (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (retained : Finset (Fin q × X)) (S : Finset (Fin q → Y))
    (loc : Coord ↪ Fin q) (A0 r H : ℕ) (x : ℝ)
    (hH : 2 ≤ H) (hx : 0 < x) (hxlegal : 2 * x ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun (fun a b => N (e a) b) 1)
      (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun a b => N (e a) b) 1)
      (bracketGE Ref Y 1 x (3 / 10)))
    (hA0 : ⌈(Fintype.card Ref : ℝ) * (2 * x)⌉₊ ≤ A0)
    (hR : ∀ i, refRowFloor A0 r ≤ (referenceSupport e retained (loc i)).card)
    (hpairs : ∀ i j : Coord, i ≠ j → (9 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ 2 ≤
      (ProductExtraction.projection {loc i, loc j} S).card)
    (hP : ∀ z ∈ retained, ∀ y ∈ S, P.eval z y = interlaceFun N q z y)
    (hcost : P.cost ≤ H + r) (p : List Bool)
    (hp : p ∈ nodes P r retained) (hdepth : p.length = r)
    (i j : Coord)
    (hi : p ∈ coordRoutes (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) A0 r i)
    (hj : p ∈ coordRoutes (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) A0 r j) : i = j := by
  by_contra hij
  have hloc : loc i ≠ loc j := fun he => hij (loc.injective he)
  have hQ : ({loc i, loc j} : Finset (Fin q)).card = 2 := by simp [hloc]
  have hQsub : {loc i, loc j} ⊆ represented (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) loc A0 r p := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩
    · have hz' := Finset.mem_singleton.mp hz
      subst z
      exact Finset.mem_image.mpr ⟨j, by simp [hj], rfl⟩
  have hrows := represented_row_floors e P retained loc A0 r p {loc i, loc j}
    ⌈(Fintype.card Ref : ℝ) * (2 * x)⌉₊ hR hQsub
    (by simpa only [hdepth, Nat.sub_self, refRowFloor, pow_zero, one_mul] using hA0)
  have htwo := twoCopyLambda (fun a b => N (e a) b) hH hx (by linarith : x ≤ 1 / 2)
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1) h1
    (by convert h2 using 1 <;> norm_num)
  have hbound : H + 1 ≤ Dfamily (interlaceFun (fun a b => N (e a) b) 2)
      (bracketGE Ref Y 2 (2 * x) (9 / 25)) := by
    have h := htwo.trans (min_le_left _ _)
    convert h using 1 <;> norm_num
  have hlower := lower_of_reference_projection N e (by omega : 0 < 2)
    {loc i, loc j} hQ (RoutedClosure.rowsAt retained (rowStop r (completeNoBob r P)) p)
    S hrows (hpairs i j hij) hbound
  have hupper := RoutedClosure.terminal_subset_cost_le P r (H + 1) retained
    (RoutedClosure.rowsAt retained (rowStop r (completeNoBob r P)) p) S
    (interlaceFun N q) hP (by omega) (by omega) p hp hdepth
    (fun z hz => Finset.mem_filter.mp hz)
  omega

/-- The two child projections cover the original joint projection. -/
theorem projection_children (Q : Finset (Fin q)) (S : Finset (Fin q → Y))
    (b : (Fin q → Y) → Bool) :
    (ProductExtraction.projection Q S).card ≤
      (ProductExtraction.projection Q (S.filter fun y => b y = false)).card +
      (ProductExtraction.projection Q (S.filter fun y => b y = true)).card := by
  have hS : S = (S.filter fun y => b y = false) ∪ (S.filter fun y => b y = true) := by
    ext y
    cases hy : b y <;> simp [hy]
  have hp : ProductExtraction.projection Q S =
      ProductExtraction.projection Q (S.filter fun y => b y = false) ∪
      ProductExtraction.projection Q (S.filter fun y => b y = true) := by
    conv_lhs => rw [hS]
    exact Finset.image_union _ _
  rw [hp]
  exact Finset.card_union_le _ _

theorem denser_projection_child (Q : Finset (Fin q)) (S : Finset (Fin q → Y))
    (b : (Fin q → Y) → Bool) {a : ℝ}
    (h : 2 * a ≤ (ProductExtraction.projection Q S).card) :
    ∃ bit : Bool, a ≤ (ProductExtraction.projection Q (S.filter fun y => b y = bit)).card := by
  have hsum : ((ProductExtraction.projection Q S).card : ℝ) ≤
      (ProductExtraction.projection Q (S.filter fun y => b y = false)).card +
      (ProductExtraction.projection Q (S.filter fun y => b y = true)).card := by
    exact_mod_cast projection_children Q S b
  by_cases hl : a ≤ (ProductExtraction.projection Q (S.filter fun y => b y = false)).card
  · exact ⟨false, hl⟩
  · exact ⟨true, by linarith⟩

theorem denser_child (S : Finset (Fin q → Y)) (b : (Fin q → Y) → Bool) {a : ℝ}
    (h : 2 * a ≤ S.card) : ∃ bit : Bool, a ≤ (S.filter fun y => b y = bit).card := by
  have hsum : (S.filter fun y => b y = false).card + (S.filter fun y => b y = true).card = S.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun y => b y = false)
    have heq : (S.filter fun y => ¬ b y = false) = S.filter (fun y => b y = true) := by
      ext y
      cases hy : b y <;> simp [hy]
    simpa only [heq] using h
  have hr : ((S.filter fun y => b y = false).card : ℝ) +
      (S.filter fun y => b y = true).card = S.card := by exact_mod_cast hsum
  by_cases hl : a ≤ (S.filter fun y => b y = false).card
  · exact ⟨false, hl⟩
  · exact ⟨true, by linarith⟩

/-- Localized stopping with the actual first Bob bit already spent. Its
factor one half is supplied to the stopping theorem, not hidden in a gate. -/
theorem fullProduct_half_blockLowerBound [Nonempty Ref] [Nonempty Y]
    (M : Ref → Y → Bool) {H m R : ℕ} {x h : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m) (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m)
    (hx : 0 < x) (hrow : (2 : ℝ) ^ m * x ≤ 1) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun M 1) (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun M 1) (bracketGE Ref Y 1 x (3 / 10)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)))
    (R' : ℕ) (hR' : R' ≤ R) :
    ProtocolSeparation.BlockLowerBound (interlaceFun M q) Prod.fst Finset.univ
      (2 ^ R' * HardSeed.copyCount m)
      ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card Ref : ℝ)⌉₊ (h / 2)
      (H + (R' + m)) := by
  let E : Fin (Fintype.card (Fin q → Y)) ≃ (Fin q → Y) := (Fintype.equivFin _).symm
  have hbound := ExactCoordinateControl.coordinateBlockLowerBound_of_width (z := h / 2)
    M hwidth hH hm hx hrow (by norm_num : (0 : ℝ) ≤ 0) hh h1 h2
    ((by omega : 1 ≤ H).trans h1) E (fullProduct_balanced (2 ^ m) E)
    hgateOne (by simpa using hgateSeed) 1 R'
    (2 ^ R' * HardSeed.copyCount m)
    ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card Ref : ℝ)⌉₊
    (by omega) hR' le_rfl le_rfl (by norm_num [Real.rpow_neg_one]; linarith)
  intro A C Q _ hC hQ hA
  let C' := C.image E.symm
  have hcard : C'.card = C.card := Finset.card_image_of_injective _ E.symm.injective
  have hlower := hbound A C' Q (Finset.subset_univ _)
    (by simpa only [C', hcard, Finset.card_univ, Fintype.card_fin] using hC) hQ hA
  let col : C' → C := fun j => ⟨E j.val, by
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp j.property
    simpa only [← heq, E.apply_symm_apply] using hc⟩
  exact hlower.trans (D_mapNodes_le (subgame (interlaceFun M q) A C) id col)

/-- The routed integral floor dominates the genuine row-density ceiling. -/
theorem density_floor_le {A0 ell : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hA0 : ⌈(Fintype.card Ref : ℝ) * (2 * x)⌉₊ ≤ A0) :
    ⌈(Fintype.card Ref : ℝ) * ((2 : ℝ) ^ ell * x)⌉₊ ≤ refRowFloor A0 ell := by
  have hA : (Fintype.card Ref : ℝ) * (2 * x) ≤ A0 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hA0)
  apply Nat.ceil_le.mpr
  simp only [refRowFloor, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ ell := by positivity
  have hc : (0 : ℝ) ≤ (Fintype.card Ref : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hA hp]

/-- At a first Bob node, excessive reference weight gives a child requiring
one more bit than the residual protocol has. Small capacities use the row
ladder; large capacities use localized stopping on actual full tuples. -/
theorem firstBob_reference_weight_lt [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X)
    (P : Protocol (Fin q × X) (Fin q → Y) Bool)
    (retained : Finset (Fin q × X)) (S : Finset (Fin q → Y))
    (loc : Coord ↪ Fin q) (A0 r m H : ℕ) (x theta : ℝ)
    (hq : q = 2 ^ r) (hmr : m ≤ r) (hm : 2 ^ 20 ≤ m)
    (hH : 2 ≤ H) (hx : 0 < x) (hrow : (2 : ℝ) ^ m * x ≤ 1)
    (htheta : 0 < theta)
    (h1 : H ≤ Dfamily (interlaceFun (fun a b => N (e a) b) 1)
      (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun a b => N (e a) b) 1)
      (bracketGE Ref Y 1 x (3 / 10)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ m) theta (H + r))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      theta * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)))
    (hA0 : ⌈(Fintype.card Ref : ℝ) * (2 * x)⌉₊ ≤ A0)
    (hR : ∀ i, refRowFloor A0 r ≤ (referenceSupport e retained (loc i)).card)
    (hS : theta * (Fintype.card (Fin q → Y) : ℝ) ≤ S.card)
    (hsmall : ∀ ell, 1 ≤ ell → ell < m → ∀ Q : Finset (Fin q),
      Q ⊆ Finset.univ.image loc → Q.card = 2 ^ (ell - 1) + 1 →
      (18 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card ≤
        (ProductExtraction.projection Q S).card)
    (hP : ∀ z ∈ retained, ∀ y ∈ S, P.eval z y = interlaceFun N q z y)
    (hcost : P.cost ≤ H + r) (p : List Bool)
    (hp : p ∈ nodes P r retained) (hpdepth : p.length < r) :
    weightAt (completeNoBob r P) (fun i => referenceSupport e retained (loc i)) A0 r p <
      (9 / 16 : ℝ) * stoppingCapacity r p.length := by
  by_contra hbad
  have hbad := le_of_not_gt hbad
  let ell := r - p.length
  have hell : 1 ≤ ell := by dsimp [ell]; omega
  have heller : ell ≤ r := Nat.sub_le _ _
  let V := represented (completeNoBob r P)
    (fun i => referenceSupport e retained (loc i)) loc A0 r p
  have hV : (9 / 16 : ℝ) * (2 : ℝ) ^ ell ≤ V.card := by
    have hw := weight_le_represented (completeNoBob r P)
      (fun i => referenceSupport e retained (loc i)) loc A0 r p
    have hb : (9 / 16 : ℝ) * (2 : ℝ) ^ ell ≤
        weightAt (completeNoBob r P) (fun i => referenceSupport e retained (loc i)) A0 r p := by
      simpa only [stoppingCapacity, Nat.cast_pow, Nat.cast_ofNat] using hbad
    exact hb.trans hw
  have hVloc : V ⊆ Finset.univ.image loc := by
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hBob : IsBobNode (descend (completeNoBob r P) p) := by
    rcases node_stops P r retained hp with h | h
    · exact h.2.1
    · exact False.elim (by have := h.2; omega)
  obtain ⟨b, lo, hi, hnode⟩ : ∃ b lo hi, descend (completeNoBob r P) p = .bNode b lo hi := by
    cases heq : descend (completeNoBob r P) p with
    | leaf z => simp [heq, IsBobNode] at hBob
    | aNode a lo hi => simp [heq, IsBobNode] at hBob
    | bNode b lo hi => exact ⟨b, lo, hi, rfl⟩
  let A := RoutedClosure.rowsAt retained (rowStop r (completeNoBob r P)) p
  have hupper (bit : Bool) := RoutedClosure.bob_child_restriction_budget P r (H + 1)
    retained S (interlaceFun N q) hP (by omega) (by omega) p hp b lo hi hnode bit
  have hfloors (Q : Finset (Fin q)) (hQ : Q ⊆ V) :
      IsEquipartitionedGE (referencePullback e A) Q
        ⌈(Fintype.card Ref : ℝ) * ((2 : ℝ) ^ ell * x)⌉₊ :=
    represented_row_floors e P retained loc A0 r p Q _ hR hQ
      (density_floor_le hx.le hA0)
  by_cases hsmallcap : ell < m
  · have hcount : 2 ^ (ell - 1) + 1 ≤ V.card := by
      have hh := smallCopyWidth_le_ceil_weight hell
        (show vartheta * (2 : ℝ) ^ ell ≤ (V.card : ℝ) by simpa [vartheta_val] using hV)
      simpa only [WrapperProjectionCovers.smallCopyWidth_dyadic hell, Nat.ceil_natCast] using hh
    obtain ⟨Q, hQV, hQcard⟩ := Finset.exists_subset_card_eq hcount
    have hproj := hsmall ell hell hsmallcap Q (hQV.trans hVloc) hQcard
    obtain ⟨bit, hchild⟩ := denser_projection_child Q S b
      (a := (9 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card) (by linarith)
    have hellrow : (2 : ℝ) ^ ell * x ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsmallcap.le) hx.le).trans hrow
    have hladder := repeatedRowDoubling (fun a b => N (e a) b) hH hx
      (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1)
      h1 (by convert h2 using 1 <;> norm_num) ell hell hellrow
    have hbound : H + ell ≤ Dfamily
        (interlaceFun (fun a b => N (e a) b) (2 ^ (ell - 1) + 1))
        (bracketGE Ref Y (2 ^ (ell - 1) + 1) ((2 : ℝ) ^ ell * x) (9 / 25)) := by
      have hh := hladder.trans (min_le_left _ _)
      convert hh using 1 <;> norm_num
    have hlower := lower_of_reference_projection N e
      (by positivity : 0 < 2 ^ (ell - 1) + 1) Q hQcard A (S.filter fun y => b y = bit)
      (hfloors Q hQV) (by simpa only [hQcard] using hchild) hbound
    have hu := hupper bit
    change _ + p.length + 1 ≤ _ at hu
    dsimp [ell, A] at hlower
    omega
  · have hlarge : m ≤ ell := by omega
    have hcount : 2 ^ (ell - m) * HardSeed.copyCount m ≤ V.card := by
      have heq := residual_copyCount_cast m (ell - m) (by omega)
      rw [Nat.sub_add_cancel hlarge] at heq
      exact_mod_cast (show ((2 ^ (ell - m) * HardSeed.copyCount m : ℕ) : ℝ) ≤ V.card by
        rw [heq]; linarith)
    obtain ⟨Q, hQV, hQcard⟩ := Finset.exists_subset_card_eq hcount
    obtain ⟨bit, hchild⟩ := denser_child S b
      (a := theta / 2 * (Fintype.card (Fin q → Y) : ℝ)) (by linarith)
    have hwidth : q = 2 ^ (r - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmr]
      exact hq
    have hb := fullProduct_half_blockLowerBound (q := q) (fun a b => N (e a) b)
      hwidth hH hm hx hrow htheta h1 h2
      (by simpa only [Nat.sub_add_cancel hmr] using hgateOne) hgateSeed
      (ell - m) (Nat.sub_le_sub_right heller m)
    have hrows := hfloors Q hQV
    have hlower := hb (referencePullback e A) (S.filter fun y => b y = bit) Q
      (Finset.subset_univ _) (by simpa only [Finset.card_univ] using hchild)
      (by omega) (by
        simpa only [Nat.sub_add_cancel hlarge, mul_assoc, mul_comm, mul_left_comm] using hrows)
    have hlower' := hlower.trans
      (reference_restriction_le N e A (S.filter fun y => b y = bit))
    rw [Nat.sub_add_cancel hlarge] at hlower'
    have hu := hupper bit
    dsimp [ell, A] at hlower'
    omega

/-- Both exclusions at the literal manuscript parameters. All localized
stopping inequalities here are discharged by the proved parameter formulas.
The remaining inputs are the two reference-matrix profiles and actual
retained row/column geometry; neither exclusion is an input. -/
theorem reference_exclusions_parameters [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X) (i : Parameters.Input)
    (P : Protocol (Fin (Parameters.outerWidth i) × X)
      (Fin (Parameters.outerWidth i) → Y) Bool)
    (retained : Finset (Fin (Parameters.outerWidth i) × X))
    (S : Finset (Fin (Parameters.outerWidth i) → Y))
    (loc : Coord ↪ Fin (Parameters.outerWidth i)) (A0 : ℕ)
    (h1 : Parameters.certificateCost i - 1 ≤
      Dfamily (interlaceFun (fun a b => N (e a) b) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 5)))
    (h2 : Parameters.certificateCost i - 2 ≤
      Dfamily (interlaceFun (fun a b => N (e a) b) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 10)))
    (hA0 : ⌈(Fintype.card Ref : ℝ) *
      (2 * (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)))⌉₊ ≤ A0)
    (hR : ∀ j, refRowFloor A0 (Parameters.outerExponent i) ≤
      (referenceSupport e retained (loc j)).card)
    (hS : ((Parameters.retainedFraction i : ℚ) : ℝ) *
      (Fintype.card (Fin (Parameters.outerWidth i) → Y) : ℝ) ≤ S.card)
    (hsmall : ∀ ell, 1 ≤ ell → ell < Parameters.referenceExponent i →
      ∀ Q : Finset (Fin (Parameters.outerWidth i)), Q ⊆ Finset.univ.image loc →
      Q.card = 2 ^ (ell - 1) + 1 →
      (18 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card ≤
        (ProductExtraction.projection Q S).card)
    (hpairs : ∀ j k : Coord, j ≠ k →
      (9 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ 2 ≤
        (ProductExtraction.projection {loc j, loc k} S).card)
    (hP : ∀ z ∈ retained, ∀ y ∈ S,
      P.eval z y = interlaceFun N (Parameters.outerWidth i) z y)
    (hcost : P.cost ≤ Parameters.certificateCost i + Parameters.outerExponent i - 1) :
    (∀ p ∈ nodes P (Parameters.outerExponent i) retained,
      p.length < Parameters.outerExponent i →
      weightAt (completeNoBob (Parameters.outerExponent i) P)
        (fun j => referenceSupport e retained (loc j)) A0 (Parameters.outerExponent i) p ≤
        (9 / 16 : ℝ) * stoppingCapacity (Parameters.outerExponent i) p.length) ∧
    (∀ p ∈ nodes P (Parameters.outerExponent i) retained,
      p.length = Parameters.outerExponent i → ∀ j k : Coord,
      p ∈ coordRoutes (completeNoBob (Parameters.outerExponent i) P)
        (fun j => referenceSupport e retained (loc j)) A0 (Parameters.outerExponent i) j →
      p ∈ coordRoutes (completeNoBob (Parameters.outerExponent i) P)
        (fun j => referenceSupport e retained (loc j)) A0 (Parameters.outerExponent i) k →
      j = k) := by
  have hscale : 1 ≤ Parameters.scale i := (by norm_num : 1 ≤ (2 : ℕ) ^ 24).trans
    (Parameters.scale_floor i)
  have hscaleSq : 1 ≤ Parameters.scale i ^ 2 := one_le_pow₀ hscale
  have hmr : Parameters.referenceExponent i ≤ Parameters.outerExponent i := by
    unfold Parameters.referenceExponent Parameters.outerExponent
    nlinarith
  have hC : 3 ≤ Parameters.certificateCost i := by
    unfold Parameters.certificateCost Parameters.firstExponent
    omega
  have hm := (ParameterGates.hard_seed_exponent_domains i).2.1
  have hx : 0 < (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)) := by positivity
  have hrow : (2 : ℝ) ^ Parameters.referenceExponent i *
      (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)) ≤ 1 := by
    simpa only [Parameters.referenceWidth, Nat.cast_pow, Nat.cast_ofNat] using
      ParameterGates.reference_row_request i
  have htwo : 2 * (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)) ≤ 1 := by
    have hp : (2 : ℝ) ≤ (2 : ℝ) ^ Parameters.referenceExponent i := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ Parameters.referenceExponent i by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hrow
  have htheta : (0 : ℝ) < (Parameters.retainedFraction i : ℚ) := by
    exact_mod_cast Parameters.retainedFraction_pos i
  have hs := ParameterGates.reference_stopping_gates i
  have hgOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ Parameters.referenceExponent i)
      (Parameters.retainedFraction i : ℚ)
      (Parameters.certificateCost i - 1 + Parameters.outerExponent i) := by
    simpa only [yLoss, Parameters.referenceWidth, Nat.cast_pow, Nat.cast_ofNat,
      add_zero, div_one] using hs.1
  have hgSeed : HardSeed.columnDensity ((2 : ℝ) ^ Parameters.referenceExponent i) ≤
      ((Parameters.retainedFraction i : ℚ) : ℝ) *
        (2 : ℝ) ^ (-((Parameters.certificateCost i - 1 + Parameters.referenceExponent i : ℕ) : ℝ)) := by
    simpa only [Parameters.referenceWidth, Nat.cast_pow, Nat.cast_ofNat] using hs.2
  have h2' : Parameters.certificateCost i - 1 - 1 ≤
      Dfamily (interlaceFun (fun a b => N (e a) b) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 10)) := by omega
  constructor
  · intro p hp hd
    exact (firstBob_reference_weight_lt N e P retained S loc A0
      (Parameters.outerExponent i) (Parameters.referenceExponent i)
      (Parameters.certificateCost i - 1) _ _ rfl hmr hm (by omega)
      hx hrow htheta h1 h2' hgOne hgSeed hA0 hR hS hsmall hP (by omega) p hp hd).le
  · intro p hp hd j k hj hk
    exact terminal_reference_unique N e P retained S loc A0
      (Parameters.outerExponent i) (Parameters.certificateCost i - 1) _
      (by omega) hx htwo h1 h2' hA0 hR hpairs hP (by omega) p hp hd j k hj hk

end EthInapproximability.CurrentPaper.ConcreteReferenceExclusions
