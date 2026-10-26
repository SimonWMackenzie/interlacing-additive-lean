import EthInapproximability.CurrentPaper.ProtocolFrontier
import NPCC.Relaxed

/-!
# Local estimates for the current paper's complete stopping collection

Source: replacement v8, `A-stage4-details.tex`,
`clm:paper-global-outflow` and `clm:paper-global-transfer`.

The sets below are actual retained rows of one fixed protocol.  Initial
deletions, reference rows lost along a route, and additional rows leaving
their assigned node are disjoint pieces of the same original block.  In
particular none of the mass identities is an assumed conservation law.

The communication bounds used here are local restriction theorems; their
specialisation to the protected matrix is a separate obligation.  This file
does not assume either the desired outflow bound or a final global gap.
-/

namespace EthInapproximability.CurrentPaper.RoutedClosure

open scoped BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.DenseFrontierConservation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.CurrentPaper

variable {X Y Coord Node : Type*}
variable [DecidableEq X] [DecidableEq Coord] [DecidableEq Node]

/-- Rows of one original copy, before any deletion. -/
def originalBlock (full : Finset X) (origin : X → Coord) (j : Coord) : Finset X :=
  full.filter fun x => origin x = j

/-- Rows of a specified copy at their actual stopping destination. -/
def blockAt (retained : Finset X) (origin : X → Coord)
    (destination : X → Node) (j : Coord) (p : Node) : Finset X :=
  retained.filter fun x => origin x = j ∧ destination x = p

/-- Initially retained reference rows of a copy which do not reach its node. -/
def lostReference (retained reference : Finset X) (origin : X → Coord)
    (destination : X → Node) (j : Coord) (p : Node) : Finset X :=
  (retained ∩ reference).filter fun x => origin x = j ∧ destination x ≠ p

/-- Exact four-way partition of one original block.  It counts every
destination, including first-Bob and zero-reference nodes. -/
theorem block_card_partition (full retained reference : Finset X)
    (hretained : retained ⊆ full) (origin : X → Coord) (destination : X → Node)
    (assigned : Coord → Node) (j : Coord) :
    (originalBlock full origin j).card =
      (blockAt retained origin destination j (assigned j)).card +
      (originalBlock full origin j \ retained).card +
      (lostReference retained reference origin destination j (assigned j)).card +
      (GlobalCount.outgoing (retained \ reference) origin destination assigned j).card := by
  classical
  let B := originalBlock full origin j
  let R := B ∩ retained
  let S := R.filter fun x => destination x = assigned j
  let T := R.filter fun x => destination x ≠ assigned j
  have hB : R.card + (B \ retained).card = B.card :=
    Finset.card_inter_add_card_sdiff B retained
  have hR : S.card + T.card = R.card := by
    exact Finset.card_filter_add_card_filter_not (s := R) (p := fun x => destination x = assigned j)
  have hT : (T ∩ reference).card + (T \ reference).card = T.card :=
    Finset.card_inter_add_card_sdiff T reference
  have hS : S = blockAt retained origin destination j (assigned j) := by
    ext x
    simp only [S, R, B, originalBlock, blockAt, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨⟨_, hj⟩, hx⟩, hp⟩
      exact ⟨hx, hj, hp⟩
    · rintro ⟨hx, hj, hp⟩
      exact ⟨⟨⟨hretained hx, hj⟩, hx⟩, hp⟩
  have hTR : T ∩ reference =
      lostReference retained reference origin destination j (assigned j) := by
    ext x
    simp only [T, R, B, originalBlock, lostReference, Finset.mem_filter,
      Finset.mem_inter]
    constructor
    · rintro ⟨⟨⟨⟨_, hj⟩, hx⟩, hp⟩, hf⟩
      exact ⟨⟨hx, hf⟩, hj, hp⟩
    · rintro ⟨⟨hx, hf⟩, hj, hp⟩
      exact ⟨⟨⟨⟨hretained hx, hj⟩, hx⟩, hp⟩, hf⟩
  have hTA : T \ reference =
      GlobalCount.outgoing (retained \ reference) origin destination assigned j := by
    ext x
    simp only [T, R, B, originalBlock, GlobalCount.outgoing, Finset.mem_filter,
      Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨⟨⟨_, hj⟩, hx⟩, hp⟩, hf⟩
      exact ⟨⟨hx, hf⟩, hj, hp⟩
    · rintro ⟨⟨hx, hf⟩, hj, hp⟩
      exact ⟨⟨⟨⟨hretained hx, hj⟩, hx⟩, hp⟩, hf⟩
  rw [hS] at hR
  rw [hTR, hTA] at hT
  change B.card = _
  change R.card + (originalBlock full origin j \ retained).card = B.card at hB
  omega

omit [DecidableEq X] in
/-- A genuine residual protocol computes every selected row on the SAME
retained column set, even if the ambient protocol is specified only on the
original retained rectangle. -/
theorem residual_agrees (P : Protocol X Y Bool) (r : ℕ)
    (retained : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (p : List Bool) (rows : Finset X)
    (hrows : ∀ x ∈ rows, x ∈ retained ∧
      ProtocolFrontier.rowStop r (completeNoBob r P) x = p) :
    D (subgame F rows columns) ≤ (descend (completeNoBob r P) p).cost := by
  let Q := Protocol.restrictSub rows columns (descend (completeNoBob r P) p)
  have hQ : Q.Computes (subgame F rows columns) := by
    intro x y
    have hx := hrows x.val x.property
    rw [show Q = Protocol.restrictSub rows columns (descend (completeNoBob r P) p) from rfl,
      Protocol.eval_restrictSub]
    change (descend (completeNoBob r P) p).eval x.val y.val = F x.val y.val
    rw [← hx.2, ProtocolFrontier.rowStop_eval, completeNoBob_eval]
    exact hP x.val hx.1 y.val y.property
  have hcost := Nat.sInf_le (show Q.cost ∈ AchievableCosts (subgame F rows columns)
    from ⟨Q, rfl, hQ⟩)
  simpa only [Q, Protocol.cost_restrictSub] using hcost

/-- Every actual subset of a terminal rectangle has the same charged upper
bound; this form permits the joint two-coordinate transfer restriction. -/
theorem terminal_subset_cost_le (P : Protocol X Y Bool) (r C : ℕ)
    (retained rows : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (p : List Bool) (hp : p ∈ ProtocolFrontier.nodes P r retained) (hdepth : p.length = r)
    (hrows : ∀ x ∈ rows, x ∈ retained ∧
      ProtocolFrontier.rowStop r (completeNoBob r P) x = p) :
    D (subgame F rows columns) ≤ C - 1 := by
  have hb := ProtocolFrontier.node_residual_budget P r retained hC hcost hp
  rw [hdepth] at hb
  have hd := residual_agrees P r retained columns F hP p rows hrows
  omega

/-- At an assigned terminal node the actual restriction of a cost
`C+r-1` protocol has at most `C-1` bits left. -/
theorem terminal_block_cost_le (P : Protocol X Y Bool) (r C : ℕ)
    (retained : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (origin : X → Coord) (j : Coord) (p : List Bool)
    (hp : p ∈ ProtocolFrontier.nodes P r retained) (hdepth : p.length = r) :
    D (subgame F (blockAt retained origin
      (ProtocolFrontier.rowStop r (completeNoBob r P)) j p) columns) ≤ C - 1 := by
  exact terminal_subset_cost_le P r C retained _ columns F hP hC hcost p hp hdepth
    (by intro x hx; exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.2⟩)

/-- Compulsory outflow from an actual assigned rectangle.  The only lower
bound premise is the upstream dense-restriction theorem for this matrix;
the depth contradiction and all row accounting are derived here. -/
theorem compulsory_outflow (P : Protocol X Y Bool) (r C m : ℕ)
    (full retained reference : Finset X) (hretained : retained ⊆ full)
    (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hm : 0 < m) (hcost : P.cost ≤ C + r - 1)
    (origin : X → Coord) (assigned : Coord → List Bool) (j : Coord)
    (hp : assigned j ∈ ProtocolFrontier.nodes P r retained)
    (hdepth : (assigned j).length = r) (eta : ℚ)
    (hblock : (originalBlock full origin j).card = m)
    (hdelete : ((originalBlock full origin j \ retained).card : ℚ) ≤ eta * m / 16)
    (hreference : ((lostReference retained reference origin
      (ProtocolFrontier.rowStop r (completeNoBob r P)) j (assigned j)).card : ℚ) <
        eta * m / 16)
    (hdense : ∀ rows : Finset X,
      rows ⊆ originalBlock full origin j → (1 - eta) * m ≤ (rows.card : ℚ) →
        C ≤ D (subgame F rows columns)) :
    7 * eta / 8 < GlobalCount.mass m
      (GlobalCount.outgoing (retained \ reference) origin
        (ProtocolFrontier.rowStop r (completeNoBob r P)) assigned j) := by
  let dest := ProtocolFrontier.rowStop r (completeNoBob r P)
  let stay := blockAt retained origin dest j (assigned j)
  have hstay : (stay.card : ℚ) < (1 - eta) * m := by
    by_contra hn
    have hd := hdense stay (by
      intro x hx
      obtain ⟨hx, hj, _⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hretained hx, hj⟩) (le_of_not_gt hn)
    have hu := terminal_block_cost_le P r C retained columns F hP hC hcost
      origin j (assigned j) hp hdepth
    change D (subgame F stay columns) ≤ C - 1 at hu
    omega
  have hpartition := block_card_partition full retained reference hretained
    origin dest assigned j
  rw [hblock] at hpartition
  have hpartitionQ : (m : ℚ) = (stay.card : ℚ) +
      ((originalBlock full origin j \ retained).card : ℚ) +
      ((lostReference retained reference origin dest j (assigned j)).card : ℚ) +
      ((GlobalCount.outgoing (retained \ reference) origin dest assigned j).card : ℚ) := by
    exact_mod_cast hpartition
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  apply (lt_div_iff₀ hmQ).mpr
  change 7 * eta / 8 * m < _
  dsimp [dest] at hpartitionQ
  nlinarith

/-- Outgoing rows from `j` which actually arrive at the node assigned to `i`.
The row labels, and not a synthetic flow matrix, determine this set. -/
def transferTo (rows : Finset X) (origin : X → Coord) (destination : X → Node)
    (assigned : Coord → Node) (j i : Coord) : Finset X :=
  (GlobalCount.outgoing rows origin destination assigned j).filter fun x =>
    destination x = assigned i

omit [DecidableEq X] in
/-- Actual disjoint destination fibres account for all transfers. -/
theorem transfer_mass_eq_sum (rows : Finset X) (origin : X → Coord)
    (destination : X → Node) (assigned : Coord → Node) (J : Finset Coord)
    (hinj : Set.InjOn assigned J) (j : Coord) (m : ℕ) :
    GlobalCount.mass m (GlobalCount.transferred rows origin destination J assigned j) =
      ∑ i ∈ J, GlobalCount.mass m (transferTo rows origin destination assigned j i) := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (GlobalCount.outgoing rows origin destination assigned j) (J.image assigned) destination
  rw [Finset.sum_image (fun i hi k hk hik => hinj hi hk hik)] at hc
  have hcn : (GlobalCount.transferred rows origin destination J assigned j).card =
      ∑ i ∈ J, (transferTo rows origin destination assigned j i).card := hc.symm
  simp only [GlobalCount.mass, ← Finset.sum_div, ← Nat.cast_sum]
  rw [hcn]

/-- Summing the concrete per-destination two-stream bounds gives the paper's
`3 eta / 40` estimate. Reference errors are normalized by `g*m`; the two
different normalizations remain visible in the `epsilon` sum premise. -/
theorem transfer_mass_bound (rows : Finset X) (origin : X → Coord)
    (destination : X → Node) (assigned : Coord → Node) (J : Finset Coord)
    (hinj : Set.InjOn assigned J) (j : Coord) (m q : ℕ)
    (mu lambda eta g : ℚ) (epsilon : Coord → ℚ)
    (hmu : 0 ≤ mu) (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) (hg : 0 < g)
    (hcard : J.card ≤ q) (hmug : mu ≤ g / 20)
    (hloss : (∑ i ∈ J, epsilon i) ≤ eta / (8 * g))
    (hlambdaGate : 2 * mu * q * lambda ≤ eta / 16)
    (hlocal : ∀ i ∈ J, GlobalCount.mass m
      (transferTo rows origin destination assigned j i) ≤ 2 * mu * (lambda + epsilon i)) :
    GlobalCount.mass m (GlobalCount.transferred rows origin destination J assigned j) ≤
      3 * eta / 40 := by
  rw [transfer_mass_eq_sum rows origin destination assigned J hinj j m]
  have hsum : (∑ i ∈ J, 2 * mu * (lambda + epsilon i)) =
      2 * mu * ((J.card : ℚ) * lambda + ∑ i ∈ J, epsilon i) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
  have hcardQ : (J.card : ℚ) ≤ q := by exact_mod_cast hcard
  have hsumBound := Finset.sum_le_sum hlocal
  rw [hsum] at hsumBound
  have hbase : 2 * mu * ((J.card : ℚ) * lambda) ≤ eta / 16 := by
    calc
      _ ≤ 2 * mu * ((q : ℚ) * lambda) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardQ hlambda) (by positivity)
      _ = 2 * mu * q * lambda := by ring
      _ ≤ eta / 16 := hlambdaGate
  have herr : 2 * mu * (∑ i ∈ J, epsilon i) ≤ eta / 80 := by
    calc
      _ ≤ 2 * mu * (eta / (8 * g)) :=
        mul_le_mul_of_nonneg_left hloss (by positivity)
      _ ≤ 2 * (g / 20) * (eta / (8 * g)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmug (by norm_num))
          (by positivity)
      _ = eta / 80 := by field_simp; ring
  nlinarith

/-- Rows reaching a stopping node, without any filter by reference support. -/
def rowsAt (retained : Finset X) (destination : X → Node) (p : Node) : Finset X :=
  retained.filter fun x => destination x = p

/-- A proved two-stream restriction lower bound rules out excessive transfer
to another assigned node. Its threshold is the current paper's
`2*mu*(lambda0+epsilon_i)`, not the obsolete three-support threshold. -/
theorem terminal_transfer_bound (P : Protocol X Y Bool) (r C m : ℕ)
    (retained additional : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (origin : X → Coord) (assigned : Coord → List Bool) (j i : Coord)
    (hp : assigned i ∈ ProtocolFrontier.nodes P r retained)
    (hdepth : (assigned i).length = r) (mu lambda epsilon : ℚ)
    (htwoStream : 2 * mu * (lambda + epsilon) < GlobalCount.mass m
      (transferTo additional origin (ProtocolFrontier.rowStop r (completeNoBob r P))
        assigned j i) →
      C ≤ D (subgame F
        (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) (assigned i))
        columns)) :
    GlobalCount.mass m
      (transferTo additional origin (ProtocolFrontier.rowStop r (completeNoBob r P))
        assigned j i) ≤ 2 * mu * (lambda + epsilon) := by
  by_contra hn
  have hlower := htwoStream (lt_of_not_ge hn)
  have hupper := terminal_subset_cost_le P r C retained
    (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) (assigned i))
    columns F hP hC hcost (assigned i) hp hdepth
    (by intro x hx; exact Finset.mem_filter.mp hx)
  omega

/-- Terminal receiving capacity from a genuine multi-copy restriction lower
bound, including terminals containing no reference rows. -/
theorem terminal_receiving_bound (P : Protocol X Y Bool) (r C m : ℕ)
    (retained additional : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (origin : X → Coord) (J : Finset Coord) (p : List Bool)
    (hp : p ∈ ProtocolFrontier.nodes P r retained)
    (hdepth : p.length = r) (capacity : ℚ)
    (hpacket : 2 * capacity ≤ GlobalCount.mass m
      (GlobalCount.received additional origin (ProtocolFrontier.rowStop r (completeNoBob r P)) J p) →
      C ≤ D (subgame F
        (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) p) columns)) :
    GlobalCount.mass m
      (GlobalCount.received additional origin (ProtocolFrontier.rowStop r (completeNoBob r P)) J p) <
        2 * capacity := by
  by_contra hn
  have hlower := hpacket (le_of_not_gt hn)
  have hupper := terminal_subset_cost_le P r C retained
    (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) p)
    columns F hP hC hcost p hp hdepth
    (by intro x hx; exact Finset.mem_filter.mp hx)
  omega

/-- The next Bob bit is charged explicitly. Both branches are restrictions
of the same fixed columns and of the same residual protocol. -/
theorem bob_child_restriction_budget (P : Protocol X Y Bool) (r C : ℕ)
    (retained : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (p : List Bool) (hp : p ∈ ProtocolFrontier.nodes P r retained)
    (b : Y → Bool) (lo hi : Protocol X Y Bool)
    (hnode : descend (completeNoBob r P) p = .bNode b lo hi) (bit : Bool) :
    D (subgame F (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) p)
      (columns.filter fun y => b y = bit)) + p.length + 1 ≤ C + r - 1 := by
  let rows := rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) p
  let cols := columns.filter fun y => b y = bit
  let child := if bit then hi else lo
  let Q := Protocol.restrictSub rows cols child
  have hQ : Q.Computes (subgame F rows cols) := by
    intro x y
    have hx := Finset.mem_filter.mp x.property
    have hy := Finset.mem_filter.mp y.property
    have hEval : (descend (completeNoBob r P) p).eval x.val y.val = F x.val y.val := by
      rw [← hx.2, ProtocolFrontier.rowStop_eval, completeNoBob_eval]
      exact hP x.val hx.1 y.val hy.1
    rw [hnode] at hEval
    rw [show Q = Protocol.restrictSub rows cols child from rfl, Protocol.eval_restrictSub]
    change child.eval x.val y.val = F x.val y.val
    cases bit <;> simpa [child, Protocol.eval, hy.2] using hEval
  have hD := Nat.sInf_le (show Q.cost ∈ AchievableCosts (subgame F rows cols)
    from ⟨Q, rfl, hQ⟩)
  have hD' : D (subgame F rows cols) ≤ child.cost := by
    simpa only [Q, Protocol.cost_restrictSub] using hD
  have hb := ProtocolFrontier.node_residual_budget P r retained hC hcost hp
  rw [hnode, Protocol.cost] at hb
  have hc : child.cost ≤ max lo.cost hi.cost := by
    cases bit <;> simp [child]
  change D (subgame F rows cols) + p.length + 1 ≤ C + r - 1
  omega

/-- First-Bob receiving capacity follows from the packet lower bound on an
actual Bob child. The extra queried bit makes its contradiction strict. -/
theorem firstBob_receiving_bound (P : Protocol X Y Bool) (r C m : ℕ)
    (retained additional : Finset X) (columns : Finset Y) (F : X → Y → Bool)
    (hP : ∀ x ∈ retained, ∀ y ∈ columns, P.eval x y = F x y)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    (origin : X → Coord) (J : Finset Coord) (p : List Bool)
    (hp : p ∈ ProtocolFrontier.nodes P r retained) (hdepth : p.length < r)
    (b : Y → Bool) (lo hi : Protocol X Y Bool)
    (hnode : descend (completeNoBob r P) p = .bNode b lo hi) (capacity : ℚ)
    (hpacket : capacity ≤ GlobalCount.mass m
      (GlobalCount.received additional origin (ProtocolFrontier.rowStop r (completeNoBob r P)) J p) →
      ∃ bit : Bool, C + (r - p.length) - 1 ≤ D (subgame F
        (rowsAt retained (ProtocolFrontier.rowStop r (completeNoBob r P)) p)
        (columns.filter fun y => b y = bit))) :
    GlobalCount.mass m
      (GlobalCount.received additional origin (ProtocolFrontier.rowStop r (completeNoBob r P)) J p) <
        capacity := by
  by_contra hn
  obtain ⟨bit, hlower⟩ := hpacket (le_of_not_gt hn)
  have hupper := bob_child_restriction_budget P r C retained columns F hP hC hcost p hp
    b lo hi hnode bit
  omega

end EthInapproximability.CurrentPaper.RoutedClosure
