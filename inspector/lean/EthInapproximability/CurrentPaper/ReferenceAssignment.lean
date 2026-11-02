import EthInapproximability.CurrentPaper.ProtocolFrontier
import EthInapproximability.ParameterizedNP.FrontierIndexing
import EthInapproximability.CurrentPaper.ReferenceRouteLoss

/-!
# Reference supports in the complete stopping collection

Source: replacement v8, `A-stage4-details.tex`,
`clm:paper-global-assignment`. The routing used here is the actual branching
support routing of `FrontierIndexing`: threshold `2^k A0`, weight one until
the first split, then weight one half. Its conservation theorem is reused.
The stopping collection is the current paper's complete retained-row
collection, including nodes carrying no routed reference support.

Only the local communication exclusions (first-Bob weight and uniqueness
at a final node) are intended as inputs. Assignment and conservation are
not certificate fields or assumptions.
-/

namespace EthInapproximability.CurrentPaper.ReferenceAssignment

open scoped BigOperators
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open ProtocolFrontier
open ReferenceRouteLoss

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- A row lying in an Alice-only stopping rectangle actually executes to its
address. Thus a routed support cannot invent an unreachable frontier node. -/
theorem rowStop_eq_of_mem_aliceCols (r : ℕ) (P : Protocol X Y Z)
    (p : List Bool) (x : X) (ha : IsAlicePath P p)
    (hx : x ∈ aliceCols P p) (hlen : p.length ≤ r)
    (hs : IsBobNode (descend P p) ∨ p.length = r) : rowStop r P x = p := by
  induction p generalizing P r with
  | nil =>
    cases r with
    | zero => rfl
    | succ r =>
      rcases hs with hs | hs
      · cases P <;> simp_all [IsBobNode, descend, rowStop]
      · simp at hs
  | cons b p ih =>
    cases r with
    | zero => simp at hlen
    | succ r =>
      rcases ha with ⟨ha, hap⟩
      rcases ha with ⟨a, l, h, rfl⟩
      have hx' := (Finset.mem_inter.mp hx)
      have hab : a x = b := by
        simpa [aliceConstraint] using hx'.1
      have hp : p.length ≤ r := by simpa using hlen
      have hs' : IsBobNode (descend (descendStep (.aNode a l h) b) p) ∨
          p.length = r := by
        simpa [descend, descendStep] using hs
      have he := ih r (descendStep (.aNode a l h) b) hap hx'.2 hp hs'
      cases b <;> simp_all [rowStop, descendStep]

/-- Every genuinely routed reference node occurs in the all-row frontier.
The positive support threshold supplies an actual representative row. -/
theorem coordRoutes_subset_nodes {Coord : Type} [Fintype Coord]
    (P : Protocol X Y Z) (retained : Finset X) (R : Coord → Finset X)
    {A0 r : ℕ} (hA : 0 < A0)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hsub : ∀ i, R i ⊆ retained) (i : Coord) :
    coordRoutes (completeNoBob r P) R A0 r i ⊆ nodes P r retained := by
  intro p hp
  have hf := coordRoutes_rows_floor (P := completeNoBob r P) (hR i) hp
  have hpos : 0 < (rowsAt (completeNoBob r P) (R i) p).card := by
    apply lt_of_lt_of_le _ hf
    unfold refRowFloor
    positivity
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxr := (Finset.mem_inter.mp hx).1
  have hxa := (Finset.mem_inter.mp hx).2
  have hstop := frontierRoutes_stop (completedNoBob_completeNoBob P r)
    (mem_frontierRoutes_of_mem_coordRoutes hp)
  have hlen := coordRoutes_length_le (completedNoBob_completeNoBob P r) hp
  have hs : IsBobNode (descend (completeNoBob r P) p) ∨ p.length = r := by
    rcases hstop with hs | hs
    · exact Or.inl hs.2.1
    · exact Or.inr hs.2
  have he := rowStop_eq_of_mem_aliceCols r _ p x (coordRoutes_isAlicePath hp) hxa hlen hs
  rw [← he]
  exact destination_mem P r retained (hsub i hxr)

section Weights

variable {Coord : Type} [Fintype Coord]

/-- The actual total routed reference weight at a protocol address. -/
noncomputable def weightAt (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (p : List Bool) : ℝ :=
  ∑ i, if p ∈ coordRoutes P R A0 r i then (kindAlong P (R i) A0 r p).weight else 0

/-- Passing from the reference-only addresses to all retained-row stopping
addresses preserves all weight and adds zero-weight nodes. -/
theorem weight_conservation (P : Protocol X Y Z) (retained : Finset X)
    (R : Coord → Finset X) {A0 r : ℕ} (hA : 0 < A0)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hsub : ∀ i, R i ⊆ retained) :
    (Fintype.card Coord : ℝ) ≤
      ∑ p ∈ nodes P r retained, weightAt (completeNoBob r P) R A0 r p := by
  classical
  unfold weightAt
  rw [Finset.sum_comm]
  calc
    (Fintype.card Coord : ℝ) = ∑ _i : Coord, (1 : ℝ) := by simp
    _ ≤ ∑ i, ∑ p ∈ nodes P r retained,
        if p ∈ coordRoutes (completeNoBob r P) R A0 r i then
          (kindAlong (completeNoBob r P) (R i) A0 r p).weight else 0 := by
      apply Finset.sum_le_sum
      intro i _
      have hset := coordRoutes_subset_nodes P retained R hA hR hsub i
      have hs : (nodes P r retained).filter
          (fun p => p ∈ coordRoutes (completeNoBob r P) R A0 r i) =
          coordRoutes (completeNoBob r P) R A0 r i := by
        ext p
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hp => hset hp
      rw [← Finset.sum_filter, hs]
      exact one_le_sum_coordRoutes _ R A0 r i

/-- A final stopping address carrying an unsplit reference support. -/
noncomputable def assignedNodes (P : Protocol X Y Z) (retained : Finset X)
    (R : Coord → Finset X) (A0 r : ℕ) : Finset (List Bool) := by
  classical
  exact (nodes P r retained).filter fun p => p.length = r ∧
    ∃ i, p ∈ coordRoutes (completeNoBob r P) R A0 r i ∧
      kindAlong (completeNoBob r P) (R i) A0 r p = CertKind.clean

/-- Under the local two-support exclusion, a represented final node carries
exactly the weight of its single actual reference coordinate. -/
theorem weight_eq_of_unique (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (p : List Bool) (i : Coord)
    (hi : p ∈ coordRoutes P R A0 r i)
    (hu : ∀ j, p ∈ coordRoutes P R A0 r j → j = i) :
    weightAt P R A0 r p = (kindAlong P (R i) A0 r p).weight := by
  classical
  unfold weightAt
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    exact if_neg (fun hj => hji (hu j hj))
  · simp

/-- Assignment/counting from two local protocol exclusions. All objects in
the statement are computed from actual support routing and the complete
retained-row frontier; no mass array or assignment certificate is supplied. -/
theorem assigned_nodes_count (P : Protocol X Y Z) (retained : Finset X)
    (R : Coord → Finset X) {A0 r : ℕ} (hA : 0 < A0)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hsub : ∀ i, R i ⊆ retained) (e0 : ℝ)
    (hcoord : (2 : ℝ) ^ r - e0 ≤ Fintype.card Coord)
    (hbob : ∀ p ∈ nodes P r retained, p.length < r →
      weightAt (completeNoBob r P) R A0 r p ≤
        (9 / 16 : ℝ) * stoppingCapacity r p.length)
    (hterminal : ∀ p ∈ nodes P r retained, p.length = r →
      ∀ i j, p ∈ coordRoutes (completeNoBob r P) R A0 r i →
        p ∈ coordRoutes (completeNoBob r P) R A0 r j → i = j) :
    (2 : ℝ) ^ r - e0 / (1 - (9 / 16 : ℝ)) ≤
        (assignedNodes P retained R A0 r).card ∧
      (∑ p ∈ nodes P r retained \ assignedNodes P retained R A0 r,
        (stoppingCapacity r p.length : ℝ)) ≤
        (2 : ℝ) ^ r - (assignedNodes P retained R A0 r).card := by
  classical
  let F := nodes P r retained
  let B := assignedNodes P retained R A0 r
  let W := weightAt (completeNoBob r P) R A0 r
  let cap := fun p : List Bool => (stoppingCapacity r p.length : ℝ)
  have hBF : B ⊆ F := Finset.filter_subset _ _
  have hcapB : ∀ p ∈ B, cap p = 1 := by
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2.1
    simp [cap, stoppingCapacity, ht]
  have hWB : ∀ p ∈ B, W p = 1 := by
    intro p hp
    obtain ⟨hpF, ht, i, hi, hic⟩ := Finset.mem_filter.mp hp
    have hu := hterminal p hpF ht
    have he := weight_eq_of_unique (completeNoBob r P) R A0 r p i hi
      (fun j hj => hu j i hj hi)
    simpa [W, hic, CertKind.weight] using he
  have hWo : ∀ p ∈ F \ B, W p ≤ (9 / 16 : ℝ) * cap p := by
    intro p hp
    obtain ⟨hpF, hpB⟩ := Finset.mem_sdiff.mp hp
    have hlen : p.length ≤ r := by
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hpF
      rw [← hx]
      exact (rowStop_alice_length r _ x).2
    by_cases ht : p.length = r
    · have hc : cap p = 1 := by simp [cap, stoppingCapacity, ht]
      rw [hc, mul_one]
      by_cases hi : ∃ i, p ∈ coordRoutes (completeNoBob r P) R A0 r i
      · obtain ⟨i, hi⟩ := hi
        have hnc : kindAlong (completeNoBob r P) (R i) A0 r p ≠ CertKind.clean := by
          intro hc
          exact hpB (Finset.mem_filter.mpr ⟨hpF, ht, i, hi, hc⟩)
        have hk : kindAlong (completeNoBob r P) (R i) A0 r p = CertKind.low := by
          cases hh : kindAlong (completeNoBob r P) (R i) A0 r p <;> simp_all
        have he := weight_eq_of_unique (completeNoBob r P) R A0 r p i hi
          (fun j hj => hterminal p hpF ht j i hj hi)
        dsimp [W]
        rw [he, hk]
        norm_num [CertKind.weight]
      · have hz : W p = 0 := by
          simp only [W, weightAt]
          apply Finset.sum_eq_zero
          intro i _
          exact if_neg (fun hx => hi ⟨i, hx⟩)
        rw [hz]
        norm_num
    · exact hbob p hpF (lt_of_le_of_ne hlen ht)
  have hsumCapB : ∑ p ∈ B, cap p = (B.card : ℝ) := by
    rw [Finset.sum_congr rfl hcapB]
    simp
  have hsumWB : ∑ p ∈ B, W p = (B.card : ℝ) := by
    rw [Finset.sum_congr rfl hWB]
    simp
  have hsplitCap := Finset.sum_sdiff hBF (f := cap)
  have hsplitW := Finset.sum_sdiff hBF (f := W)
  have hk : (∑ p ∈ F, cap p) ≤ (2 : ℝ) ^ r := by
    dsimp [F, cap]
    exact_mod_cast nodes_kraft P r retained
  have hother : (∑ p ∈ F \ B, cap p) ≤ (2 : ℝ) ^ r - B.card := by
    rw [hsumCapB] at hsplitCap
    linarith
  have hcons := hcoord.trans (weight_conservation P retained R hA hR hsub)
  have hsumWo : (∑ p ∈ F \ B, W p) ≤
      (9 / 16 : ℝ) * ∑ p ∈ F \ B, cap p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hWo
  rw [hsumWB] at hsplitW
  constructor
  · change (2 : ℝ) ^ r - e0 / (1 - (9 / 16 : ℝ)) ≤ (B.card : ℝ)
    change (2 : ℝ) ^ r - e0 ≤ ∑ p ∈ F, W p at hcons
    norm_num at *
    linarith
  · exact hother

end Weights

section Coordinates

variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- The assigned terminal addresses correspond to distinct original
coordinates, not merely to abstract certificates. The unsplit-routing theorem
gives uniqueness even before the local terminal collision bound is used. -/
theorem exists_coordinate_assignment (P : Protocol X Y Z) (retained : Finset X)
    (R : Coord → Finset X) {A0 r : ℕ} (hr : 0 < r) :
    ∃ (J : Finset Coord) (owner : Coord → List Bool),
      J.card = (assignedNodes P retained R A0 r).card ∧
      Set.InjOn owner J ∧
      (∀ i ∈ J, owner i ∈ assignedNodes P retained R A0 r ∧
        owner i ∈ coordRoutes (completeNoBob r P) R A0 r i ∧
        kindAlong (completeNoBob r P) (R i) A0 r (owner i) = CertKind.clean ∧
        ((R i) \ rowsAt (completeNoBob r P) (R i) (owner i)).card <
          (2 ^ r - 1) * A0) ∧
      J.image owner = assignedNodes P retained R A0 r := by
  classical
  let B := assignedNodes P retained R A0 r
  have hex (p : B) : ∃ i, p.val ∈ coordRoutes (completeNoBob r P) R A0 r i ∧
      kindAlong (completeNoBob r P) (R i) A0 r p.val = CertKind.clean :=
    (Finset.mem_filter.mp p.property).2.2
  let g : B → Coord := fun p => Classical.choose (hex p)
  have hg (p : B) : p.val ∈ coordRoutes (completeNoBob r P) R A0 r (g p) ∧
      kindAlong (completeNoBob r P) (R (g p)) A0 r p.val = CertKind.clean :=
    Classical.choose_spec (hex p)
  have hinjg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    have hq := hg q
    rw [← hpq] at hq
    exact (coordRoutes_clean_unique (hg p).1 (hg p).2 hq.1).symm
  let J : Finset Coord := Finset.univ.image g
  have hi (i : Coord) (h : i ∈ J) : ∃ p : B, g p = i := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    exact ⟨p, hp⟩
  let owner : Coord → List Bool := fun i =>
    if h : i ∈ J then (Classical.choose (hi i h)).val else []
  have ho (i : Coord) (h : i ∈ J) :
      owner i ∈ B ∧ owner i ∈ coordRoutes (completeNoBob r P) R A0 r i ∧
        kindAlong (completeNoBob r P) (R i) A0 r (owner i) = CertKind.clean := by
    have he := Classical.choose_spec (hi i h)
    have hp := hg (Classical.choose (hi i h))
    rw [he] at hp
    simp only [owner, dif_pos h]
    exact ⟨(Classical.choose (hi i h)).property, hp⟩
  have howner (p : B) : owner (g p) = p.val := by
    have hmem : g p ∈ J := Finset.mem_image_of_mem g (Finset.mem_univ p)
    have hc := Classical.choose_spec (hi (g p) hmem)
    have he := hinjg hc
    simp only [owner, dif_pos hmem, he]
  refine ⟨J, owner, ?_, ?_, ?_, ?_⟩
  · dsimp [J]
    rw [Finset.card_image_of_injective _ hinjg]
    simp [B]
  · intro i hi' j hj' he
    let p := Classical.choose (hi i hi')
    let q := Classical.choose (hi j hj')
    have hp : g p = i := Classical.choose_spec (hi i hi')
    have hq : g q = j := Classical.choose_spec (hi j hj')
    have he' : p.val = q.val := by
      calc
        p.val = owner (g p) := (howner p).symm
        _ = owner i := congrArg owner hp
        _ = owner j := he
        _ = owner (g q) := congrArg owner hq.symm
        _ = q.val := howner q
    have hpq : p = q := Subtype.ext he'
    rw [← hp, ← hq, hpq]
  · intro i hi'
    have h := ho i hi'
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    exact coordRoutes_clean_loss_lt h.2.1 h.2.2
      (Finset.mem_filter.mp h.1).2.1 hr
  · apply Finset.Subset.antisymm
    · intro p hp
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hp
      exact (ho i hi').1
    · intro p hp
      let pp : B := ⟨p, hp⟩
      exact Finset.mem_image.mpr ⟨g pp,
        Finset.mem_image_of_mem g (Finset.mem_univ pp), howner pp⟩

end Coordinates

/-- The same strict loss statement for actual protocol destinations, not an
abstract support count. -/
theorem routed_terminal_loss {Coord : Type} (P : Protocol X Y Z)
    (R : Coord → Finset X) {A0 r : ℕ} {i : Coord} {p : List Bool}
    (hp : p ∈ coordRoutes (completeNoBob r P) R A0 r i)
    (hc : kindAlong (completeNoBob r P) (R i) A0 r p = CertKind.clean)
    (ht : p.length = r) (hr : 0 < r) :
    ((R i).filter fun x => rowStop r (completeNoBob r P) x ≠ p).card <
      (2 ^ r - 1) * A0 := by
  have hsub : (R i).filter (fun x => rowStop r (completeNoBob r P) x ≠ p) ⊆
      R i \ rowsAt (completeNoBob r P) (R i) p := by
    intro x hx
    obtain ⟨hxR, hxne⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨hxR, ?_⟩
    intro hxa
    apply hxne
    exact rowStop_eq_of_mem_aliceCols r _ p x (coordRoutes_isAlicePath hp)
      (Finset.mem_inter.mp hxa).2 ht.le (Or.inr ht)
  exact (Finset.card_le_card hsub).trans_lt (coordRoutes_clean_loss_lt hp hc ht hr)

/-- `clm:paper-global-assignment`, with the two local communication exclusions
left visible. `J`, its distinct actual terminal rectangles, their losses, and
the capacity of ALL unassigned stopping nodes are derived.

Instantiate `Coord` by the coordinates outside the exceptional cover and
`hcoord` by their actual finite cardinality. -/
theorem global_assignment {Coord : Type} [Fintype Coord] [DecidableEq Coord]
    (P : Protocol X Y Z) (retained : Finset X) (R : Coord → Finset X)
    {A0 r : ℕ} (hA : 0 < A0) (hr : 0 < r)
    (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    (hsub : ∀ i, R i ⊆ retained) (e0 : ℝ)
    (hcoord : (2 : ℝ) ^ r - e0 ≤ Fintype.card Coord)
    (hbob : ∀ p ∈ nodes P r retained, p.length < r →
      weightAt (completeNoBob r P) R A0 r p ≤
        (9 / 16 : ℝ) * stoppingCapacity r p.length)
    (hterminal : ∀ p ∈ nodes P r retained, p.length = r →
      ∀ i j, p ∈ coordRoutes (completeNoBob r P) R A0 r i →
        p ∈ coordRoutes (completeNoBob r P) R A0 r j → i = j) :
    ∃ (J : Finset Coord) (owner : Coord → List Bool),
      Set.InjOn owner J ∧
      (∀ i ∈ J, owner i ∈ nodes P r retained ∧ (owner i).length = r ∧
        owner i ∈ coordRoutes (completeNoBob r P) R A0 r i ∧
        kindAlong (completeNoBob r P) (R i) A0 r (owner i) = CertKind.clean ∧
        ((R i).filter fun x => rowStop r (completeNoBob r P) x ≠ owner i).card <
          (2 ^ r - 1) * A0) ∧
      ((2 : ℝ) ^ r - e0 / (1 - (9 / 16 : ℝ)) ≤ (J.card : ℝ)) ∧
      ((∑ p ∈ nodes P r retained \ J.image owner,
          (stoppingCapacity r p.length : ℝ)) ≤ (2 : ℝ) ^ r - J.card) ∧
      ((2 : ℝ) ^ r - J.card ≤ e0 / (1 - (9 / 16 : ℝ))) := by
  classical
  obtain ⟨J, owner, hcard, hinj, hown, himage⟩ :=
    exists_coordinate_assignment P retained R hr
  have hcount := assigned_nodes_count P retained R hA hR hsub e0 hcoord hbob hterminal
  rw [← hcard] at hcount
  refine ⟨J, owner, hinj, ?_, hcount.1, ?_, ?_⟩
  · intro i hi
    have h := hown i hi
    have hp := Finset.mem_filter.mp h.1
    exact ⟨hp.1, hp.2.1, h.2.1, h.2.2.1,
      routed_terminal_loss P R h.2.1 h.2.2.1 hp.2.1 hr⟩
  · rw [himage]
    exact hcount.2
  · linarith [hcount.1]

end EthInapproximability.CurrentPaper.ReferenceAssignment
