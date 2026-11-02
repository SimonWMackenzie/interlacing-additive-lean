import EthInapproximability.CurrentPaper.OuterRouting
import EthInapproximability.CurrentPaper.OuterLoss

/-!
# Loss of an attached marker in the constructed outer frontier

Source: v8 `A-stage4-details.tex`, proof of
`lem:paper-terminal-two-stream`, paragraph "The outer interlace".

This closes the geometric-loss input for the actual routing construction.
An attached marker at a frontier node has never split. At each query its
discarded projection has size strictly below the real next threshold; the
fibre bound turns that into a bound on actual discarded joint inputs.
-/

noncomputable section
open scoped Classical
open Workspace.Types.Protocol

namespace EthInapproximability.CurrentPaper.OuterAttachedLoss

open OuterRouting

variable {X Y A B : Type*} [DecidableEq X] [DecidableEq A]

/-- The actual Boolean query children partition the finite support. -/
theorem child_card_add (R : Finset X) (a : X → Bool) (bit : Bool) :
    (child R a bit).card + (child R a (!bit)).card = R.card := by
  have hd : Disjoint (child R a bit) (child R a (!bit)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_child.mp hx).2
    have hy' := (mem_child.mp hy).2
    cases bit <;> simp_all
  have hu : child R a bit ∪ child R a (!bit) = R := by
    cases bit
    · exact child_union R a
    · simpa [Finset.union_comm] using child_union R a
  rw [← Finset.card_union_of_disjoint hd, hu]

/-- An attached output can only come from an attached, unsplit parent and
the heavier child selected by the actual projection comparison. -/
theorem attached_route {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {m m' : Marker X B} {bit : Bool}
    (hr : route π threshold a m bit = some m') (ha : m'.attached = true) :
    m.attached = true ∧ ¬splits π threshold a m ∧
      bit = heavy m.support a (π m.bin) := by
  unfold route at hr
  split_ifs at hr with hs hb
  · cases hr
    simp [Marker.cut] at ha
  · cases hr
    exact ⟨ha, hs, hb⟩

/-- A ceiling-rounded split test still gives a strict bound by the REAL
threshold, not by a rounded-up threshold. -/
theorem attached_step_loss {π : B → X → A} {T N : ℝ} {a : X → Bool}
    {m m' : Marker X B} {bit : Bool} (hN : 0 < N)
    (hfibre : ∀ c, ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N)
    (hr : route π ⌈T⌉₊ a m bit = some m') (ha : m'.attached = true) :
    (m.support.card : ℝ) - m'.support.card < N * T := by
  obtain ⟨hattached, hnosplit, hheavy⟩ := attached_route hr ha
  obtain ⟨_, hsupport⟩ := route_support hr
  let L := child m.support a (!(heavy m.support a (π m.bin)))
  have hf : ∀ c, ((L.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N := by
    intro c
    apply le_trans ?_ (hfibre c)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (child_subset m.support a _))
  have hcard := IndexedProjection.card_le_image_card_mul L (π m.bin) hf
  have hwidth : ((L.image (π m.bin)).card : ℝ) < T :=
    Nat.lt_ceil.mp (unsplit_light_small hattached hnosplit)
  have hloss : (L.card : ℝ) < N * T := by
    calc
      _ ≤ ((L.image (π m.bin)).card : ℝ) * N := hcard
      _ < T * N := mul_lt_mul_of_pos_right hwidth hN
      _ = N * T := mul_comm _ _
  have hpartition := child_card_add m.support a (heavy m.support a (π m.bin))
  have hpartitionR :
      (((child m.support a (heavy m.support a (π m.bin))).card : ℕ) : ℝ) +
        L.card = m.support.card := by exact_mod_cast hpartition
  rw [hsupport, hheavy]
  linarith

/-- Fibre bounds remain valid for every actual routed support. -/
theorem routeAll_fibre_bound {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {ms : List (Marker X B)} {N : ℝ}
    (hfibre : ∀ m ∈ ms, ∀ c,
      ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N)
    (bit : Bool) :
    ∀ m ∈ routeAll π threshold a bit ms, ∀ c,
      ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N := by
  intro m hm c
  obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
  obtain ⟨hbin, hsupport⟩ := route_support hr
  rw [hbin, hsupport]
  apply le_trans ?_ (hfibre m₀ hm₀ c)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (child_subset m₀.support a bit))

/-- Every attached marker in the constructed frontier comes from an
initially attached marker. The ACTUAL support loss is bounded by the finite
dyadic budget; neither a support trajectory nor its losses are hypotheses. -/
theorem frontier_attached_loss (π : B → X → A) (T : ℕ → ℝ) (N : ℝ)
    (hN : 0 < N) (hhalve : ∀ d, T d = 2 * T (d + 1))
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B))
    (hfibre : ∀ m ∈ ms, ∀ c,
      ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N)
    {s : Stop X B} (hs : s ∈ frontier π (fun k => ⌈T k⌉₊) n d P ms)
    {m : Marker X B} (hm : m ∈ s.markers) (ha : m.attached = true) :
    ∃ m₀ ∈ ms, m₀.attached = true ∧ m.bin = m₀.bin ∧
      m.support ⊆ m₀.support ∧
      (m₀.support.card : ℝ) - m.support.card ≤ N * (T d - T (d + s.path.length)) := by
  induction n generalizing d P ms s m with
  | zero =>
    simp only [OuterRouting.frontier, List.mem_singleton] at hs
    cases hs
    exact ⟨m, hm, ha, rfl, Finset.Subset.refl _, by simp⟩
  | succ n ih =>
    cases P with
    | leaf z =>
      simp only [OuterRouting.frontier, List.mem_singleton] at hs
      cases hs
      exact ⟨m, hm, ha, rfl, Finset.Subset.refl _, by simp⟩
    | bNode b l h =>
      simp only [OuterRouting.frontier, List.mem_singleton] at hs
      cases hs
      exact ⟨m, hm, ha, rfl, Finset.Subset.refl _, by simp⟩
    | aNode a l h =>
      simp only [OuterRouting.frontier, List.mem_append, List.mem_map] at hs
      rcases hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
      · obtain ⟨m₁, hm₁, ha₁, hbin, hsub, hloss⟩ :=
          ih (d + 1) l _ (routeAll_fibre_bound hfibre false) hs' hm ha
        obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm₁
        obtain ⟨hbin₀, hsupport⟩ := route_support hr
        have ha₀ := (attached_route hr ha₁).1
        have hstep := attached_step_loss hN (hfibre m₀ hm₀) hr ha₁
        refine ⟨m₀, hm₀, ha₀, hbin.trans hbin₀, ?_, ?_⟩
        · exact hsub.trans (by rw [hsupport]; exact child_subset _ _ _)
        · have hlen : d + (Stop.prepend false s').path.length = d + 1 + s'.path.length := by
            simp [Stop.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [hlen, hhalve d]
          nlinarith
      · obtain ⟨m₁, hm₁, ha₁, hbin, hsub, hloss⟩ :=
          ih (d + 1) h _ (routeAll_fibre_bound hfibre true) hs' hm ha
        obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm₁
        obtain ⟨hbin₀, hsupport⟩ := route_support hr
        have ha₀ := (attached_route hr ha₁).1
        have hstep := attached_step_loss hN (hfibre m₀ hm₀) hr ha₁
        refine ⟨m₀, hm₀, ha₀, hbin.trans hbin₀, ?_, ?_⟩
        · exact hsub.trans (by rw [hsupport]; exact child_subset _ _ _)
        · have hlen : d + (Stop.prepend true s').path.length = d + 1 + s'.path.length := by
            simp [Stop.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [hlen, hhalve d]
          nlinarith

/-- Positive dyadic thresholds make every finite attached route lose
strictly less than the entire initial loss budget. -/
theorem frontier_attached_loss_lt (π : B → X → A) (T : ℕ → ℝ) (N : ℝ)
    (hN : 0 < N) (hT : ∀ k, 0 < T k) (hhalve : ∀ k, T k = 2 * T (k + 1))
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B))
    (hfibre : ∀ m ∈ ms, ∀ c,
      ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N)
    {s : Stop X B} (hs : s ∈ frontier π (fun k => ⌈T k⌉₊) n d P ms)
    {m : Marker X B} (hm : m ∈ s.markers) (ha : m.attached = true) :
    ∃ m₀ ∈ ms, m₀.attached = true ∧ m.bin = m₀.bin ∧
      m.support ⊆ m₀.support ∧
      (m₀.support.card : ℝ) - m.support.card < N * T d := by
  obtain ⟨m₀, hm₀, ha₀, hbin, hsub, hloss⟩ :=
    frontier_attached_loss π T N hN hhalve n d P ms hfibre hs hm ha
  refine ⟨m₀, hm₀, ha₀, hbin, hsub, ?_⟩
  have hpositive := mul_pos hN (hT (d + s.path.length))
  nlinarith

end EthInapproximability.CurrentPaper.OuterAttachedLoss
