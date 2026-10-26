import EthInapproximability.CurrentPaper.IndexedProjection
import EthInapproximability.CurrentPaper.ProtocolFrontier
import EthInapproximability.CurrentPaper.OuterWeightCount

/-!
# Actual support routing in the outer interlace

Source: v8 `A-stage4-details.tex`, proof of
`lem:paper-terminal-two-stream`, paragraph "The outer interlace".

The routing below reads the Alice predicates of an actual protocol. Supports
are finite sets of actual inputs, and their ordinary-coordinate projections
are retained explicitly. A joint support splits only when BOTH projections
pass the next threshold. Otherwise its small child is discarded in its
entirety; a fibre count controls the actual joint mass lost.

The generic local communication tests are deliberately separate from this
finite routing mechanism. No protocol-order or frontier certificate is used
to define the routing.
-/

noncomputable section
open scoped BigOperators Classical
open Workspace.Types.Protocol

namespace EthInapproximability.CurrentPaper.OuterRouting

open EthInapproximability.ParameterizedNP.DenseWeightedCount

variable {X Y A B : Type*} [DecidableEq X] [DecidableEq A]

/-- Actual rows on one side of an Alice query. -/
def child (R : Finset X) (a : X → Bool) (bit : Bool) : Finset X :=
  R.filter (fun x => a x = bit)

omit [DecidableEq X] in
@[simp] theorem mem_child {R : Finset X} {a : X → Bool} {bit : Bool} {x : X} :
    x ∈ child R a bit ↔ x ∈ R ∧ a x = bit := Finset.mem_filter

omit [DecidableEq X] in
theorem child_subset (R : Finset X) (a : X → Bool) (bit : Bool) :
    child R a bit ⊆ R := Finset.filter_subset _ _

theorem child_union (R : Finset X) (a : X → Bool) :
    child R a false ∪ child R a true = R := by
  ext x
  cases hx : a x <;> simp [child, hx]

/-- Projection sizes need not add: the same ordinary label may occur in both
children. The inequality in the required direction still holds. -/
theorem projection_card_le (R : Finset X) (a : X → Bool) (π : X → A) :
    (R.image π).card ≤ ((child R a false).image π).card +
      ((child R a true).image π).card := by
  calc
    _ = (((child R a false).image π) ∪ ((child R a true).image π)).card := by
      rw [← Finset.image_union, child_union]
    _ ≤ _ := Finset.card_union_le _ _

/-- Choose one heavier ordinary projection; ties go to the false child. -/
def heavy (R : Finset X) (a : X → Bool) (π : X → A) : Bool :=
  if ((child R a false).image π).card < ((child R a true).image π).card
    then true else false

theorem projection_heavy (R : Finset X) (a : X → Bool) (π : X → A) :
    (R.image π).card ≤ 2 * ((child R a (heavy R a π)).image π).card := by
  have h := projection_card_le R a π
  unfold heavy
  split_ifs with hlt <;> simp_all <;> omega

theorem light_projection_le (R : Finset X) (a : X → Bool) (π : X → A) :
    ((child R a (!(heavy R a π))).image π).card ≤
      ((child R a (heavy R a π)).image π).card := by
  unfold heavy
  split_ifs with hlt <;> simp_all <;> omega

/-- A routed marker retains its original bin label. `attached` means that its
support is still the joint ordinary/additional support, not separate witnesses. -/
structure Marker (X B : Type*) where
  bin : B
  support : Finset X
  attached : Bool

def Marker.width (π : B → X → A) (m : Marker X B) : ℕ :=
  (m.support.image (π m.bin)).card

def Marker.cut (m : Marker X B) (a : X → Bool) (bit attached : Bool) : Marker X B :=
  ⟨m.bin, child m.support a bit, attached⟩

/-- The split test inspects both ACTUAL query children. -/
def splits (π : B → X → A) (threshold : ℕ) (a : X → Bool) (m : Marker X B) : Prop :=
  m.attached = true ∧
    threshold ≤ ((child m.support a false).image (π m.bin)).card ∧
    threshold ≤ ((child m.support a true).image (π m.bin)).card

/-- At most one descendant of each original marker is sent to a given child.
A split sends one ordinary marker to EACH child. -/
def route (π : B → X → A) (threshold : ℕ) (a : X → Bool)
    (m : Marker X B) (bit : Bool) : Option (Marker X B) :=
  if splits π threshold a m then some (m.cut a bit false)
  else if bit = heavy m.support a (π m.bin) then some (m.cut a bit m.attached)
  else none

theorem route_support {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {m m' : Marker X B} {bit : Bool} (h : route π threshold a m bit = some m') :
    m'.bin = m.bin ∧ m'.support = child m.support a bit := by
  unfold route at h
  split_ifs at h <;> simp only [Option.some.injEq] at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩

theorem route_floor {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {m m' : Marker X B} {bit : Bool}
    (hfloor : 2 * threshold ≤ m.width π)
    (h : route π threshold a m bit = some m') : threshold ≤ m'.width π := by
  unfold route at h
  split_ifs at h with hs hb
  · cases h
    cases bit
    · exact hs.2.1
    · exact hs.2.2
  · cases h
    have hh := projection_heavy m.support a (π m.bin)
    simp only [Marker.width, Marker.cut] at *
    rw [hb]
    omega

/-- Real-density version: this avoids strengthening a ceiling-rounded row
threshold by an accidental extra input. -/
theorem route_floor_real {π : B → X → A} {T : ℝ} {a : X → Bool}
    {m m' : Marker X B} {bit : Bool}
    (hfloor : 2 * T ≤ (m.width π : ℝ))
    (h : route π ⌈T⌉₊ a m bit = some m') : T ≤ (m'.width π : ℝ) := by
  unfold route at h
  split_ifs at h with hs hb
  · cases h
    have hh : ⌈T⌉₊ ≤ (m.cut a bit false).width π := by
      cases bit
      · exact hs.2.1
      · exact hs.2.2
    exact (Nat.le_ceil T).trans (by exact_mod_cast hh)
  · cases h
    have hh : (m.width π : ℝ) ≤
        2 * (((child m.support a (heavy m.support a (π m.bin))).image (π m.bin)).card : ℝ) := by
      exact_mod_cast projection_heavy m.support a (π m.bin)
    simp only [Marker.width, Marker.cut]
    rw [hb]
    linarith
theorem unsplit_light_small {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {m : Marker X B} (ha : m.attached = true) (hs : ¬splits π threshold a m) :
    ((child m.support a (!(heavy m.support a (π m.bin)))).image (π m.bin)).card <
      threshold := by
  have hn : ¬(threshold ≤ ((child m.support a false).image (π m.bin)).card ∧
      threshold ≤ ((child m.support a true).image (π m.bin)).card) := by
    exact fun h => hs ⟨ha, h⟩
  have hh := light_projection_le m.support a (π m.bin)
  cases hb : heavy m.support a (π m.bin) <;> simp only [hb, Bool.not_false,
    Bool.not_true] at * <;> omega

/-- This bounds lost JOINT inputs, not just their projected labels. -/
theorem unsplit_joint_loss {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {m : Marker X B} {N : ℝ} (hN : 0 < N)
    (hfibre : ∀ c, ((m.support.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N)
    (ha : m.attached = true) (hs : ¬splits π threshold a m) :
    ((child m.support a (!(heavy m.support a (π m.bin)))).card : ℝ) < threshold * N := by
  let L := child m.support a (!(heavy m.support a (π m.bin)))
  have hf : ∀ c, ((L.filter (fun x => π m.bin x = c)).card : ℝ) ≤ N := by
    intro c
    apply le_trans ?_ (hfibre c)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (child_subset m.support a _))
  have hb := IndexedProjection.card_le_image_card_mul L (π m.bin) hf
  have hl : ((L.image (π m.bin)).card : ℝ) < threshold := by
    exact_mod_cast unsplit_light_small ha hs
  exact hb.trans_lt (mul_lt_mul_of_pos_right hl hN)

/-- Marker weight: three units for every ordinary marker, plus one for an
attached additional component. -/
def markerWeight (m : Marker X B) : ℕ := 3 + if m.attached then 1 else 0

def weight (ms : List (Marker X B)) : ℕ := (ms.map markerWeight).sum

@[simp] theorem weight_nil : weight ([] : List (Marker X B)) = 0 := rfl
@[simp] theorem weight_cons (m : Marker X B) (ms : List (Marker X B)) :
    weight (m :: ms) = markerWeight m + weight ms := rfl
@[simp] theorem weight_append (ms ns : List (Marker X B)) :
    weight (ms ++ ns) = weight ms + weight ns := by simp [weight]

/-- The children are computed from each marker's actual query split. -/
def routeAll (π : B → X → A) (threshold : ℕ) (a : X → Bool)
    (bit : Bool) : List (Marker X B) → List (Marker X B)
  | [] => []
  | m :: ms => (route π threshold a m bit).toList ++ routeAll π threshold a bit ms

theorem route_weight (π : B → X → A) (threshold : ℕ) (a : X → Bool)
    (m : Marker X B) :
    markerWeight m ≤ weight (route π threshold a m false).toList +
      weight (route π threshold a m true).toList := by
  unfold route
  by_cases hs : splits π threshold a m
  · simp [hs, weight, markerWeight, Marker.cut, hs.1]
  · simp only [hs, ↓reduceIte]
    cases hb : heavy m.support a (π m.bin) <;>
      simp [hb, weight, markerWeight, Marker.cut]

/-- Splitting adds weight; no marker weight disappears on a routing step. -/
theorem routeAll_weight (π : B → X → A) (threshold : ℕ) (a : X → Bool)
    (ms : List (Marker X B)) :
    weight ms ≤ weight (routeAll π threshold a false ms) +
      weight (routeAll π threshold a true ms) := by
  induction ms with
  | nil => simp [routeAll]
  | cons m ms ih =>
    have hm := route_weight π threshold a m
    simp only [routeAll, weight_cons, weight_append]
    omega

/-- Every routed marker has an actual parent and exact query-child support. -/
theorem mem_routeAll {π : B → X → A} {threshold : ℕ} {a : X → Bool}
    {bit : Bool} {ms : List (Marker X B)} {m' : Marker X B}
    (h : m' ∈ routeAll π threshold a bit ms) :
    ∃ m ∈ ms, route π threshold a m bit = some m' := by
  induction ms with
  | nil => simp [routeAll] at h
  | cons m ms ih =>
    rcases List.mem_append.mp h with h | h
    · exact ⟨m, List.mem_cons_self, by simpa using h⟩
    · obtain ⟨m₀, hm₀, hr⟩ := ih h
      exact ⟨m₀, List.mem_cons_of_mem _ hm₀, hr⟩

structure Stop (X B : Type*) where
  path : List Bool
  markers : List (Marker X B)

def Stop.prepend (bit : Bool) (s : Stop X B) : Stop X B :=
  ⟨bit :: s.path, s.markers⟩

/-- The complete routing frontier of this actual protocol. It does not stop
early at isolated bins. The downstream local lower bounds must exclude all
leaves and cutoff nodes before a first-Bob conclusion is drawn. -/
def frontier (π : B → X → A) (threshold : ℕ → ℕ) :
    ℕ → ℕ → Protocol X Y Bool → List (Marker X B) → List (Stop X B)
  | 0, _, _, ms => [⟨[], ms⟩]
  | _ + 1, _, .leaf _, ms => [⟨[], ms⟩]
  | _ + 1, _, .bNode _ _ _, ms => [⟨[], ms⟩]
  | n + 1, d, .aNode a l h, ms =>
      (frontier π threshold n (d + 1) l (routeAll π (threshold (d + 1)) a false ms)).map
          (Stop.prepend false) ++
      (frontier π threshold n (d + 1) h (routeAll π (threshold (d + 1)) a true ms)).map
          (Stop.prepend true)

/-- Total marker weight is proved from the constructed routing tree. -/
theorem frontier_weight (π : B → X → A) (threshold : ℕ → ℕ)
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B)) :
    weight ms ≤ ((frontier π threshold n d P ms).map (fun s => weight s.markers)).sum := by
  induction n generalizing d P ms with
  | zero => simp [frontier]
  | succ n ih =>
    cases P with
    | leaf _ => simp [frontier]
    | bNode _ _ _ => simp [frontier]
    | aNode a l h =>
      have hstep := routeAll_weight π (threshold (d + 1)) a ms
      have hl := ih (d + 1) l (routeAll π (threshold (d + 1)) a false ms)
      have hr := ih (d + 1) h (routeAll π (threshold (d + 1)) a true ms)
      simp only [frontier, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, Stop.prepend]
      omega

/-- Kraft capacity is proved directly on the actual binary routing tree,
including empty-marker branches. No prefix-free family is a hypothesis. -/
theorem frontier_kraft (π : B → X → A) (threshold : ℕ → ℕ)
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B)) :
    ((frontier π threshold n d P ms).map (fun s => 2 ^ (n - s.path.length))).sum ≤ 2 ^ n := by
  induction n generalizing d P ms with
  | zero => simp [frontier]
  | succ n ih =>
    cases P with
    | leaf _ => simp [frontier]
    | bNode _ _ _ => simp [frontier]
    | aNode a l h =>
      have hl := ih (d + 1) l (routeAll π (threshold (d + 1)) a false ms)
      have hr := ih (d + 1) h (routeAll π (threshold (d + 1)) a true ms)
      simp only [frontier, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, Stop.prepend, List.length_cons, Nat.add_sub_add_right,
        pow_succ]
      omega

/-- Each final support traces back to one original support. On every input
in it, the residual protocol is the ACTUAL executed suffix, for all columns.
No fresh row-dependent choice of a column or protocol is made. -/
theorem frontier_execution (π : B → X → A) (threshold : ℕ → ℕ)
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B))
    {s : Stop X B} (hs : s ∈ frontier π threshold n d P ms)
    {m : Marker X B} (hm : m ∈ s.markers) :
    ∃ m₀ ∈ ms, m.bin = m₀.bin ∧ m.support ⊆ m₀.support ∧
      ∀ x ∈ m.support, ∀ y, (descend P s.path).eval x y = P.eval x y := by
  induction n generalizing d P ms s m with
  | zero =>
    simp only [frontier, List.mem_singleton] at hs
    cases hs
    exact ⟨m, hm, rfl, Finset.Subset.refl _, by intros; rfl⟩
  | succ n ih =>
    cases P with
    | leaf z =>
      simp only [frontier, List.mem_singleton] at hs
      cases hs
      exact ⟨m, hm, rfl, Finset.Subset.refl _, by intros; rfl⟩
    | bNode b l h =>
      simp only [frontier, List.mem_singleton] at hs
      cases hs
      exact ⟨m, hm, rfl, Finset.Subset.refl _, by intros; rfl⟩
    | aNode a l h =>
      simp only [frontier, List.mem_append, List.mem_map] at hs
      rcases hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
      · obtain ⟨m₁, hm₁, hbin, hsub, heval⟩ := ih (d + 1) l _ hs' hm
        obtain ⟨m₀, hm₀, hroute⟩ := mem_routeAll hm₁
        obtain ⟨hbin₀, hsupport⟩ := route_support hroute
        refine ⟨m₀, hm₀, hbin.trans hbin₀, ?_, ?_⟩
        · exact hsub.trans (by rw [hsupport]; exact child_subset _ _ _)
        · intro x hx y
          have hax := (mem_child.mp (hsupport ▸ hsub hx)).2
          simpa [Stop.prepend, descend, descendStep, Protocol.eval, hax] using heval x hx y
      · obtain ⟨m₁, hm₁, hbin, hsub, heval⟩ := ih (d + 1) h _ hs' hm
        obtain ⟨m₀, hm₀, hroute⟩ := mem_routeAll hm₁
        obtain ⟨hbin₀, hsupport⟩ := route_support hroute
        refine ⟨m₀, hm₀, hbin.trans hbin₀, ?_, ?_⟩
        · exact hsub.trans (by rw [hsupport]; exact child_subset _ _ _)
        · intro x hx y
          have hax := (mem_child.mp (hsupport ▸ hsub hx)).2
          simpa [Stop.prepend, descend, descendStep, Protocol.eval, hax] using heval x hx y

/-- Every actual routed marker retains the appropriate real-valued row
density. The ceiling is used only by the finite comparison deciding a split. -/
theorem frontier_floor (π : B → X → A) (T : ℕ → ℝ)
    (hT : ∀ d, T d = 2 * T (d + 1))
    (n d : ℕ) (P : Protocol X Y Bool) (ms : List (Marker X B))
    (hfloor : ∀ m ∈ ms, T d ≤ (m.width π : ℝ))
    {s : Stop X B} (hs : s ∈ frontier π (fun d => ⌈T d⌉₊) n d P ms)
    {m : Marker X B} (hm : m ∈ s.markers) :
    T (d + s.path.length) ≤ (m.width π : ℝ) := by
  induction n generalizing d P ms s m with
  | zero =>
    simp only [frontier, List.mem_singleton] at hs
    cases hs
    simpa using hfloor m hm
  | succ n ih =>
    cases P with
    | leaf z =>
      simp only [frontier, List.mem_singleton] at hs
      cases hs
      simpa using hfloor m hm
    | bNode b l h =>
      simp only [frontier, List.mem_singleton] at hs
      cases hs
      simpa using hfloor m hm
    | aNode a l h =>
      have hchild (bit : Bool) :
          ∀ m' ∈ routeAll π ⌈T (d + 1)⌉₊ a bit ms, T (d + 1) ≤ (m'.width π : ℝ) := by
        intro m' hm'
        obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm'
        apply route_floor_real (m := m₀) ?_ hr
        rw [← hT]
        exact hfloor m₀ hm₀
      simp only [frontier, List.mem_append, List.mem_map] at hs
      rcases hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
      · have hh := ih (d + 1) l _ (hchild false) hs' hm
        simpa [Stop.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      · have hh := ih (d + 1) h _ (hchild true) hs' hm
        simpa [Stop.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

end EthInapproximability.CurrentPaper.OuterRouting
