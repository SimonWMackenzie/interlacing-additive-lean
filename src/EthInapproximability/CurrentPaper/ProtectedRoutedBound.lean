import EthInapproximability.CurrentPaper.TerminalOuterBound
import EthInapproximability.CurrentPaper.ProtectedIndexedLadder

/-!
# The protected Stage--4 residual protocol bound

Source: frozen replacement v8, `A-stage4-details.tex`,
`lem:paper-protected-routed-closure` (the original Bob-only suffix).

We transpose the residual protocol so that its diagonal inputs are Alice's
inputs. Marker supports remain actual inputs of that protocol. Ordinary
entries use one fixed indexed family; attached entries use fixed graph-row
sections and a regular coordinate quotient of the same diagonal labels.
-/

noncomputable section
open scoped Classical BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.UpperBound

namespace EthInapproximability.CurrentPaper.ProtectedRoutedBound

open OuterRouting JointTransfer TerminalOuterBound
open EthInapproximability.ParameterizedNP.TerminalStateRealization

section Graph

variable {A U V Z W : Type*} [Fintype A] [Fintype U] [Fintype V]
  [Nonempty A] [DecidableEq A] [DecidableEq V]

/-- A graph witness remains a literal restriction after routing its actual
diagonal inputs. The only complexity premise is the source's original
`q1+3`-copy profile, not a lower bound on a routed protocol. -/
theorem graph_protocol_lower (g : U → V → Bool) {v H d : ℕ} {xcap : ℝ}
    (hprofile : H + 1 ≤ Dfamily (interlaceFun g v)
      (bracketGE U V v xcap (1 / 2)))
    (rows : Finset (Fin v × U))
    (hrows : IsEquipartitionedGE rows Finset.univ
      ⌈(Fintype.card U : ℝ) * xcap⌉₊)
    (tuple : A → Fin v → V) (hreg : RegularOn Finset.univ tuple d) (hd : 0 < d)
    (rowMap : (Fin v × U) → W) (P : Protocol Z W Bool)
    (R : Finset Z) (π : Z → A) (hinj : Set.InjOn π ↑R)
    (hmass : (1 / 2 : ℝ) * Fintype.card A ≤ (R.card : ℝ))
    (heval : ∀ z ∈ R, ∀ r ∈ rows,
      P.eval z (rowMap r) = interlaceFun g v r (tuple (π z))) :
    H + 1 ≤ P.cost := by
  classical
  let C := R.image (fun z => tuple (π z))
  have hcard : (R.image π).card = R.card := Finset.card_image_iff.mpr hinj
  have hquot := regularOn_density_transfer hreg hd (Finset.subset_univ (R.image π))
  rw [Finset.card_univ, hcard] at hquot
  have himage : (R.image π).image tuple = C := by simp [C, Finset.image_image, Function.comp_def]
  rw [himage] at hquot
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hdens : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ v ≤ C.card := by
    have h := ((le_div_iff₀ hA).mpr hmass).trans hquot
    have hV : (0 : ℝ) ≤ Fintype.card (Fin v → V) := by positivity
    by_cases hz : Fintype.card (Fin v → V) = 0
    · simp only [hz, Nat.cast_zero, div_zero] at h
      norm_num at h
    · have hp : (0 : ℝ) < Fintype.card (Fin v → V) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have ht := (le_div_iff₀ hp).mp h
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using ht
  let colMap : {c // c ∈ C} → Z := selectedRowSection R (fun z => tuple (π z))
  let Q := Protocol.comap (fun r : {r // r ∈ rows} => rowMap r.val)
    colMap (Protocol.swap P)
  have hQ : Q.Computes (subgame (interlaceFun g v) rows C) := by
    intro r c
    have hc := selectedRowSection_mem R (fun z => tuple (π z)) c
    have hcval := selectedRowSection_apply R (fun z => tuple (π z)) c
    rw [show Q = Protocol.comap (fun r : {r // r ∈ rows} => rowMap r.val)
      colMap (Protocol.swap P) from rfl, Protocol.comap_eval, Protocol.eval_swap]
    rw [heval _ hc _ r.property]
    exact congrArg (interlaceFun g v r.val) hcval
  have hcost : D (subgame (interlaceFun g v) rows C) ≤ P.cost := by
    have h := Nat.sInf_le (s := AchievableCosts (subgame (interlaceFun g v) rows C))
      ⟨Q, rfl, hQ⟩
    simpa only [Q, Protocol.comap_cost, Protocol.cost_swap] using h
  have hbracket : (rows, C) ∈ bracketGE U V v xcap (1 / 2) := by
    exact ⟨hrows, Nat.ceil_le.mpr (by simpa only [mul_comm] using hdens)⟩
  have hfamily : Dfamily (interlaceFun g v) (bracketGE U V v xcap (1 / 2)) ≤
      D (subgame (interlaceFun g v) rows C) := Nat.sInf_le ⟨(rows, C), hbracket, rfl⟩
  exact hprofile.trans (hfamily.trans hcost)

end Graph

section Routing

variable {A B U V Z W : Type*} [Fintype A] [DecidableEq A] [DecidableEq Z]

/-- All invariants concern actual input sets and exact evaluation identities.
The graph maps are fixed before routing and do not depend on a child query. -/
structure State {q L v : ℕ} (f : A → B → Bool) (S : Fin L → Fin q → B)
    (K : Finset (Fin L)) (rowMap : Fin L → W) (π : Fin q → Z → A)
    (witnesses : Finset (Fin q))
    (g : U → V → Bool) (graphRows : Fin q → Finset (Fin v × U))
    (graphMap : Fin q → (Fin v × U) → W) (tuple : Fin q → A → Fin v → V)
    (x : ℝ) (P : Protocol Z W Bool) (n : ℕ) (ms : List (Marker Z (Fin q))) : Prop where
  bins : (ms.map Marker.bin).Nodup
  witness : ∀ mark ∈ ms, mark.attached = true → mark.bin ∈ witnesses
  width : ∀ mark ∈ ms,
    threshold (Fintype.card A) x n ≤ (mark.width π : ℝ)
  injective : ∀ mark ∈ ms, Set.InjOn (π mark.bin) ↑mark.support
  ordinary : ∀ mark ∈ ms, ∀ z ∈ mark.support, ∀ l ∈ K,
    P.eval z (rowMap l) = f (π mark.bin z) (S l mark.bin)
  graph : ∀ mark ∈ ms, mark.attached = true → ∀ z ∈ mark.support,
    ∀ r ∈ graphRows mark.bin,
      P.eval z (graphMap mark.bin r) = interlaceFun g v r (tuple mark.bin (π mark.bin z))
  mass : ∀ mark ∈ ms, mark.attached = true →
    (1 / 2 : ℝ) * Fintype.card A + threshold (Fintype.card A) x n ≤ mark.support.card

theorem attached_mass_step {q : ℕ} (π : Fin q → Z → A) {x : ℝ} {n : ℕ}
    (a : Z → Bool) (bit : Bool) (mark mark' : Marker Z (Fin q))
    (hinj : Set.InjOn (π mark.bin) ↑mark.support)
    (hmass : (1 / 2 : ℝ) * Fintype.card A + threshold (Fintype.card A) x (n + 1) ≤
      mark.support.card)
    (hr : route π ⌈threshold (Fintype.card A) x n⌉₊ a mark bit = some mark')
    (ha : mark'.attached = true) :
    (1 / 2 : ℝ) * Fintype.card A + threshold (Fintype.card A) x n ≤ mark'.support.card := by
  have hfibre : ∀ c, ((mark.support.filter (fun z => π mark.bin z = c)).card : ℝ) ≤ 1 := by
    intro c
    have h : (mark.support.filter (fun z => π mark.bin z = c)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z hz z' hz'
      exact hinj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1
        ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm)
    exact_mod_cast h
  have hs := OuterAttachedLoss.attached_step_loss (by norm_num : (0 : ℝ) < 1)
    hfibre hr ha
  rw [threshold_succ] at hmass
  linarith

theorem State.alice_child {q L v : ℕ} {f : A → B → Bool} {S : Fin L → Fin q → B}
    {K : Finset (Fin L)} {rowMap : Fin L → W} {π : Fin q → Z → A}
    {witnesses : Finset (Fin q)}
    {g : U → V → Bool} {graphRows : Fin q → Finset (Fin v × U)}
    {graphMap : Fin q → (Fin v × U) → W} {tuple : Fin q → A → Fin v → V}
    {x : ℝ} {a : Z → Bool} {lo hi : Protocol Z W Bool} {n : ℕ}
    {ms : List (Marker Z (Fin q))}
    (state : State f S K rowMap π witnesses g graphRows graphMap tuple x (.aNode a lo hi) (n + 1) ms)
    (bit : Bool) :
    State f S K rowMap π witnesses g graphRows graphMap tuple x (if bit then hi else lo) n
      (routeAll π ⌈threshold (Fintype.card A) x n⌉₊ a bit ms) := by
  refine ⟨routeAll_bins_nodup _ _ _ _ _ state.bins, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro mark' hm' ha
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    have h := state.witness mark hm (OuterAttachedLoss.attached_route hr ha).1
    simpa only [(route_support hr).1] using h
  · intro mark' hm'
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    apply route_floor_real (m := mark) _ hr
    simpa only [threshold_succ] using state.width mark hm
  · intro mark' hm'
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    obtain ⟨hbin, hsupp⟩ := route_support hr
    rw [hbin]
    exact (state.injective mark hm).mono (by rw [hsupp]; exact child_subset _ _ _)
  · intro mark' hm' z hz l hl
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    obtain ⟨hbin, hsupp⟩ := route_support hr
    have hz' := mem_child.mp (hsupp ▸ hz)
    have he := state.ordinary mark hm z hz'.1 l hl
    cases bit <;> simpa [Protocol.eval, hz'.2, hbin] using he
  · intro mark' hm' ha z hz r hrg
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    obtain ⟨hbin, hsupp⟩ := route_support hr
    have hattach := (OuterAttachedLoss.attached_route hr ha).1
    have hz' := mem_child.mp (hsupp ▸ hz)
    have he := state.graph mark hm hattach z hz'.1 r (by simpa [hbin] using hrg)
    cases bit <;> simpa [Protocol.eval, hz'.2, hbin] using he
  · intro mark' hm' ha
    obtain ⟨mark, hm, hr⟩ := mem_routeAll hm'
    exact attached_mass_step π a bit mark mark' (state.injective mark hm)
      (state.mass mark hm (OuterAttachedLoss.attached_route hr ha).1) hr ha

end Routing

section LowerBound

variable {A B U V Z W : Type*} [Fintype A] [Fintype B] [Fintype U] [Fintype V]
  [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] [DecidableEq V]
  [DecidableEq Z]

/-- Primitive indexed-family hypotheses used throughout the residual
argument. The all-scale tests are proved from these by localized stopping
and the row-doubling theorem. -/
structure OrdinaryInputs (f : A → B → Bool) {m R L H : ℕ}
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → B) (x h ε : ℝ) : Prop where
  cost : 2 ≤ H
  order : 2 ^ 20 ≤ m
  scale_pos : 0 < x
  row_scale : (2 : ℝ) ^ m * x ≤ 1
  error_nonneg : 0 ≤ ε
  density_pos : 0 < h
  first : H ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 5))
  half : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 10))
  balanced : IsBalancedFamily (2 ^ m) S ε
  density : (9 / 25 : ℝ) ≤ h / (2 * (1 + ε))
  stopping : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m))
  seed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
    h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε)

theorem ordinary_protocol_lower (f : A → B → Bool) {m R L H n : ℕ}
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → B) {x h ε : ℝ}
    (inputs : OrdinaryInputs (H := H) f S x h ε) (hn : n ≤ R + m)
    (P : Protocol Z W Bool) (K : Finset (Fin L)) (rowMap : Fin L → W)
    (π : Fin (2 ^ R * 2 ^ m) → Z → A) (ms : List (Marker Z (Fin (2 ^ R * 2 ^ m))))
    (hbins : (ms.map Marker.bin).Nodup)
    (hwidth : ∀ mark ∈ ms, threshold (Fintype.card A) x n ≤ (mark.width π : ℝ))
    (hK : h / 2 * (L : ℝ) ≤ K.card)
    (hcount : ProtectedIndexedLadder.markerCount n ≤ ms.length)
    (heval : ∀ mark ∈ ms, ∀ z ∈ mark.support, ∀ l ∈ K,
      P.eval z (rowMap l) = f (π mark.bin z) (S l mark.bin)) :
    H + max 1 n ≤ P.cost := by
  classical
  let I := markerBins ms
  let Rs : Finset (Fin (2 ^ R * 2 ^ m) × A) := Finset.univ.filter
    (fun r => r.1 ∈ I ∧ r.2 ∈ (markerRows ms r.1).image (π r.1))
  have hrows : ProtocolSeparation.HasRowsInBlocks Prod.fst Rs I
      ⌈(Fintype.card A : ℝ) * ((2 : ℝ) ^ (n + 1) * x)⌉₊ := by
    intro i hi
    have hfibre : Rs.filter (fun r => r.1 = i) =
        ((markerRows ms i).image (π i)).image (fun a => (i, a)) := by
      ext ⟨j, a⟩
      by_cases hj : j = i
      · subst j; simp [Rs, hi]
      · simp [Rs, hj, Ne.symm hj]
    rw [hfibre, Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2)]
    obtain ⟨mark, hm, rfl⟩ := mem_markerBins.mp hi
    have hsub : mark.support ⊆ markerRows ms mark.bin :=
      fun z hz => mem_markerRows.mpr ⟨mark, hm, rfl, hz⟩
    have hc : ((mark.support.image (π mark.bin)).card : ℝ) ≤
        ((markerRows ms mark.bin).image (π mark.bin)).card := by
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hsub (f := π mark.bin))
    apply Nat.ceil_le.mpr
    have hw := hwidth mark hm
    dsimp [Marker.width] at hw
    calc
      _ = threshold (Fintype.card A) x n := by unfold threshold; ring
      _ ≤ _ := hw.trans hc
  have hselection : ∀ r ∈ Rs, ∃ mark ∈ ms, ∃ z ∈ mark.support,
      mark.bin = r.1 ∧ π r.1 z = r.2 := by
    intro r hr
    obtain ⟨_, hrimage⟩ := (Finset.mem_filter.mp hr).2
    obtain ⟨z, hz, hzr⟩ := Finset.mem_image.mp hrimage
    obtain ⟨mark, hm, hbin, hzm⟩ := mem_markerRows.mp hz
    exact ⟨mark, hm, z, hzm, hbin, hzr⟩
  let pickMark (r : {r // r ∈ Rs}) := (hselection r.val r.property).choose
  let pickZ (r : {r // r ∈ Rs}) := (hselection r.val r.property).choose_spec.2.choose
  let Q := Protocol.comap pickZ (fun l : {l // l ∈ K} => rowMap l.val) P
  have hQ : Q.Computes (subgame (relaxedInterlace f S) Rs K) := by
    intro r l
    have hm := (hselection r.val r.property).choose_spec
    have hz := hm.2.choose_spec
    rw [show Q = Protocol.comap pickZ (fun l : {l // l ∈ K} => rowMap l.val) P from rfl,
      Protocol.comap_eval]
    have he := heval (pickMark r) hm.1 (pickZ r) hz.1 l.val l.property
    have hbin : (pickMark r).bin = r.val.1 := hz.2.1
    have hproj : π (pickMark r).bin (pickZ r) = r.val.2 :=
      (congrArg (fun i => π i (pickZ r)) hbin).trans hz.2.2
    exact he.trans (congrArg₂ f hproj (congrArg (S l.val) hbin))
  have hu : D (subgame (relaxedInterlace f S) Rs K) ≤ P.cost := by
    have hh := Nat.sInf_le (s := AchievableCosts (subgame (relaxedInterlace f S) Rs K))
      ⟨Q, rfl, hQ⟩
    simpa only [Q, Protocol.comap_cost] using hh
  have hl := ProtectedIndexedLadder.dyadic_half_test f inputs.cost inputs.order
    inputs.scale_pos inputs.row_scale inputs.error_nonneg inputs.density_pos
    inputs.first inputs.half S inputs.balanced inputs.density inputs.stopping inputs.seed
    n hn Rs K I (Finset.subset_univ _) (by simpa using hK)
    (by simpa only [I, markerBins_card ms hbins] using hcount) hrows
  exact hl.trans hu

/-- Actual-query induction for the protected residual protocol. Every
ordinary test is discharged by the proved indexed-family ladder, and every
attached test by the original graph-copy profile on fixed row sections. -/
theorem protocol_weight_bound (f : A → B → Bool) {m R L H v d : ℕ}
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → B) {x h ε xcap : ℝ}
    (inputs : OrdinaryInputs (H := H) f S x h ε)
    (K : Finset (Fin L)) (hK : h * (L : ℝ) ≤ K.card)
    (rowMap : Fin L → W) (π : Fin (2 ^ R * 2 ^ m) → Z → A)
    (witnesses : Finset (Fin (2 ^ R * 2 ^ m)))
    (g : U → V → Bool) (graphRows : Fin (2 ^ R * 2 ^ m) → Finset (Fin v × U))
    (graphMap : Fin (2 ^ R * 2 ^ m) → (Fin v × U) → W)
    (tuple : Fin (2 ^ R * 2 ^ m) → A → Fin v → V)
    (hgraph : H + 1 ≤ Dfamily (interlaceFun g v) (bracketGE U V v xcap (1 / 2)))
    (hgraphRows : ∀ i ∈ witnesses, IsEquipartitionedGE (graphRows i) Finset.univ
      ⌈(Fintype.card U : ℝ) * xcap⌉₊)
    (hreg : ∀ i ∈ witnesses, RegularOn Finset.univ (tuple i) d) (hd : 0 < d)
    (n : ℕ) (hn : n ≤ R + m) (P : Protocol Z W Bool)
    (ms : List (Marker Z (Fin (2 ^ R * 2 ^ m))))
    (state : State f S K rowMap π witnesses g graphRows graphMap tuple x P n ms)
    (hcost : P.cost ≤ H + n) : weight ms ≤ 3 * 2 ^ n := by
  have hx : 0 < x := inputs.scale_pos
  have hhalf : h / 2 * (L : ℝ) ≤ K.card := by
    have hL : (0 : ℝ) ≤ L := by positivity
    nlinarith [inputs.density_pos]
  induction n generalizing P ms with
  | zero =>
    by_contra hnot
    have hw : 3 < weight ms := by simpa using lt_of_not_ge hnot
    by_cases hlen : 2 ≤ ms.length
    · have hl := ordinary_protocol_lower f S inputs hn P K rowMap π ms state.bins
        state.width hhalf (by simpa [ProtectedIndexedLadder.markerCount] using hlen)
        state.ordinary
      norm_num only [Nat.max_eq_left (by omega : 0 ≤ 1), Nat.add_zero] at hl hcost
      omega
    · have hex : ∃ mark ∈ ms, mark.attached = true := by
        by_contra hh
        have hall : ∀ mark ∈ ms, mark.attached = false := by
          intro mark hm
          cases ha : mark.attached
          · rfl
          · exact False.elim (hh ⟨mark, hm, ha⟩)
        have heq := weight_eq_three_length ms hall
        omega
      obtain ⟨mark, hm, ha⟩ := hex
      have hi := state.witness mark hm ha
      have hmass : (1 / 2 : ℝ) * Fintype.card A ≤ mark.support.card := by
        have ht : 0 ≤ threshold (Fintype.card A) x 0 := by
          unfold threshold
          positivity
        linarith [state.mass mark hm ha]
      have hl := graph_protocol_lower g hgraph (graphRows mark.bin)
        (hgraphRows mark.bin hi) (tuple mark.bin) (hreg mark.bin hi) hd
        (graphMap mark.bin) P mark.support (π mark.bin) (state.injective mark hm)
        hmass (state.graph mark hm ha)
      omega
  | succ n ih =>
    by_contra hnot
    have hw : 3 * 2 ^ (n + 1) < weight ms := lt_of_not_ge hnot
    have hcount : ProtectedIndexedLadder.markerCount (n + 1) ≤ ms.length :=
      ProtectedIndexedLadder.markerCount_le_of_weight _ _ (by omega)
        (hw.trans_le (weight_le_four_length ms))
    cases P with
    | leaf z =>
      have hl := ordinary_protocol_lower f S inputs hn (.leaf z) K rowMap π ms
        state.bins state.width hhalf hcount state.ordinary
      simp only [Protocol.cost] at hl
      omega
    | aNode a lo hi =>
      have hlo := ih (by omega) lo (routeAll π ⌈threshold (Fintype.card A) x n⌉₊ a false ms)
        (by simpa using state.alice_child false) (by simp only [Protocol.cost] at hcost; omega)
      have hhi := ih (by omega) hi (routeAll π ⌈threshold (Fintype.card A) x n⌉₊ a true ms)
        (by simpa using state.alice_child true) (by simp only [Protocol.cost] at hcost; omega)
      have hwroute := routeAll_weight π ⌈threshold (Fintype.card A) x n⌉₊ a ms
      rw [Nat.pow_succ] at hw
      omega
    | bNode b lo hi =>
      obtain ⟨bit, hlarge⟩ := ProtocolSeparation.exists_large_bool_child K (fun l => b (rowMap l))
      let K' := K.filter (fun l => b (rowMap l) = bit)
      let P' := if bit then hi else lo
      have hK' : h / 2 * (L : ℝ) ≤ K'.card := by
        have hc : (K.card : ℝ) ≤ 2 * K'.card := by exact_mod_cast hlarge
        linarith
      have heval : ∀ mark ∈ ms, ∀ z ∈ mark.support, ∀ l ∈ K',
          P'.eval z (rowMap l) = f (π mark.bin z) (S l mark.bin) := by
        intro mark hm z hz l hl
        obtain ⟨hlK, hbit⟩ := Finset.mem_filter.mp hl
        have he := state.ordinary mark hm z hz l hlK
        cases bit <;> simpa [P', Protocol.eval, hbit] using he
      have hl := ordinary_protocol_lower f S inputs hn P' K' rowMap π ms
        state.bins state.width hK' hcount heval
      have hc : P'.cost ≤ H + n := by
        simp only [Protocol.cost] at hcost
        cases bit <;> simp only [P', Bool.false_eq_true, ↓reduceIte] <;> omega
      omega

/-- One distinct initial marker per ordinary coordinate; a witness is
attached exactly on the specified subset of these coordinates. -/
def initialMarkers {q : ℕ} (ordinary witnesses : Finset (Fin q))
    (support : Fin q → Finset Z) : List (Marker Z (Fin q)) :=
  ordinary.toList.map (fun i => ⟨i, support i, decide (i ∈ witnesses)⟩)

theorem initialMarkers_bins {q : ℕ} (ordinary witnesses : Finset (Fin q))
    (support : Fin q → Finset Z) :
    ((initialMarkers ordinary witnesses support).map Marker.bin).Nodup := by
  simpa [initialMarkers, List.map_map, Function.comp_def] using ordinary.nodup_toList

theorem initialMarkers_weight {q : ℕ} (ordinary witnesses : Finset (Fin q))
    (hsub : witnesses ⊆ ordinary) (support : Fin q → Finset Z) :
    weight (initialMarkers ordinary witnesses support) = 3 * ordinary.card + witnesses.card := by
  simp [initialMarkers, weight, List.map_map, markerWeight, Finset.sum_map_toList,
    Finset.sum_add_distrib, Finset.inter_eq_right.mpr hsub, Nat.mul_comm]

theorem initial_state (f : A → B → Bool) {q L v n : ℕ}
    (S : Fin L → Fin q → B) {x : ℝ}
    (K : Finset (Fin L)) (rowMap : Fin L → W) (π : Fin q → Z → A)
    (ordinary witnesses : Finset (Fin q)) (hsub : witnesses ⊆ ordinary)
    (g : U → V → Bool) (graphRows : Fin q → Finset (Fin v × U))
    (graphMap : Fin q → (Fin v × U) → W) (tuple : Fin q → A → Fin v → V)
    (P : Protocol Z W Bool) (support : Fin q → Finset Z)
    (hinj : ∀ i ∈ ordinary, Set.InjOn (π i) ↑(support i))
    (hmass : ∀ i ∈ ordinary, (3 / 4 : ℝ) * Fintype.card A ≤ (support i).card)
    (hscale : (2 : ℝ) ^ (n + 1) * x ≤ 1 / 4)
    (heval : ∀ i ∈ ordinary, ∀ z ∈ support i, ∀ l ∈ K,
      P.eval z (rowMap l) = f (π i z) (S l i))
    (hgraph : ∀ i ∈ witnesses, ∀ z ∈ support i, ∀ r ∈ graphRows i,
      P.eval z (graphMap i r) = interlaceFun g v r (tuple i (π i z))) :
    State f S K rowMap π witnesses g graphRows graphMap tuple x P n
      (initialMarkers ordinary witnesses support) := by
  have hthreshold : threshold (Fintype.card A) x n ≤ (1 / 4 : ℝ) * Fintype.card A :=
    mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)
  refine ⟨initialMarkers_bins ordinary witnesses support, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro mark hm ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    simpa using ha
  · intro mark hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hi' := Finset.mem_toList.mp hi
    have hc := Finset.card_image_iff.mpr (hinj i hi')
    change threshold (Fintype.card A) x n ≤ ((support i).image (π i)).card
    rw [hc]
    linarith [hmass i hi', (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ Fintype.card A)]
  · intro mark hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact hinj i (Finset.mem_toList.mp hi)
  · intro mark hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact heval i (Finset.mem_toList.mp hi)
  · intro mark hm ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact hgraph i (by simpa using ha)
  · intro mark hm ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hi' := Finset.mem_toList.mp hi
    change (1 / 2 : ℝ) * Fintype.card A + threshold (Fintype.card A) x n ≤ (support i).card
    linarith [hmass i hi']

/-- The prepared physical supports force one bit beyond the residual
budget. This is the cost contradiction required by the protected N proof,
with the prefix cost kept outside this local theorem. -/
theorem prepared_protocol_lower (f : A → B → Bool) {m R L H v d b w : ℕ}
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → B) {x h ε xcap : ℝ}
    (inputs : OrdinaryInputs (H := H) f S x h ε)
    (K : Finset (Fin L)) (hK : h * (L : ℝ) ≤ K.card)
    (rowMap : Fin L → W) (π : Fin (2 ^ R * 2 ^ m) → Z → A)
    (ordinary witnesses : Finset (Fin (2 ^ R * 2 ^ m))) (hsub : witnesses ⊆ ordinary)
    (hordinary : 2 ^ R * 2 ^ m ≤ ordinary.card + b)
    (hwitnesses : w ≤ witnesses.card + b) (hexcess : 4 * b < w)
    (g : U → V → Bool) (graphRows : Fin (2 ^ R * 2 ^ m) → Finset (Fin v × U))
    (graphMap : Fin (2 ^ R * 2 ^ m) → (Fin v × U) → W)
    (tuple : Fin (2 ^ R * 2 ^ m) → A → Fin v → V)
    (hgraph : H + 1 ≤ Dfamily (interlaceFun g v) (bracketGE U V v xcap (1 / 2)))
    (hgraphRows : ∀ i ∈ witnesses, IsEquipartitionedGE (graphRows i) Finset.univ
      ⌈(Fintype.card U : ℝ) * xcap⌉₊)
    (hreg : ∀ i ∈ witnesses, RegularOn Finset.univ (tuple i) d) (hd : 0 < d)
    (P : Protocol Z W Bool) (support : Fin (2 ^ R * 2 ^ m) → Finset Z)
    (hinj : ∀ i ∈ ordinary, Set.InjOn (π i) ↑(support i))
    (hmass : ∀ i ∈ ordinary, (3 / 4 : ℝ) * Fintype.card A ≤ (support i).card)
    (hscale : (2 : ℝ) ^ (R + m + 1) * x ≤ 1 / 4)
    (heval : ∀ i ∈ ordinary, ∀ z ∈ support i, ∀ l ∈ K,
      P.eval z (rowMap l) = f (π i z) (S l i))
    (hgraphEval : ∀ i ∈ witnesses, ∀ z ∈ support i, ∀ r ∈ graphRows i,
      P.eval z (graphMap i r) = interlaceFun g v r (tuple i (π i z))) :
    H + (R + m) + 1 ≤ P.cost := by
  by_contra hnot
  have hcost : P.cost ≤ H + (R + m) := by omega
  have hs := initial_state f S K rowMap π ordinary witnesses hsub g graphRows graphMap
    tuple P support hinj hmass hscale heval hgraphEval
  have hw := protocol_weight_bound f S inputs K hK rowMap π witnesses g graphRows graphMap
    tuple hgraph hgraphRows hreg hd (R + m) (le_refl _) P
    (initialMarkers ordinary witnesses support) hs hcost
  rw [initialMarkers_weight ordinary witnesses hsub support, pow_add] at hw
  omega

end LowerBound

end EthInapproximability.CurrentPaper.ProtectedRoutedBound
