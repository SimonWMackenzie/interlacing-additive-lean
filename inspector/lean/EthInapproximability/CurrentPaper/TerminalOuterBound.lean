import EthInapproximability.CurrentPaper.TerminalTwoStreams
import EthInapproximability.CurrentPaper.OuterAttachedLoss

/-!
# The outer selector contribution in the terminal two-stream bound

Source: replacement v8, `A-stage4-details.tex`,
`lem:paper-terminal-two-stream`, paragraph "The outer interlace".

The proof follows the actual Alice-query routing, keeping ordinary bin labels
and an attached joint pair support. The weight argument is expressed by
induction on the remaining Alice-depth budget. This is the local form of the
source's frontier-weight and Kraft argument; every real query is charged.
-/

noncomputable section
open scoped Classical BigOperators
open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol Workspace.UpperBound

namespace EthInapproximability.CurrentPaper.TerminalOuterBound

open OuterRouting JointTransfer TerminalTwoStreams

section Routing

variable {Z W B K : Type*} [DecidableEq Z] [DecidableEq K]

/-- Routing sends at most one descendant of each original bin to each child. -/
theorem routeAll_bins_sublist (π : B → Z → K) (T : ℕ) (a : Z → Bool)
    (bit : Bool) (ms : List (Marker Z B)) :
    List.Sublist ((routeAll π T a bit ms).map Marker.bin) (ms.map Marker.bin) := by
  induction ms with
  | nil => simp [routeAll]
  | cons m ms ih =>
    simp only [routeAll, List.map_append, List.map_cons]
    cases hr : route π T a m bit with
    | none => simpa [hr] using ih.cons m.bin
    | some m' =>
      have hbin := (route_support hr).1
      simpa [hr, hbin] using ih.cons_cons m.bin

theorem routeAll_bins_nodup (π : B → Z → K) (T : ℕ) (a : Z → Bool)
    (bit : Bool) (ms : List (Marker Z B)) (h : (ms.map Marker.bin).Nodup) :
    ((routeAll π T a bit ms).map Marker.bin).Nodup :=
  (routeAll_bins_sublist π T a bit ms).nodup h

/-- An injective joint pair map bounds every ordinary-coordinate fibre. -/
theorem fibre_card_le_of_pair_injective {L : ℕ}
    (R : Finset Z) (π ψ : Z → Fin L)
    (hinj : Set.InjOn (fun z => (π z, ψ z)) ↑R) (c : Fin L) :
    (R.filter (fun z => π z = c)).card ≤ L := by
  have hi : Set.InjOn ψ ↑(R.filter (fun z => π z = c)) := by
    intro u hu v hv huv
    obtain ⟨huR, huπ⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvR, hvπ⟩ := Finset.mem_filter.mp hv
    exact hinj huR hvR (Prod.ext (huπ.trans hvπ.symm) huv)
  have hc := Finset.card_image_iff.mpr hi
  calc
    _ = ((R.filter (fun z => π z = c)).image ψ).card := hc.symm
    _ ≤ Fintype.card (Fin L) := Finset.card_le_univ _
    _ = L := Fintype.card_fin L

/-- Exact remaining-depth row threshold in the source: `2*kappa*x` rows. -/
def threshold (L : ℕ) (x : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1) * x * L

theorem threshold_succ (L : ℕ) (x : ℝ) (n : ℕ) :
    threshold L x (n + 1) = 2 * threshold L x n := by
  simp only [threshold, pow_succ]
  ring

/-- The manuscript's routing margin implies the surplus needed on indexed
pairs. The template quotient is regular and therefore does not incur the
balance divisor; that divisor belongs to the later inner extraction. -/
theorem routing_margin_quotient_surplus {a tau ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (49 / 64 : ℝ) ≤ (a - tau) / (1 + ε) ^ 2) :
    (49 / 64 : ℝ) + tau ≤ a := by
  have hden : 0 < (1 + ε) ^ 2 := by positivity
  have hm := (le_div_iff₀ hden).mp hmargin
  nlinarith [sq_nonneg ε]

/-- The actual parameter constants have enough slack even if a later
balanced extraction is performed before the routing surplus is counted. -/
theorem parameter_quotient_surplus {a tau ε : ℝ}
    (ha : (9701 / 9801 : ℝ) ≤ a) (htau : tau ≤ 1 / 100)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 100) :
    (49 / 64 : ℝ) + tau ≤ a / (1 + ε) ^ 2 := by
  have hden : 0 < (1 + ε) ^ 2 := by positivity
  have hden_le : (1 + ε) ^ 2 ≤ (10201 / 10000 : ℝ) := by nlinarith
  apply (show (49 / 64 : ℝ) + tau ≤ 49 / 64 + 1 / 100 by linarith).trans
  apply (le_div_iff₀ hden).mpr
  nlinarith

open EthInapproximability.ParameterizedNP.TerminalStateRealization in
/-- Initial physical-pair density passes through the regular template
quotient with no balanced-extraction loss. This supplies exactly the
indexed-pair surplus required by `initial_state`. -/
theorem regular_pair_initial_surplus {C : Type*} [DecidableEq C] {L d m : ℕ}
    (hL : 0 < L) (Bo Bf : Finset C) (zo zf : C → Fin L)
    (ho : RegularOn Bo zo d) (hf : RegularOn Bf zf d) (hd : 0 < d)
    (hBo : Bo.card = m) (hBf : Bf.card = m)
    (Pstar : Finset (C × C)) (hstar : Pstar ⊆ Bo ×ˢ Bf)
    {a tau ε : ℝ} (ha : a ≤ (Pstar.card : ℝ) / (m : ℝ) ^ 2)
    (hε : 0 ≤ ε) (hmargin : (49 / 64 : ℝ) ≤ (a - tau) / (1 + ε) ^ 2) :
    ((49 / 64 : ℝ) + tau) * (L : ℝ) ^ 2 ≤
      ((Pstar.image (fun y => (zo y.1, zf y.2))).card : ℝ) := by
  have hquot := JointTransfer.surviving_pair_density Bo Bf zo zf ho hf hd hBo hBf
    Pstar Pstar hstar Finset.Subset.rfl (eta := 0) ha (by simp)
  simp only [sub_zero, Fintype.card_fin] at hquot
  have hs := routing_margin_quotient_surplus hε hmargin
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  exact (le_div_iff₀ hpos).mp (hs.trans hquot)

theorem attached_mass_survives {L : ℕ} (hL : 0 < L)
    (π : B → Z → Fin L) (ψ : Z → Fin L) (x : ℝ) (n : ℕ)
    (a : Z → Bool) (bit : Bool) (m m' : Marker Z B)
    (hinj : Set.InjOn (fun z => (π m.bin z, ψ z)) ↑m.support)
    (hmass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L x (n + 1) ≤
      m.support.card)
    (hr : route π ⌈threshold L x n⌉₊ a m bit = some m')
    (ha : m'.attached = true) :
    (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L x n ≤ m'.support.card := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep := OuterAttachedLoss.attached_step_loss hLR
    (fun c => by exact_mod_cast
      (fibre_card_le_of_pair_injective m.support (π m.bin) ψ hinj c)) hr ha
  rw [threshold_succ] at hmass
  linarith

end Routing

section PairedProtocol

variable {Z W B : Type*} [Fintype B] [DecidableEq Z] [DecidableEq B]

/-- The two-copy game uses one actual common reference tuple set and one
actual additional row set. Both types of rows use the same retained pairs
of Alice inputs from the same parent protocol. -/
theorem pairedGame_le_protocol {s L : ℕ}
    (M : B → Fin L → Bool) (P : Protocol Z W Bool)
    (C : Finset (Fin s → B)) (F : Finset B)
    (refMap : (Fin s → B) → W) (extraMap : B → W)
    (p : Fin s) (R : Finset Z) (π ψ : Z → Fin L)
    (hordinary : ∀ z ∈ R, ∀ c ∈ C, P.eval z (refMap c) = M (c p) (π z))
    (hadditional : ∀ z ∈ R, ∀ f ∈ F, P.eval z (extraMap f) = M f (ψ z)) :
    D (pairedGame M (C.image (fun c => c p)) F
      (R.image (fun z => (π z, ψ z)))) ≤ P.cost := by
  let rowMap :
      ({b // b ∈ C.image (fun c => c p)} ⊕ {b // b ∈ F}) → W :=
    Sum.elim (fun b => refMap (selectedRowSection C (fun c => c p) b))
      (fun b => extraMap b.val)
  let colMap : {k // k ∈ R.image (fun z => (π z, ψ z))} → Z :=
    selectedRowSection R (fun z => (π z, ψ z))
  let Q := Protocol.comap rowMap colMap (Protocol.swap P)
  have hQ : Q.Computes (pairedGame M (C.image (fun c => c p)) F
      (R.image (fun z => (π z, ψ z)))) := by
    intro b k
    have hk := selectedRowSection_mem R (fun z => (π z, ψ z)) k
    have hkval := selectedRowSection_apply R (fun z => (π z, ψ z)) k
    rw [show Q = Protocol.comap rowMap colMap (Protocol.swap P) from rfl,
      Protocol.comap_eval, Protocol.eval_swap]
    rcases b with b | b
    · have hb := selectedRowSection_mem C (fun c => c p) b
      have hbval := selectedRowSection_apply C (fun c => c p) b
      change P.eval (colMap k) (refMap (selectedRowSection C (fun c => c p) b)) = _
      rw [hordinary _ hk _ hb]
      simpa only [pairedGame, hbval, colMap] using congrArg (M b.val) (congrArg Prod.fst hkval)
    · change P.eval (colMap k) (extraMap b.val) = _
      rw [hadditional _ hk _ b.property]
      simpa only [pairedGame, colMap] using congrArg (M b.val) (congrArg Prod.snd hkval)
  have hcost : D (pairedGame M (C.image (fun c => c p)) F
      (R.image (fun z => (π z, ψ z)))) ≤ Q.cost :=
    Nat.sInf_le ⟨Q, rfl, hQ⟩
  simpa only [Q, Protocol.comap_cost, Protocol.cost_swap] using hcost

end PairedProtocol

/-- A common correlated tuple set and actual row sections suffice for the
ordinary outer-bin ladder. The protocol and column section are fixed. -/
theorem actual_outer_ladder {A B Z W : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq A]
    (f : A → B → Bool) (P : Protocol Z W Bool)
    {s H k : ℕ} {x : ℝ}
    (hH : 2 ≤ H) (hk : 1 ≤ k) (hx : 0 < x)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 10)))
    (I : Finset (Fin s)) (support : Fin s → Finset Z) (π : Fin s → Z → A)
    (C : Finset (Fin s → B)) (σ : (Fin s → B) → W)
    (hI : 2 ^ (k - 1) + 1 ≤ I.card)
    (hwidth : ∀ i ∈ I, (Fintype.card A : ℝ) * ((2 : ℝ) ^ k * x) ≤
      ((support i).image (π i)).card)
    (hC : (Fintype.card B : ℝ) ^ s * (9 / 25) ≤ C.card)
    (heval : ∀ i ∈ I, ∀ z ∈ support i, ∀ c ∈ C,
      P.eval z (σ c) = f (π i z) (c i)) :
    H + k ≤ P.cost := by
  classical
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hI
  let u := 2 ^ (k - 1) + 1
  let e : Fin u ≃ {i // i ∈ J} := Fintype.equivOfCardEq (by simpa [u] using hJ.symm)
  let R : Finset (Fin s × A) :=
    Finset.univ.filter (fun a => a.1 ∈ I ∧ a.2 ∈ (support a.1).image (π a.1))
  have hrows : IsEquipartitionedGE R J
      ⌈(Fintype.card A : ℝ) * ((2 : ℝ) ^ k * x)⌉₊ := by
    intro i hi
    have hRi : R.filter (fun a => a.1 = i) =
        ((support i).image (π i)).image (fun a => (i, a)) := by
      ext ⟨j, a⟩
      by_cases hj : j = i
      · subst j
        simp [R, hJI hi]
      · simp [R, hj, Ne.symm hj]
    rw [hRi, Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2)]
    exact Nat.ceil_le.mpr (hwidth i (hJI hi))
  obtain ⟨RC, hRC, hRsource, hCsource⟩ :=
    EthInapproximability.ParameterizedNP.InheritedContracts.coordProjection
      s u (by dsimp [u]; positivity) J e R C
      ⌈(Fintype.card A : ℝ) * ((2 : ℝ) ^ k * x)⌉₊
      ((2 : ℝ) ^ k * x) (9 / 25) hrows (Nat.ceil_le.mpr hC) (le_refl _)
  have hrowWitness : ∀ a ∈ RC.1,
      ∃ z ∈ support (e a.1).val, π (e a.1).val z = a.2 := by
    intro a ha
    have ht := hRsource a ha
    change ((e a.1).val, a.2) ∈ R at ht
    have himg := (Finset.mem_filter.mp ht).2.2
    exact Finset.mem_image.mp himg
  let rowMap : {a // a ∈ RC.1} → Z := fun a => (hrowWitness a.val a.property).choose
  let colSource : {c // c ∈ RC.2} → {c // c ∈ C} := fun c =>
    ⟨(hCsource c.val c.property).choose, (hCsource c.val c.property).choose_spec.1⟩
  let Q := Protocol.comap rowMap (fun c => σ (colSource c).val) P
  have hQ : Q.Computes (subgame (interlaceFun f u) RC.1 RC.2) := by
    intro a c
    rw [show Q = Protocol.comap rowMap (fun c => σ (colSource c).val) P from rfl,
      Protocol.comap_eval]
    change P.eval (rowMap a) (σ (colSource c).val) = f a.val.2 (c.val a.val.1)
    have hz := (hrowWitness a.val a.property).choose_spec
    have h := heval (e a.val.1).val (hJI (e a.val.1).property) (rowMap a) hz.1
      (colSource c).val (colSource c).property
    rw [h]
    apply congrArg₂ f hz.2
    exact ((hCsource c.val c.property).choose_spec.2 a.val.1).symm
  have hcost : D (subgame (interlaceFun f u) RC.1 RC.2) ≤ P.cost := by
    apply Nat.sInf_le
    exact ⟨Q, Protocol.comap_cost _ _ P, hQ⟩
  have hhalf : H - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE A B 1 x ((3 / 5 : ℝ) / 2)) := by
    convert h2 using 1
    norm_num
  have hld := repeatedRowDoubling f hH hx (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 / 5 : ℝ) ≤ 1) h1 hhalf k hk hscale
  have htop : H + k ≤ Dfamily (interlaceFun f u)
      (bracketGE A B u ((2 : ℝ) ^ k * x) (9 / 25)) := by
    simpa only [u, show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] using
      hld.trans (min_le_left _ _)
  have hRCcost : Dfamily (interlaceFun f u)
      (bracketGE A B u ((2 : ℝ) ^ k * x) (9 / 25)) ≤
      D (subgame (interlaceFun f u) RC.1 RC.2) := Nat.sInf_le ⟨RC, hRC, rfl⟩
  exact htop.trans (hRCcost.trans hcost)

section MarkerState

variable {Z W B : Type*} [DecidableEq Z]

/-- Finite data and actual evaluation identities carried along a route.
No communication lower bound or protocol-order conclusion is a field. -/
structure RoutingState {s L : ℕ} (M : B → Fin L → Bool)
    (C : Finset (Fin s → B)) (F : Finset B)
    (refMap : (Fin s → B) → W) (extraMap : B → W)
    (π : Fin s → Z → Fin L) (ψ : Z → Fin L) (x : ℝ)
    (P : Protocol Z W Bool) (n : ℕ) (ms : List (Marker Z (Fin s))) : Prop where
  bins : (ms.map Marker.bin).Nodup
  width : ∀ m ∈ ms, threshold L x n ≤ (m.width π : ℝ)
  ordinary : ∀ m ∈ ms, ∀ z ∈ m.support, ∀ c ∈ C,
    P.eval z (refMap c) = M (c m.bin) (π m.bin z)
  additional : ∀ m ∈ ms, m.attached = true → ∀ z ∈ m.support, ∀ f ∈ F,
    P.eval z (extraMap f) = M f (ψ z)
  pair_injective : ∀ m ∈ ms, m.attached = true →
    Set.InjOn (fun z => (π m.bin z, ψ z)) ↑m.support
  pair_mass : ∀ m ∈ ms, m.attached = true →
    (49 / 64 : ℝ) * (L : ℝ)^2 + L * threshold L x n ≤ m.support.card

theorem RoutingState.alice_child {s L : ℕ} {M : B → Fin L → Bool}
    {C : Finset (Fin s → B)} {F : Finset B}
    {refMap : (Fin s → B) → W} {extraMap : B → W}
    {π : Fin s → Z → Fin L} {ψ : Z → Fin L} {x : ℝ}
    {a : Z → Bool} {lo hi : Protocol Z W Bool} {n : ℕ}
    {ms : List (Marker Z (Fin s))}
    (hL : 0 < L)
    (h : RoutingState M C F refMap extraMap π ψ x (.aNode a lo hi) (n + 1) ms)
    (bit : Bool) :
    RoutingState M C F refMap extraMap π ψ x (if bit then hi else lo) n
      (routeAll π ⌈threshold L x n⌉₊ a bit ms) := by
  constructor
  · exact routeAll_bins_nodup _ _ _ _ _ h.bins
  · intro m hm
    obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
    apply route_floor_real (m := m₀) ?_ hr
    rw [← threshold_succ]
    exact h.width m₀ hm₀
  · intro m hm z hz c hc
    obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
    obtain ⟨hbin, hsupp⟩ := route_support hr
    have hzc := mem_child.mp (hsupp ▸ hz)
    have he := h.ordinary m₀ hm₀ z hzc.1 c hc
    cases bit <;> simpa [Protocol.eval, hzc.2, hbin] using he
  · intro m hm ha z hz f hf
    obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
    obtain ⟨_, hsupp⟩ := route_support hr
    have ha₀ := (OuterAttachedLoss.attached_route hr ha).1
    have hzc := mem_child.mp (hsupp ▸ hz)
    have he := h.additional m₀ hm₀ ha₀ z hzc.1 f hf
    cases bit <;> simpa [Protocol.eval, hzc.2] using he
  · intro m hm ha z hz z' hz' hzz'
    obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
    obtain ⟨hbin, hsupp⟩ := route_support hr
    have ha₀ := (OuterAttachedLoss.attached_route hr ha).1
    apply h.pair_injective m₀ hm₀ ha₀
      (child_subset _ _ _ (hsupp ▸ hz)) (child_subset _ _ _ (hsupp ▸ hz'))
    simpa [hbin] using hzz'
  · intro m hm ha
    obtain ⟨m₀, hm₀, hr⟩ := mem_routeAll hm
    have ha₀ := (OuterAttachedLoss.attached_route hr ha).1
    exact attached_mass_survives hL π ψ x n a bit m₀ m
      (h.pair_injective m₀ hm₀ ha₀) (h.pair_mass m₀ hm₀ ha₀) hr ha

def markerBins {s : ℕ} (ms : List (Marker Z (Fin s))) : Finset (Fin s) :=
  (ms.map Marker.bin).toFinset

def markerRows {s : ℕ} (ms : List (Marker Z (Fin s))) (i : Fin s) : Finset Z :=
  ms.toFinset.biUnion (fun m => if m.bin = i then m.support else ∅)

@[simp] theorem mem_markerBins {s : ℕ} {ms : List (Marker Z (Fin s))} {i : Fin s} :
    i ∈ markerBins ms ↔ ∃ m ∈ ms, m.bin = i := by simp [markerBins]

@[simp] theorem mem_markerRows {s : ℕ} {ms : List (Marker Z (Fin s))}
    {i : Fin s} {z : Z} :
    z ∈ markerRows ms i ↔ ∃ m ∈ ms, m.bin = i ∧ z ∈ m.support := by
  simp only [markerRows, Finset.mem_biUnion, List.mem_toFinset]
  apply exists_congr
  intro m
  by_cases hb : m.bin = i <;> simp [hb]

theorem markerBins_card {s : ℕ} (ms : List (Marker Z (Fin s)))
    (h : (ms.map Marker.bin).Nodup) : (markerBins ms).card = ms.length := by
  simpa [markerBins] using List.toFinset_card_of_nodup h

theorem ordinary_ladder_markers [Fintype B] [Nonempty B]
    {s L H k n : ℕ} (hL : 0 < L) (M : B → Fin L → Bool)
    (P : Protocol Z W Bool) {x : ℝ}
    (hH : 2 ≤ H) (hk : 1 ≤ k) (hx : 0 < x) (hkn : k ≤ n + 1)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun (Function.swap M) 1)
      (bracketGE (Fin L) B 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (Function.swap M) 1)
      (bracketGE (Fin L) B 1 x (3 / 10)))
    (C : Finset (Fin s → B)) (refMap : (Fin s → B) → W)
    (π : Fin s → Z → Fin L) (ms : List (Marker Z (Fin s)))
    (hbins : (ms.map Marker.bin).Nodup)
    (hwidth : ∀ m ∈ ms, threshold L x n ≤ (m.width π : ℝ))
    (hC : (Fintype.card B : ℝ) ^ s * (9 / 25) ≤ C.card)
    (hcount : 2 ^ (k - 1) + 1 ≤ ms.length)
    (heval : ∀ m ∈ ms, ∀ z ∈ m.support, ∀ c ∈ C,
      P.eval z (refMap c) = M (c m.bin) (π m.bin z)) : H + k ≤ P.cost := by
  letI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  apply actual_outer_ladder (Function.swap M) P hH hk hx hscale h1 h2
    (markerBins ms) (markerRows ms) π C refMap
  · simpa [markerBins_card ms hbins] using hcount
  · intro i hi
    obtain ⟨m, hm, rfl⟩ := mem_markerBins.mp hi
    have hsub : m.support ⊆ markerRows ms m.bin := by
      intro z hz
      exact mem_markerRows.mpr ⟨m, hm, rfl, hz⟩
    have himg := Finset.card_le_card (Finset.image_subset_image hsub (f := π m.bin))
    have hp : (2 : ℝ) ^ k ≤ 2 ^ (n + 1) :=
      pow_le_pow_right₀ (by norm_num) hkn
    have hw := hwidth m hm
    have himgR : ((m.support.image (π m.bin)).card : ℝ) ≤
      ((markerRows ms m.bin).image (π m.bin)).card := by exact_mod_cast himg
    have hwk : (L : ℝ) * ((2 : ℝ)^k * x) ≤ (m.width π : ℝ) := by
      calc
        (L : ℝ) * ((2 : ℝ)^k * x) = (2 : ℝ)^k * (x * (L : ℝ)) := by ring
        _ ≤ (2 : ℝ)^(n + 1) * (x * (L : ℝ)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = threshold L x n := by unfold threshold; ring
        _ ≤ (m.width π : ℝ) := hw
    simpa only [Fintype.card_fin] using hwk.trans himgR
  · exact hC
  · intro i hi z hz c hc
    obtain ⟨m, hm, hbin, hz'⟩ := mem_markerRows.mp hz
    simpa only [hbin] using heval m hm z hz' c hc

end MarkerState

theorem weight_le_four_length {Z B : Type*} (ms : List (Marker Z B)) :
    weight ms ≤ 4 * ms.length := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [weight_cons, List.length_cons, markerWeight]
    split <;> omega

theorem weight_eq_three_length {Z B : Type*} (ms : List (Marker Z B))
    (h : ∀ m ∈ ms, m.attached = false) : weight ms = 3 * ms.length := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hm := h m List.mem_cons_self
    have ht := ih (fun n hn => h n (List.mem_cons_of_mem _ hn))
    simp [weight_cons, markerWeight, hm, ht]
    omega

theorem bins_of_excess_weight {Z B : Type*} {n : ℕ}
    (hn : 1 ≤ n) (ms : List (Marker Z B)) (h : 3 * 2 ^ n < weight ms) :
    2 ^ (n - 1) + 1 ≤ ms.length := by
  have hw := weight_le_four_length ms
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
  rw [hp] at h
  omega

open EthInapproximability.ParameterizedNP.TerminalStateRealization

theorem eval_projection_density {B : Type*} [Fintype B] [Nonempty B] [DecidableEq B]
    {s : ℕ} (C : Finset (Fin s → B)) (p : Fin s) {rho : ℝ}
    (hC : rho * Fintype.card (Fin s → B) ≤ (C.card : ℝ)) :
    rho * Fintype.card B ≤ ((C.image (fun c => c p)).card : ℝ) := by
  classical
  have ht := regularOn_density_transfer
    (regularOn_univ_iff_isFibreBounded.mpr
      (isFibreBounded_evalAt p (Classical.choice (inferInstance : Nonempty B))))
    (evalFibre_card_pos p (Classical.choice (inferInstance : Nonempty B)))
    (Finset.subset_univ C)
  have hN : (0 : ℝ) < Fintype.card (Fin s → B) := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hB).mp
  exact ((le_div_iff₀ hN).mpr hC).trans (by simpa using ht)

section OuterBound

variable {X Y Z W : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Exactly the original two input profiles and scalar hypotheses used by
the checked fixed-bin theorem. No two-stream conclusion is a field. -/
structure PairInputs (f : X → Y → Bool) {q L : ℕ} (S : Fin L → Fin q → Y)
    (H m ell : ℕ) (x ε eps delta : ℝ) : Prop where
  qpos : 0 < q
  width : q = 2 ^ ell * 2 ^ (m - 1)
  cost : 2 ≤ H
  order : 2 ^ 20 ≤ m
  x_pos : 0 < x
  row_scale : (2 : ℝ) ^ m * x ≤ 1
  error_nonneg : 0 ≤ ε
  error_small : 2 * ε + ε ^ 2 ≤ 1 / 50
  first : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5))
  half : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10))
  balanced : IsBalancedFamily (2 ^ m) S ε
  stopping : (3 / 5 : ℝ) ≤
    yLoss (2 * ε + ε ^ 2) (2 ^ m) (49 / 64) (H + (ell + m))
  seed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
    (49 / 64) * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + (2 * ε + ε ^ 2))
  lambda_small : (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x) < 1
  extra_margin : (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x) + eps < delta

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed-bin transport traverses two nested finite subtype games.
theorem attached_protocol_bound (f : X → Y → Bool) {q L H m ell n s : ℕ}
    (S : Fin L → Fin q → Y) {x ε eps delta xT : ℝ}
    (inputs : PairInputs f S H m ell x ε eps delta) (hxT : 0 ≤ xT)
    (C : Finset (Fin s → (Fin q × X))) (F : Finset (Fin q × X))
    (refMap : (Fin s → (Fin q × X)) → W) (extraMap : (Fin q × X) → W)
    (π : Fin s → Z → Fin L) (ψ : Z → Fin L)
    (P : Protocol Z W Bool) (ms : List (Marker Z (Fin s)))
    (state : RoutingState (relaxedInterlace f S) C F refMap extraMap π ψ xT P n ms)
    (hC : (1 - eps) * Fintype.card (Fin s → (Fin q × X)) ≤ (C.card : ℝ))
    (hF : delta * Fintype.card (Fin q × X) ≤ (F.card : ℝ))
    (mark : Marker Z (Fin s)) (hmark : mark ∈ ms) (hattached : mark.attached = true) :
    H + m + ell ≤ P.cost := by
  classical
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp inputs.qpos
  let K := mark.support.image (fun z => (π mark.bin z, ψ z))
  have hcard : K.card = mark.support.card :=
    Finset.card_image_iff.mpr (state.pair_injective mark hmark hattached)
  have hmass := state.pair_mass mark hmark hattached
  have hK : (49 / 64 : ℝ) * (L * L : ℕ) ≤ (K.card : ℝ) := by
    rw [hcard]
    have ht : 0 ≤ (L : ℝ) * threshold L xT n := by unfold threshold; positivity
    have heq : (49 / 64 : ℝ) * (L * L : ℕ) = (49 / 64 : ℝ) * (L : ℝ)^2 := by
      norm_num [Nat.cast_mul, pow_two]
    rw [heq]
    linarith
  have hfixed := paired_fixedBin f inputs.qpos inputs.width inputs.cost inputs.order
    inputs.x_pos inputs.row_scale inputs.error_nonneg inputs.error_small
    inputs.first inputs.half S inputs.balanced inputs.stopping inputs.seed
    (C.image (fun c => c mark.bin)) F K (eval_projection_density C mark.bin hC) hF
    inputs.lambda_small inputs.extra_margin hK
  exact hfixed.trans (pairedGame_le_protocol (relaxedInterlace f S) P C F refMap extraMap
    mark.bin mark.support (π mark.bin) ψ
    (state.ordinary mark hmark) (state.additional mark hmark hattached))

/-- Every genuinely short protocol has at most the ordinary marker weight.
Alice steps use the constructed routing. Bob steps use an actual half-column
restriction and the row ladder. At remaining depth zero, an attached joint
support is ruled out by the proved fixed-bin theorem. -/
theorem protocol_weight_bound (f : X → Y → Bool) {q L H m ell s D2 : ℕ}
    (S : Fin L → Fin q → Y) {x ε eps delta xT : ℝ}
    (inputs : PairInputs f S H m ell x ε eps delta)
    (hD2 : D2 + 1 = H + m + ell) (hD2pos : 2 ≤ D2) (hxT : 0 < xT)
    (hsecond : D2 ≤ Dfamily (interlaceFun (Function.swap (relaxedInterlace f S)) 1)
      (bracketGE (Fin L) (Fin q × X) 1 xT (3 / 5)))
    (hsecondHalf : D2 - 1 ≤ Dfamily (interlaceFun (Function.swap (relaxedInterlace f S)) 1)
      (bracketGE (Fin L) (Fin q × X) 1 xT (3 / 10)))
    (heps : eps ≤ 1 / 5)
    (C : Finset (Fin s → (Fin q × X))) (F : Finset (Fin q × X))
    (hC : (1 - eps) * Fintype.card (Fin s → (Fin q × X)) ≤ (C.card : ℝ))
    (hF : delta * Fintype.card (Fin q × X) ≤ (F.card : ℝ))
    (refMap : (Fin s → (Fin q × X)) → W) (extraMap : (Fin q × X) → W)
    (π : Fin s → Z → Fin L) (ψ : Z → Fin L)
    (n : ℕ) (P : Protocol Z W Bool) (ms : List (Marker Z (Fin s)))
    (state : RoutingState (relaxedInterlace f S) C F refMap extraMap π ψ xT P n ms)
    (hcost : P.cost ≤ D2 + n) (hscale : (2 : ℝ) ^ (n + 1) * xT ≤ 1) :
    weight ms ≤ 3 * 2 ^ n := by
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp inputs.qpos
  have hL : 0 < L := inputs.balanced.1
  have hCpow : (1 - eps) * (Fintype.card (Fin q × X) : ℝ) ^ s ≤ C.card := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hC
  have hfull : (Fintype.card (Fin q × X) : ℝ) ^ s * (9 / 25) ≤ C.card := by
    have hh := mul_le_mul_of_nonneg_right
      (show (9 / 25 : ℝ) ≤ 1 - eps by linarith) (by positivity :
        0 ≤ (Fintype.card (Fin q × X) : ℝ) ^ s)
    nlinarith
  induction n generalizing P ms with
  | zero =>
    by_contra hnot
    have hw : 3 < weight ms := by simpa using (lt_of_not_ge hnot)
    by_cases hcount : 2 ≤ ms.length
    · have hl := ordinary_ladder_markers hL (relaxedInterlace f S) P hD2pos
        (k := 1) (n := 0) (by omega) hxT (by omega) hscale hsecond hsecondHalf
        C refMap π ms state.bins state.width hfull (by simpa using hcount)
        state.ordinary
      omega
    · have ha : ∃ mark ∈ ms, mark.attached = true := by
        by_contra hn
        push Not at hn
        have hf : ∀ mark ∈ ms, mark.attached = false := by
          intro mark hm
          cases hb : mark.attached <;> simp_all
        have he := weight_eq_three_length ms hf
        omega
      obtain ⟨mark, hm, ha⟩ := ha
      have hl := attached_protocol_bound f S inputs hxT.le C F refMap extraMap π ψ
        P ms state hC hF mark hm ha
      omega
  | succ n ih =>
    have hscale' : (2 : ℝ) ^ (n + 1) * xT ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right
        (show (2 : ℝ) ^ (n + 1) ≤ 2 ^ (n + 1 + 1) from
          pow_le_pow_right₀ (by norm_num) (by omega)) hxT.le
      exact hh.trans hscale
    by_contra hnot
    have hw := lt_of_not_ge hnot
    have hcount := bins_of_excess_weight (by omega : 1 ≤ n + 1) ms hw
    cases P with
    | leaf z =>
      have hl := ordinary_ladder_markers hL (relaxedInterlace f S) (.leaf z) hD2pos
        (k := n + 1) (n := n + 1) (by omega) hxT (by omega) hscale'
        hsecond hsecondHalf C refMap π ms state.bins state.width hfull hcount state.ordinary
      simp only [Protocol.cost] at hl
      omega
    | aNode a lo hi =>
      have hcl : lo.cost ≤ D2 + n := by simp only [Protocol.cost] at hcost; omega
      have hch : hi.cost ≤ D2 + n := by simp only [Protocol.cost] at hcost; omega
      have hl := ih lo (routeAll π ⌈threshold L xT n⌉₊ a false ms)
        (state.alice_child hL false) hcl hscale'
      have hh := ih hi (routeAll π ⌈threshold L xT n⌉₊ a true ms)
        (state.alice_child hL true) hch hscale'
      have hr := routeAll_weight π ⌈threshold L xT n⌉₊ a ms
      rw [pow_succ] at hw
      omega
    | bNode b lo hi =>
      obtain ⟨bit, hlarge⟩ := ProtocolSeparation.exists_large_bool_child C
        (fun c => b (refMap c))
      let C' := C.filter (fun c => b (refMap c) = bit)
      let P' := if bit then hi else lo
      have hhalf : (Fintype.card (Fin q × X) : ℝ) ^ s * (9 / 25) ≤ C'.card := by
        have hlargeR : (C.card : ℝ) ≤ 2 * C'.card := by exact_mod_cast hlarge
        have hh := mul_le_mul_of_nonneg_right
          (show (18 / 25 : ℝ) ≤ 1 - eps by linarith) (by positivity :
            0 ≤ (Fintype.card (Fin q × X) : ℝ) ^ s)
        nlinarith
      have heval : ∀ mark ∈ ms, ∀ z ∈ mark.support, ∀ c ∈ C',
          P'.eval z (refMap c) = relaxedInterlace f S (c mark.bin) (π mark.bin z) := by
        intro mark hm z hz c hc
        obtain ⟨hcC, hbit⟩ := Finset.mem_filter.mp hc
        have he := state.ordinary mark hm z hz c hcC
        cases bit <;> simpa [P', Protocol.eval, hbit] using he
      have hl := ordinary_ladder_markers hL (relaxedInterlace f S) P' hD2pos
        (k := n + 1) (n := n + 1) (by omega) hxT (by omega) hscale'
        hsecond hsecondHalf C' refMap π ms state.bins state.width hhalf hcount heval
      have hc : P'.cost ≤ D2 + n := by
        simp only [Protocol.cost] at hcost
        cases bit <;> simp only [P', Bool.false_eq_true, ↓reduceIte] <;> omega
      omega

/-- Initially there is one ordinary support in each bin and exactly one
additional stream, carried by the distinguished bin's joint support. -/
def initialMarkers {s : ℕ} (support : Fin s → Finset Z) (dist : Fin s) :
    List (Marker Z (Fin s)) :=
  List.ofFn (fun p => ⟨p, support p, decide (p = dist)⟩)

theorem initialMarkers_bins {s : ℕ} (support : Fin s → Finset Z) (dist : Fin s) :
    ((initialMarkers support dist).map Marker.bin).Nodup := by
  simp only [initialMarkers, List.map_ofFn]
  exact List.nodup_ofFn.mpr (fun _ _ h => h)

theorem initialMarkers_weight {s : ℕ} (support : Fin s → Finset Z) (dist : Fin s) :
    weight (initialMarkers support dist) = 3 * s + 1 := by
  simp [initialMarkers, weight, markerWeight, List.map_ofFn, List.sum_ofFn,
    Finset.sum_add_distrib, Nat.mul_comm]

theorem initial_state (f : X → Y → Bool) {q L s n : ℕ}
    (S : Fin L → Fin q → Y) (xT : ℝ)
    (C : Finset (Fin s → (Fin q × X))) (F : Finset (Fin q × X))
    (refMap : (Fin s → (Fin q × X)) → W) (extraMap : (Fin q × X) → W)
    (π : Fin s → Z → Fin L) (ψ : Z → Fin L)
    (P : Protocol Z W Bool) (support : Fin s → Finset Z) (dist : Fin s)
    (hwidth : ∀ p, threshold L xT n ≤ ((support p).image (π p)).card)
    (hordinary : ∀ p, ∀ z ∈ support p, ∀ c ∈ C,
      P.eval z (refMap c) = relaxedInterlace f S (c p) (π p z))
    (hadditional : ∀ z ∈ support dist, ∀ b ∈ F,
      P.eval z (extraMap b) = relaxedInterlace f S b (ψ z))
    (hinjective : Set.InjOn (fun z => (π dist z, ψ z)) ↑(support dist))
    (hmass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT n ≤
      (support dist).card) :
    RoutingState (relaxedInterlace f S) C F refMap extraMap π ψ xT P n
      (initialMarkers support dist) := by
  refine ⟨initialMarkers_bins support dist, ?_, ?_, ?_, ?_, ?_⟩
  · intro mark hm
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
    exact hwidth p
  · intro mark hm
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
    exact hordinary p
  · intro mark hm ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
    have hp : p = dist := by simpa using ha
    subst p
    exact hadditional
  · intro mark hm ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
    have hp : p = dist := by simpa using ha
    subst p
    exact hinjective
  · intro mark hm ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
    have hp : p = dist := by simpa using ha
    subst p
    exact hmass

/-- The full terminal two-stream cost, including the outer selector bits.
All supports and both row sections belong to this very protocol. The only
communication hypotheses are the original one-copy profiles of the base
game and of its inner transpose; support hypotheses are finite geometric
conditions, not an assumed marker or terminal hardness statement. -/
theorem outer_protocol_lower (f : X → Y → Bool) {q L H m ell s D2 r : ℕ}
    (S : Fin L → Fin q → Y) {x ε eps delta xT : ℝ}
    (inputs : PairInputs f S H m ell x ε eps delta)
    (hD2 : D2 + 1 = H + m + ell) (hD2pos : 2 ≤ D2) (hxT : 0 < xT)
    (hsecond : D2 ≤ Dfamily (interlaceFun (Function.swap (relaxedInterlace f S)) 1)
      (bracketGE (Fin L) (Fin q × X) 1 xT (3 / 5)))
    (hsecondHalf : D2 - 1 ≤ Dfamily (interlaceFun (Function.swap (relaxedInterlace f S)) 1)
      (bracketGE (Fin L) (Fin q × X) 1 xT (3 / 10)))
    (heps : eps ≤ 1 / 5) (hs : s = 2 ^ r)
    (hscale : (2 : ℝ) ^ (r + 1) * xT ≤ 1)
    (C : Finset (Fin s → (Fin q × X))) (F : Finset (Fin q × X))
    (hC : (1 - eps) * Fintype.card (Fin s → (Fin q × X)) ≤ (C.card : ℝ))
    (hF : delta * Fintype.card (Fin q × X) ≤ (F.card : ℝ))
    (refMap : (Fin s → (Fin q × X)) → W) (extraMap : (Fin q × X) → W)
    (π : Fin s → Z → Fin L) (ψ : Z → Fin L)
    (P : Protocol Z W Bool) (support : Fin s → Finset Z) (dist : Fin s)
    (hwidth : ∀ p, threshold L xT r ≤ ((support p).image (π p)).card)
    (hordinary : ∀ p, ∀ z ∈ support p, ∀ c ∈ C,
      P.eval z (refMap c) = relaxedInterlace f S (c p) (π p z))
    (hadditional : ∀ z ∈ support dist, ∀ b ∈ F,
      P.eval z (extraMap b) = relaxedInterlace f S b (ψ z))
    (hinjective : Set.InjOn (fun z => (π dist z, ψ z)) ↑(support dist))
    (hmass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
      (support dist).card) :
    D2 + r + 1 ≤ P.cost := by
  by_contra hnot
  have hcost : P.cost ≤ D2 + r := by omega
  have hbound := protocol_weight_bound f S inputs hD2 hD2pos hxT hsecond hsecondHalf
    heps C F hC hF refMap extraMap π ψ r P (initialMarkers support dist)
    (initial_state f S xT C F refMap extraMap π ψ P support dist
      hwidth hordinary hadditional hinjective hmass) hcost hscale
  rw [initialMarkers_weight, hs] at hbound
  omega

end OuterBound

end EthInapproximability.CurrentPaper.TerminalOuterBound
