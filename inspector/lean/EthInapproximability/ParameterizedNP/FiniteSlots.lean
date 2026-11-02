import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Parameterized NP route: zero-based finite slots

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `conv:finite-slots`, the
  convention *Zero-based finite slots* in
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/02-mechanical-contract.tex`, restated at
  `sec:preliminaries` in `sections/03-preliminaries.tex`
  ("Initial segments, finite powers, inclusions, and last slots follow the
  zero-based convention of `conv:finite-slots`").
* **Consuming anchors traced here:** `sec:one-level` in
  `sections/07-one-level-construction.tex` — the Stage-1 slot binding
  `iota_1 = inc_{q_1,L_1}`, the complementary tail inclusion
  `kappa_1 : [s+1] -> [L_1]`, `kappa_1 (r) = q_1 + r`, whose images partition
  `[L_1]`, the derived tail function `tail_{s+1}(gamma)(r) = gamma(kappa_1(r))`,
  and the Stage-4 active/neutral slot binding `iota_s = inc_{s,s+1}`,
  `nu_s = last_{s+1} = s`.
* **Reader counterpart:** `sec:preliminaries` in
  `routes/parameterized-np/reader-facing/sections/02-preliminaries.tex`, which
  uses the *one-based* convention `[d] = {1, ..., d}` and states the shift to
  this artifact's zero-based slots explicitly; the reader-side accessor
  `1 + residue` of `SOURCE_MAP.md` is the transport of the zero-based residue
  formalized here.  The reader artifact is navigation only: the frozen
  autoformalization source above is the proof source.

## Dependencies, imports, adapters

* Mathlib only (`Fin`, `Nat` arithmetic, `omega`).  No `LegacyNPCC.Stage12`
  import, hence no contact with the cited AGHP balanced-family axiom; no
  external theorem adapter and no cited-fact hypothesis is consumed here.
* Proof status of every declaration below: **new** (transcription of a frozen
  convention; the manuscript states the convention rather than proving it).

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M2`/`M4`: `Stage1SlotBinding` carries only public parameter data (`a`, `s`)
  and their legality guards.  Widths `q_1 = 2^a - 2` and `L_1 = q_1 + s + 1`
  are *derived* accessors, not fields, so no derived telescope is restated as
  a bundle field and no promise certificate, complexity bound, or robustness
  conclusion enters constructor data.
* `M7`: both sides of every slot decomposition are defined and proved nonempty
  (`six_le_q₁`, `Stage1SlotBinding.s_pos`).
* `M9`: the `[a] / [d]` split is exhaustive by `exists_inc_or_tailInc` and
  disjoint by `inc_ne_tailInc`, so no branch is left implicit.
* The convention's final clause — *"Whenever two finite slot types have
  different sizes, the required inclusion is displayed explicitly; an unwritten
  coercion between them is never intended"* — is enforced by types: `Fin a` and
  `Fin d` are distinct types and every transport below is a named function.

## Interlace widths

This module is deliberately upstream of the interlace layer; the widths `q`
and `Q` are untouched here and must be introduced with their own anchors.
-/

namespace EthInapproximability.ParameterizedNP.FiniteSlots

/-! ## The convention `conv:finite-slots` -/

/-- `[d] = {r ∈ ℕ : r < d}` of `conv:finite-slots`, zero-based.

The manuscript's finite power `X^d` is the function space `[d] → X`
(`Slot d → X` below), and "a coordinate is read by function evaluation" is
Lean function application. -/
abbrev Slot (d : ℕ) : Type := Fin d

/-- The canonical initial-slot inclusion `inc_{a,d} : [a] ↪ [d]`,
`inc_{a,d}(r) = r`, of `conv:finite-slots`, for `a ≤ d`. -/
def inc {a d : ℕ} (h : a ≤ d) (r : Slot a) : Slot d :=
  ⟨r.val, lt_of_lt_of_le r.isLt h⟩

/-- The complementary tail inclusion of `sec:one-level`: for a displayed split
`a + e = d`, the map `[e] ↪ [d]`, `r ↦ a + r`.  With `a = q_1`, `e = s + 1`,
`d = L_1` this is exactly `kappa_1(r) = q_1 + r`. -/
def tailInc {a e d : ℕ} (h : a + e = d) (r : Slot e) : Slot d :=
  ⟨a + r.val, by have := r.isLt; omega⟩

/-- The distinguished last slot `last_d = d - 1 ∈ [d]` of `conv:finite-slots`,
defined only for `d > 0`. -/
def last (d : ℕ) (hd : 0 < d) : Slot d :=
  ⟨d - 1, by omega⟩

@[simp] theorem inc_val {a d : ℕ} (h : a ≤ d) (r : Slot a) :
    (inc h r).val = r.val := rfl

@[simp] theorem tailInc_val {a e d : ℕ} (h : a + e = d) (r : Slot e) :
    (tailInc h r).val = a + r.val := rfl

@[simp] theorem last_val (d : ℕ) (hd : 0 < d) :
    (last d hd).val = d - 1 := rfl

/-! ## Derived slot data of `sec:one-level`

`gamma : [L_1] → Cols(R)` restricted along the two displayed inclusions.
`slotTail` is the manuscript's `tail_{s+1}`. -/

/-- Restriction of a finite power along the initial-slot inclusion. -/
def slotHead {X : Type*} {a e d : ℕ} (h : a + e = d) (γ : Slot d → X) :
    Slot a → X :=
  fun r => γ (inc (by omega) r)

/-- The derived tail function `tail_{s+1}(gamma)(r) = gamma(kappa_1(r))` of
`sec:one-level`, stated for a general displayed split `a + e = d`. -/
def slotTail {X : Type*} {a e d : ℕ} (h : a + e = d) (γ : Slot d → X) :
    Slot e → X :=
  fun r => γ (tailInc h r)

/-- Reassembly along the displayed split: the inverse of
`(slotHead, slotTail)`.  This is a formalization convenience, not a
manuscript object; it exists to witness that the split loses no data. -/
def slotAppend {X : Type*} {a e d : ℕ} (h : a + e = d)
    (f : Slot a → X) (g : Slot e → X) : Slot d → X :=
  fun t =>
    if ht : t.val < a then f ⟨t.val, ht⟩
    else g ⟨t.val - a, by have := t.isLt; omega⟩

/-! ## Aux-lemma battery A2: identity and functoriality of `inc` -/

/-- `inc_{d,d}` is the identity: a slot type never needs an inclusion into
itself. -/
@[simp] theorem inc_self {d : ℕ} (r : Slot d) : inc (le_refl d) r = r := rfl

/-- Inclusions compose to inclusions, so any chain of displayed initial-slot
inclusions collapses to the single displayed inclusion. -/
theorem inc_inc {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (r : Slot a) :
    inc h₂ (inc h₁ r) = inc (h₁.trans h₂) r := rfl

/-- The inclusion does not depend on the proof of `a ≤ d`
(proof irrelevance made explicit, since the manuscript displays the inclusion
by its endpoints only). -/
theorem inc_congr {a d : ℕ} (h h' : a ≤ d) (r : Slot a) :
    inc h r = inc h' r := rfl

/-! ## Aux-lemma battery A3: injectivity, monotonicity, last slot -/

theorem inc_injective {a d : ℕ} (h : a ≤ d) : Function.Injective (inc h) := by
  intro r₁ r₂ hEq
  have hval := congrArg Fin.val hEq
  simp only [inc_val] at hval
  exact Fin.ext hval

theorem tailInc_injective {a e d : ℕ} (h : a + e = d) :
    Function.Injective (tailInc h) := by
  intro r₁ r₂ hEq
  have hval := congrArg Fin.val hEq
  simp only [tailInc_val] at hval
  exact Fin.ext (by omega)

/-- `inc` is strictly monotone, so the zero-based order on `[a]` is the order
inherited from `[d]`. -/
theorem inc_lt_inc {a d : ℕ} (h : a ≤ d) {r₁ r₂ : Slot a} :
    inc h r₁ < inc h r₂ ↔ r₁ < r₂ := by
  simp only [Fin.lt_def, inc_val]

/-- `last_d` is the maximum of `[d]`. -/
theorem le_last {d : ℕ} (hd : 0 < d) (r : Slot d) : r ≤ last d hd := by
  have := r.isLt
  simp only [Fin.le_def, last_val]
  omega

/-- `last_d` is the unique slot that is not strictly below `d - 1`. -/
theorem eq_last_iff {d : ℕ} (hd : 0 < d) (r : Slot d) :
    r = last d hd ↔ r.val = d - 1 := by
  constructor
  · intro hr; rw [hr]; rfl
  · intro hr; exact Fin.ext (by simpa using hr)

/-! ## Aux-lemma battery A4: the displayed split is a partition

`sec:one-level`: "Their images partition `[L_1]`."  Disjointness plus
covering, stated for a general split `a + e = d`. -/

/-- Disjointness: no slot is simultaneously an initial slot and a tail slot. -/
theorem inc_ne_tailInc {a e d : ℕ} (h : a + e = d)
    (hle : a ≤ d) (r : Slot a) (r' : Slot e) :
    inc hle r ≠ tailInc h r' := by
  intro hEq
  have hval : r.val = a + r'.val := congrArg Fin.val hEq
  have hr := r.isLt
  omega

/-- Covering: every slot of `[d]` is an initial slot or a tail slot. -/
theorem exists_inc_or_tailInc {a e d : ℕ} (h : a + e = d) (hle : a ≤ d)
    (t : Slot d) :
    (∃ r : Slot a, inc hle r = t) ∨ (∃ r : Slot e, tailInc h r = t) := by
  by_cases ht : t.val < a
  · exact Or.inl ⟨⟨t.val, ht⟩, Fin.ext rfl⟩
  · have htd := t.isLt
    refine Or.inr ⟨⟨t.val - a, by omega⟩, Fin.ext ?_⟩
    simp only [tailInc_val]
    omega

/-- The neutral last tail slot is the last slot of the ambient type: with
`a = q_1`, `e = s + 1`, `d = L_1` this says `kappa_1(nu_s) = last_{L_1}`. -/
theorem tailInc_last {a e d : ℕ} (h : a + e = d) (he : 0 < e) (hd : 0 < d) :
    tailInc h (last e he) = last d hd := by
  refine Fin.ext ?_
  simp only [tailInc_val, last_val]
  omega

/-! ## Aux-lemma battery A5: the head/tail split is a round trip -/

@[simp] theorem slotHead_slotAppend {X : Type*} {a e d : ℕ} (h : a + e = d)
    (f : Slot a → X) (g : Slot e → X) :
    slotHead h (slotAppend h f g) = f := by
  funext r
  have hr := r.isLt
  simp only [slotHead, slotAppend, inc]
  rw [dif_pos hr]

@[simp] theorem slotTail_slotAppend {X : Type*} {a e d : ℕ} (h : a + e = d)
    (f : Slot a → X) (g : Slot e → X) :
    slotTail h (slotAppend h f g) = g := by
  funext r
  simp only [slotTail, slotAppend, tailInc]
  rw [dif_neg (by omega)]
  exact congrArg g (Fin.ext (by simp))

theorem slotAppend_slotHead_slotTail {X : Type*} {a e d : ℕ} (h : a + e = d)
    (γ : Slot d → X) :
    slotAppend h (slotHead h γ) (slotTail h γ) = γ := by
  funext t
  have htd := t.isLt
  simp only [slotAppend, slotHead, slotTail]
  by_cases ht : t.val < a
  · rw [dif_pos ht]
    exact congrArg γ (Fin.ext rfl)
  · rw [dif_neg ht]
    exact congrArg γ (Fin.ext (by simp; omega))

/-- The derived tail function is surjective: every tail pattern is realized by
some finite power.  (Non-vacuity of `tail_{s+1}` as a construction, not just as
a definition.) -/
theorem slotTail_surjective {X : Type*} {a e d : ℕ} (h : a + e = d)
    [Nonempty X] : Function.Surjective (slotTail (X := X) h) := by
  intro g
  exact ⟨slotAppend h (fun _ => Classical.arbitrary X) g, by simp⟩

/-! ## The Stage-1 slot binding of `sec:one-level`

The parameter compiler has fixed `a ≥ 3`; `q_1 = 2^a - 2`, `L_1 = q_1 + s + 1`,
and `s > 0` (the manuscript uses `p_0 = 0 ∈ [s]` at `eq:raw-stage4-universes`,
which requires `s > 0`).  Only these public parameters and their legality
guards are fields; every width is derived. -/

/-- Legal public slot parameters of one level.  Fields are exactly the
compiler-fixed integers and their guards (`M1`, `M2`). -/
structure Stage1SlotBinding where
  /-- The compiler-fixed Stage-1 exponent, `a ≥ 3`. -/
  a : ℕ
  /-- The Stage-3 bin width, positive. -/
  s : ℕ
  /-- Legality guard from `sec:one-level`: "The parameter compiler has fixed
  `a ≥ 3`". -/
  three_le_a : 3 ≤ a
  /-- Legality guard from `eq:raw-stage4-universes`: "Since `s > 0`, put
  `p_0 = 0 ∈ [s]`". -/
  s_pos : 0 < s

namespace Stage1SlotBinding

variable (F : Stage1SlotBinding)

/-- `q_1 = 2^a - 2` (derived, `M3`). -/
def q₁ : ℕ := 2 ^ F.a - 2

/-- `L_1 = q_1 + s + 1` (derived, `M3`). -/
def L₁ : ℕ := F.q₁ + (F.s + 1)

/-- The displayed split of `[L_1]` into the Stage-1 template block and the
`s + 1` seed coordinates reserved for Stage 4. -/
theorem split : F.q₁ + (F.s + 1) = F.L₁ := rfl

theorem q₁_le_L₁ : F.q₁ ≤ F.L₁ := Nat.le_add_right _ _

/-- Nonemptiness of the Stage-1 template block (`M7`): `q_1 = 2^a - 2 ≥ 6`. -/
theorem six_le_q₁ : 6 ≤ F.q₁ := by
  have h : 2 ^ 3 ≤ 2 ^ F.a := Nat.pow_le_pow_right (by norm_num) F.three_le_a
  norm_num at h
  simp only [q₁]
  omega

theorem q₁_pos : 0 < F.q₁ := lt_of_lt_of_le (by norm_num) F.six_le_q₁

theorem L₁_pos : 0 < F.L₁ := lt_of_lt_of_le F.q₁_pos F.q₁_le_L₁

/-- The split is proper on both sides: the inclusion `iota_1` is genuinely an
inclusion of a smaller slot type. -/
theorem q₁_lt_L₁ : F.q₁ < F.L₁ := by
  simp only [L₁]
  omega

/-- `iota_1 = inc_{q_1, L_1} : [q_1] ↪ [L_1]` of `sec:one-level`. -/
def iota₁ : Slot F.q₁ → Slot F.L₁ := inc F.q₁_le_L₁

/-- `kappa_1 : [s+1] ↪ [L_1]`, `kappa_1(r) = q_1 + r`, of `sec:one-level`. -/
def kappa₁ : Slot (F.s + 1) → Slot F.L₁ := tailInc F.split

/-- `iota_s = inc_{s, s+1} : [s] ↪ [s+1]`, the active-slot inclusion bound
before `eq:raw-stage4-universes`. -/
def iotaS : Slot F.s → Slot (F.s + 1) := inc (Nat.le_succ F.s)

/-- `nu_s = last_{s+1} = s ∈ [s+1]`, the neutral last slot bound before
`eq:raw-stage4-universes`. -/
def nuS : Slot (F.s + 1) := last (F.s + 1) (Nat.succ_pos F.s)

@[simp] theorem nuS_val : F.nuS.val = F.s := by simp [nuS]

/-- The `kappa_1([s+1])`-tail "consists of `s` active slots followed by the
neutral slot": no active slot is the neutral slot. -/
theorem iotaS_ne_nuS (r : Slot F.s) : F.iotaS r ≠ F.nuS := by
  have hr := r.isLt
  intro hEq
  have hval : r.val = F.s := by
    simpa [iotaS, nuS] using congrArg Fin.val hEq
  omega

/-- The neutral Stage-4 slot sits at the very end of `[L_1]`. -/
theorem kappa₁_nuS : F.kappa₁ F.nuS = last F.L₁ F.L₁_pos :=
  tailInc_last F.split (Nat.succ_pos F.s) F.L₁_pos

/-- "Their images partition `[L_1]`", disjointness half. -/
theorem iota₁_ne_kappa₁ (r : Slot F.q₁) (r' : Slot (F.s + 1)) :
    F.iota₁ r ≠ F.kappa₁ r' :=
  inc_ne_tailInc F.split F.q₁_le_L₁ r r'

/-- "Their images partition `[L_1]`", covering half. -/
theorem exists_iota₁_or_kappa₁ (t : Slot F.L₁) :
    (∃ r : Slot F.q₁, F.iota₁ r = t) ∨ (∃ r : Slot (F.s + 1), F.kappa₁ r = t) :=
  exists_inc_or_tailInc F.split F.q₁_le_L₁ t

/-- `iota_1` is a *proper* inclusion: the reserved Stage-4 coordinates are not
in its image.  This is the statement pole for the whole module — a degenerate
"inclusion" that happened to be surjective would make the displayed-inclusion
discipline of `conv:finite-slots` vacuous. -/
theorem iota₁_not_surjective : ¬ Function.Surjective F.iota₁ := by
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj (F.kappa₁ F.nuS)
  exact F.iota₁_ne_kappa₁ r F.nuS hr

/-- The Stage-1 derived tail function
`tail_{s+1}(gamma)(r) = gamma(kappa_1(r))` of `sec:one-level`, on the finite
power `C_1 = Cols(R)^{L_1}`. -/
def stage1Tail {X : Type*} (γ : Slot F.L₁ → X) : Slot (F.s + 1) → X :=
  fun r => γ (F.kappa₁ r)

theorem stage1Tail_eq {X : Type*} (γ : Slot F.L₁ → X) :
    F.stage1Tail γ = slotTail F.split γ := rfl

end Stage1SlotBinding

/-! ## Aux-lemma battery A1: non-vacuity at legal parameter values

A nondegenerate inhabitant at the smallest legal parameters, with the hardest
field (`3 ≤ a`, which forces `q_1 = 2^a - 2 ≥ 6`) discharged at its boundary.
Every width below is a concrete positive integer, and the two blocks of the
`[L_1]` partition are both nonempty, so no cardinality-degenerate reading
inhabits this structure. -/

/-- The minimal legal Stage-1 slot binding: `a = 3`, `s = 1`, hence
`q_1 = 6` and `L_1 = 8`. -/
def stage1Minimal : Stage1SlotBinding where
  a := 3
  s := 1
  three_le_a := le_refl 3
  s_pos := Nat.one_pos

@[simp] theorem stage1Minimal_q₁ : stage1Minimal.q₁ = 6 := rfl

@[simp] theorem stage1Minimal_L₁ : stage1Minimal.L₁ = 8 := rfl

/-- Nondegeneracy of the inhabitant: both blocks of the `[L_1]` partition are
nonempty, the Stage-1 block is a proper subset, and the Stage-4 seed block has
at least one active slot plus the neutral slot. -/
theorem stage1Minimal_nondegenerate :
    0 < stage1Minimal.q₁ ∧ stage1Minimal.q₁ < stage1Minimal.L₁ ∧
      0 < stage1Minimal.s ∧ 1 < stage1Minimal.s + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [stage1Minimal, Stage1SlotBinding.q₁, Stage1SlotBinding.L₁]

/-- At the minimal legal binding the neutral Stage-4 slot is slot `7` of
`[8]`, and it is not an initial Stage-1 slot: the displayed inclusion is doing
real work. -/
theorem stage1Minimal_kappa₁_nuS_val :
    (stage1Minimal.kappa₁ stage1Minimal.nuS).val = 7 := rfl

theorem stage1Minimal_iota₁_not_surjective :
    ¬ Function.Surjective stage1Minimal.iota₁ :=
  stage1Minimal.iota₁_not_surjective

end EthInapproximability.ParameterizedNP.FiniteSlots
