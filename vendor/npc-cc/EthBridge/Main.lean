import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.ComplexityAux
import NPCC.Engine
import EthBridge.Arith
import EthBridge.Defs
import EthBridge.Hypotheses
import EthBridge.Bases
import EthBridge.Induction

/-! # EthBridge Theorem 1 — the direct lower bound (Tranche E3)

The E3 obligation `eth:thm-main` from `eth-obligations.json`, statements
drafted for faithfulness sign-off before proving and now ALL PROVED
(`lake build` green, axioms: `propext`/`Classical.choice`/`Quot.sound` only)
(source: `eth-docs/REENTRY_ROBUSTIFICATION_BY_DIRECT_DEFECT_ACCOUNTING.md`,
§4 "The Direct Lower Bound", Theorem 1 / (11)):

* `terminal_a0_member`              — per-member wrapper of the landed
                                      `terminal_a0` (Bases.lean:181), the shape
                                      the `a = 1` Alice recursion consumes;
* `main_pigeonhole_child_selection` — the MAIN-state (no-`B(p)`) analogue of
                                      `pigeonhole_child_selection`: (14)+(15)
                                      force a child with `L_i ≤ d_i·λ`;
* `main_alice_step`                 — Alice step, all levels `a ≥ 1` (the note's
                                      `a = 1` "repeat the assignment argument"
                                      and the `a ≥ 2` "same … now WITHOUT the
                                      `B(p)` term" are one uniform statement);
* `main_bob_step_a1`                — Bob step at `a = 1`: denser child `+ln 2`,
                                      max projection to TWO coordinates, budget
                                      `2λ + ln 2 ≤ -2 ln y` by margin (2), the
                                      `(Two)` TOP rung gives `≥ C`;
* `main_bob_step`                   — Bob step at `a ≥ 2`: the denser child is a
                                      one-bit-down `(12)` state at the SAME
                                      level `a` (budget `c_a(p)λ + ln 2 ≤
                                      c_a(p)λ + B(p)` by (5)), then
                                      `one_bit_down` gives `≥ C+a-1`;
* `theorem_one`                     — `eth:thm-main`, the assembled induction
                                      (11): `a = 0` terminal, `a ≥ 1`
                                      nonconstancy → first-bit dichotomy →
                                      the steps;
* `theorem_one_family`              — (11) in the `stateComp`/`Dfamily` family
                                      form scaffolded in `EthBridge.Defs`.

GLOBAL JUDGE FLAGS (individual flags at each declaration).

* **Copy-count encoding `p > 2^(a-1)` (ℕ-truncation trap).** Theorem 1 ranges
  over ALL `a ≥ 0`, where `2^(a-1)` is the REAL `1/2` at `a = 0` (so the
  condition is just `p ≥ 1`). The E2 form `2 ^ (a - 1) < p` is ℕ-truncated:
  at `a = 0` it reads `2^0 = 1 < p`, i.e. `p ≥ 2` — UNFAITHFULLY STRONG. The
  E3 statements therefore use the DOUBLED ℕ-safe form
      `2 ^ a < 2 * p`   (⟺ `p > 2^(a-1)` over ℝ, for every `a ≥ 0`),
  which agrees with E2's `2 ^ (a - 1) < p` for `a ≥ 1` (divide by 2) and reads
  `1 ≤ p` at `a = 0`. Level-(a−1) eligibility in the Alice IH is likewise
  `2 ^ (a - 1) < 2 * p'`. The `a ≥ 2` Bob step, which never touches level
  `a − 1 = 0` directly, keeps E2's `2 ^ (a - 1) < p` verbatim (equivalent
  there) so it plugs into `one_bit_down` without reshaping.
* **Note §2 side condition `2^a·x ≤ 1`** (`hax`): carried on `theorem_one` /
  `theorem_one_family` for statement fidelity (Theorem 1 assumes it). In the
  PER-MEMBER proof it is expected UNCONSUMED (as in E2, where the analogous
  flag was confirmed: the a = 2 base needs only `4x ≤ 1` from `hx`); it IS
  genuinely consumed by `theorem_one_family`, whose `Dfamily` conclusion needs
  the family nonempty — witnessed by `(univ, univ)` exactly under `hax` (and
  `0 ≤ c_a(p)λ`, from `hp`+`hlam`), cf. the `stateDensity` inhabitation unit
  test. The step lemmas do not carry it.
* All conclusions are PER-MEMBER (`… ≤ D (subgame (interlaceFun W p) RC.1
  RC.2)`), matching the E2 layer; only `theorem_one_family` is family-form.
* Child complexity bounds are phrased `D(child) + 1 ≤ D(parent)` (never
  ℕ-subtraction), matching `subgame_first_bit_dichotomy`.
* `hY : 1 ≤ Fintype.card Y`: retained where a projection/split engine consumes
  it and no `hTwo`+`hC` pair is present to derive it (`main_alice_step`), and
  where it is forwarded verbatim to `one_bit_down` (`main_bob_step`,
  `theorem_one` — redundantly derivable, kept for E2 parity); OMITTED from
  `main_bob_step_a1` (derivable from `hTwo`+`hC` as in `one_bit_down_base`).
  The judge may normalize.

DISCIPLINE (met): statements were signed off against the note's literal §4
text before proving; every body is now a complete proof. No new `def`s are
introduced (the Theorem-1 state family `stateDensity` and the family
abbreviation `stateComp` are the E0 defs, already inhabitation-tested), so no
new inhabitability unit tests are owed.
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## Per-member terminal level (`a = 0`)

`terminal_a0` (Bases.lean:181, PROVED) states the note's terminal case in the
FAMILY form `C ≤ stateComp X Y W p 0 x lam`. The Theorem-1 induction consumes
it per member (it is the `a = 1` Alice step's IH instance and the `a = 0` case
of `theorem_one`). The wrapper is the standard singleton descent:
`C ≤ stateComp = Dfamily (stateDensity …) ≤ Dfamily {RC} = D (subgame …)`
(`Dfamily.anti_mono` + `Dfamily.singleton`).

JUDGE FLAGS.
* Hypotheses are exactly `terminal_a0`'s; `hmem` replaces nothing (the family
  form quantifies over members through the `Dfamily` min, the wrapper makes
  one member explicit).
* `hx1 : x ≤ 1` (not `1/4`) as in `terminal_a0` — minimal density-side form,
  already judge-signed there. -/

/-- **Note §4, terminal `a = 0`, per-member form.** `(Near)` + membership in
the level-`0` MAIN state family ⇒ complexity `≥ C`. Singleton-descent wrapper
of the landed `terminal_a0`. -/
theorem terminal_a0_member {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C : ℕ) (p : ℕ) (x lam : ℝ)
    (hp : 1 ≤ p) (hx0 : 0 < x) (hx1 : x ≤ 1) (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X)
    (hNear : NearFull W C x lam)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p 0 x lam) :
    C ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  have h := terminal_a0 W C p x lam hp hx0 hx1 hlam hX hNear
  unfold stateComp at h
  calc C ≤ Dfamily (interlaceFun W p) (stateDensity X Y p 0 x lam) := h
    _ ≤ Dfamily (interlaceFun W p) {RC} :=
        Dfamily.anti_mono _ (Set.singleton_subset_iff.mpr hmem) (Set.singleton_nonempty _)
    _ = D (subgame (interlaceFun W p) RC.1 RC.2) := Dfamily.singleton _ _

/-! ## The MAIN-state Alice pigeonhole (notes (14), (15) — no `B(p)` term)

Note §4 "Main statement: induction": "If Alice speaks, use the same
assigned-coordinate argument as above, now WITHOUT the `B(p)` term. Equations
(14) and (15) force some child with `L_i ≤ d_i λ`. That child is a main state
at level `a-1`."

This is `pigeonhole_child_selection` (Induction.lean:156) with both budgets'
`Bdef` terms deleted and the level range extended down to `a = 1` (where the
child level is `0` and `c_0(p_i) = p_i - 1/2` is the intentional half-integer,
handled by `cExcess`'s `zpow`). Proof route: otherwise sum the strict reverse
inequalities — for an INELIGIBLE child `c_(a-1)(p_i)·λ ≤ 0 ≤ L_i` closes that
side without any envelope — and get `L₀ + L₁ > (c_(a-1)(p₀) + c_(a-1)(p₁))·λ
= c_a(p)·λ ≥ L₀ + L₁` (the middle identity is exact at the `zpow` level:
`2·2^{a-2} = 2^{a-1}` holds for ALL `a ≥ 1`, including the half-integer case
`a = 1`), a contradiction.

JUDGE FLAGS.
* Copy-count forms: parent `2 ^ a < 2 * p`, child eligibility
  `2 ^ (a - 1) < 2 * p_i` (the doubled ℕ-safe encodings; see file header). At
  `a = 1` the child form reads `1 < 2p_i`, i.e. `p_i ≥ 1` — the note's
  `d_i > 0` at half-integer threshold `2^{-1}`.
* Eligibility is stated through the ℕ inequality rather than
  `0 < cExcess (a-1) p_i` so `main_alice_step` can feed its IH guard directly;
  the two are equivalent over ℝ.
* `hE₀/hE₁` (the note's "`L_i = 0` for an empty coordinate set") are RETAINED
  for parity with `alice_coordinate_split`'s outputs and the E2 statement,
  but are believed DROPPABLE here: without the `B(p)` term, `0 ≤ L_i` alone
  closes every ineligible side. The judge may drop them.
* Non-strict `≤` in the selected child's budget, as in the note. -/

/-- **Notes (14)+(15), MAIN-state pigeonhole (no `B(p)`).** If the two
projected defects satisfy `L₀ + L₁ ≤ c_a(p)·λ` and `p₀ + p₁ = p > 2^(a-1)`
(`a ≥ 1`), some child `i` is eligible (`p_i > 2^(a-2)`) with
`L_i ≤ c_(a-1)(p_i)·λ` — a MAIN-state budget at level `a-1`. -/
theorem main_pigeonhole_child_selection (a p p₀ p₁ : ℕ) (L₀ L₁ lam : ℝ)
    (ha : 1 ≤ a) (hp : 2 ^ a < 2 * p) (hsum : p₀ + p₁ = p)
    (hlam : 0 < lam) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hE₀ : p₀ = 0 → L₀ = 0) (hE₁ : p₁ = 0 → L₁ = 0)
    (hadd : L₀ + L₁ ≤ cExcess a p * lam) :
    (2 ^ (a - 1) < 2 * p₀ ∧ L₀ ≤ cExcess (a - 1) p₀ * lam) ∨
    (2 ^ (a - 1) < 2 * p₁ ∧ L₁ ≤ cExcess (a - 1) p₁ * lam) := by
  have hI : ∀ q : ℕ, cExcess (a - 1) q = (q : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2) := by
    intro q; unfold cExcess
    rw [show ((a - 1 : ℕ) : ℤ) - 1 = (a : ℤ) - 2 by omega]
  have hA : cExcess a p = (p : ℝ) - 2 * (2 : ℝ) ^ ((a : ℤ) - 2) := by
    unfold cExcess
    rw [show (a : ℤ) - 1 = 1 + ((a : ℤ) - 2) by ring,
        zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hpow_real : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ ((a : ℤ) - 2) := by
    rw [← zpow_natCast (2 : ℝ) (a - 1),
        show ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 by omega,
        show (a : ℤ) - 1 = 1 + ((a : ℤ) - 2) by ring,
        zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hbridge : ∀ q : ℕ,
      (2 ^ (a - 1) < 2 * q) ↔ ((2 : ℝ) ^ ((a : ℤ) - 2) < (q : ℝ)) := by
    intro q
    rw [← @Nat.cast_lt ℝ]
    push_cast
    rw [hpow_real]
    constructor <;> intro h <;> linarith
  have hp_real : (p₀ : ℝ) + (p₁ : ℝ) = (p : ℝ) := by exact_mod_cast hsum
  have hexp : ((p : ℝ) - 2 * (2 : ℝ) ^ ((a : ℤ) - 2)) * lam =
      ((p₀ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam +
      ((p₁ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam := by
    rw [show (p : ℝ) = (p₀ : ℝ) + (p₁ : ℝ) from hp_real.symm]; ring
  rw [hA, hexp] at hadd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc0, hc1⟩ := hcon
  by_cases he0 : 2 ^ (a - 1) < 2 * p₀ <;> by_cases he1 : 2 ^ (a - 1) < 2 * p₁
  · have hb0 := hc0 he0; rw [hI p₀] at hb0
    have hb1 := hc1 he1; rw [hI p₁] at hb1
    linarith
  · have hb0 := hc0 he0; rw [hI p₀] at hb0
    have hp1le : (p₁ : ℝ) ≤ (2 : ℝ) ^ ((a : ℤ) - 2) :=
      not_lt.mp (fun h => he1 ((hbridge p₁).mpr h))
    have hnp1 : ((p₁ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · have hb1 := hc1 he1; rw [hI p₁] at hb1
    have hp0le : (p₀ : ℝ) ≤ (2 : ℝ) ^ ((a : ℤ) - 2) :=
      not_lt.mp (fun h => he0 ((hbridge p₀).mpr h))
    have hnp0 : ((p₀ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · have hpow_nat : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ']
    omega

/-! ## The MAIN Alice step (all levels `a ≥ 1`)

Note §4, `a = 1`: "If Alice speaks, repeat the assignment and defect-splitting
argument above. It produces a level-zero state satisfying the main defect
bound"; `a ≥ 2`: "use the same assigned-coordinate argument as above, now
without the `B(p)` term … That child is a main state at level `a-1`, so it has
complexity at least `C+a-1`."

Proof route (the exact E2 `one_bit_down_alice` skeleton with MAIN budgets):
1. `alice_coordinate_split` (note (14) engine) at `T = A_a`,
   `y_p = e^{-c_a(p)λ}` (`c_a(p) > 0` from `hp`, so `y_p ≤ 1`): coordinates
   split `p₀ + p₁ = p`, each side `≥ ⌈A_a/2⌉` rows per block, `y₀·y₁ ≥ y_p`;
2. `neg_log_sum_le`: `L₀ + L₁ ≤ c_a(p)·λ`                              (14);
3. `main_pigeonhole_child_selection` (15): an eligible child `i` with
   `L_i ≤ c_(a-1)(p_i)·λ`                                     (main budget);
4. `rowThreshold_ceil_halving` (1): `A_(a-1) ≤ ⌈A_a/2⌉` — child `i` is a MAIN
   state at level `a-1`; `IH` gives `≥ C+(a-1)`; `hchild` adds Alice's bit.

JUDGE FLAGS.
* ONE statement for all `a ≥ 1`: the note phrases `a = 1` as "repeat the
  argument" — the only level-dependent ingredient is the child threshold
  `2^(a-2)`, uniform in the `cExcess`/doubled-ℕ encodings. At `a = 1` the
  caller instantiates `IH` from `terminal_a0_member`.
* `IH` quantifies over ALL `p'` at level `a-1` with the doubled guard
  `2 ^ (a - 1) < 2 * p'` (the split changes the copy count; cf. E2).
* Hypothesis set mirrors `one_bit_down_alice`: no `y`/`hTwo`/`hmargin`/`hC`
  (the Alice step never touches the terminal bases), no `hx0` (only the
  ceiling arithmetic of (1) touches `x`). `hY` retained — the split engine
  requires it and nothing here derives it.
* Conclusion `C + a` (the parent's Theorem-1 target); the `+1` over the IH's
  `C + (a - 1)` is ℕ-exact since `a ≥ 1`. -/

/-- **Note §4, MAIN Alice step (`a ≥ 1`).** If Alice speaks first and
Theorem 1 holds at level `a-1` (hypothesis `IH`), then a MAIN state at level
`a` has complexity `≥ C+a`. -/
theorem main_alice_step {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x lam : ℝ)
    (ha : 1 ≤ a) (hp : 2 ^ a < 2 * p)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p a x lam)
    (α : (Fin p × X) → Bool)
    (hchild : ∀ b : Bool,
      D (subgame (interlaceFun W p)
          (RC.1.filter fun r => α r = b) RC.2) + 1 ≤
        D (subgame (interlaceFun W p) RC.1 RC.2))
    (IH : ∀ p' : ℕ, 2 ^ (a - 1) < 2 * p' →
      ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
        RC' ∈ stateDensity X Y p' (a - 1) x lam →
        C + (a - 1) ≤ D (subgame (interlaceFun W p') RC'.1 RC'.2)) :
    C + a ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hpow_nat : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ']
  have hlt : 2 ^ (a - 1) < p := by omega
  have hone : (1 : ℕ) ≤ 2 ^ (a - 1) := Nat.one_le_pow (a - 1) 2 (by norm_num)
  have hp1 : 1 ≤ p := by omega
  have hc_pos : 0 < cExcess a p := by
    have hp_cast : (2 : ℝ) ^ (a - 1) < (p : ℝ) := by exact_mod_cast hlt
    unfold cExcess
    rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    linarith
  have hyp_one : Real.exp (-(cExcess a p * lam)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cExcess a p * lam := mul_nonneg hc_pos.le hlam.le
    linarith
  obtain ⟨p₀, p₁, y₀, y₁, S₀, K₀, S₁, K₁, hpsum, hyy, hy₀pos, hy₀le1,
      hy₁pos, hy₁le1, hdeg₀, hdeg₁, hside₀, hside₁⟩ :=
    alice_coordinate_split W p (rowThreshold (Fintype.card X) x a)
      (Real.exp (-(cExcess a p * lam)))
      hp1 (Real.exp_pos _) hyp_one hX hY RC.1 RC.2 α hrows hcols
  have hadd : -Real.log y₀ + -Real.log y₁ ≤ cExcess a p * lam :=
    neg_log_sum_le y₀ y₁ _ hy₀pos hy₁pos hyy
  have hsel := main_pigeonhole_child_selection a p p₀ p₁
    (-Real.log y₀) (-Real.log y₁) lam ha hp hpsum hlam
    (neg_nonneg.mpr (Real.log_nonpos hy₀pos.le hy₀le1))
    (neg_nonneg.mpr (Real.log_nonpos hy₁pos.le hy₁le1))
    (fun h0 => by rw [hdeg₀ h0, Real.log_one, neg_zero])
    (fun h1 => by rw [hdeg₁ h1, Real.log_one, neg_zero])
    hadd
  have hAhalf := rowThreshold_ceil_halving (Fintype.card X) x a ha
  rcases hsel with ⟨helig, hbud⟩ | ⟨helig, hbud⟩
  · have hp₀ : 1 ≤ p₀ := by omega
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₀ hp₀
    have hexp : Real.exp (-(cExcess (a - 1) p₀ * lam)) ≤ y₀ := by
      have hlog : -(cExcess (a - 1) p₀ * lam) ≤ Real.log y₀ := by linarith
      calc Real.exp (-(cExcess (a - 1) p₀ * lam))
            ≤ Real.exp (Real.log y₀) := Real.exp_le_exp.mpr hlog
        _ = y₀ := Real.exp_log hy₀pos
    have hmem' : (S₀, K₀) ∈ stateDensity X Y p₀ (a - 1) x lam := by
      refine ⟨?_, ?_⟩
      · intro j hj; exact le_trans hAhalf (hequi j hj)
      · calc ((Fintype.card Y : ℝ) ^ p₀) * Real.exp (-(cExcess (a - 1) p₀ * lam))
              ≤ ((Fintype.card Y : ℝ) ^ p₀) * y₀ :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₀.card : ℝ) := hcolsb
    have hIH := IH p₀ helig (S₀, K₀) hmem'
    calc C + a = (C + (a - 1)) + 1 := by omega
      _ ≤ D (subgame (interlaceFun W p₀) S₀ K₀) + 1 := Nat.add_le_add_right hIH 1
      _ ≤ D (subgame (interlaceFun W p)
            (RC.1.filter fun r => α r = false) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild false
  · have hp₁ : 1 ≤ p₁ := by omega
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₁ hp₁
    have hexp : Real.exp (-(cExcess (a - 1) p₁ * lam)) ≤ y₁ := by
      have hlog : -(cExcess (a - 1) p₁ * lam) ≤ Real.log y₁ := by linarith
      calc Real.exp (-(cExcess (a - 1) p₁ * lam))
            ≤ Real.exp (Real.log y₁) := Real.exp_le_exp.mpr hlog
        _ = y₁ := Real.exp_log hy₁pos
    have hmem' : (S₁, K₁) ∈ stateDensity X Y p₁ (a - 1) x lam := by
      refine ⟨?_, ?_⟩
      · intro j hj; exact le_trans hAhalf (hequi j hj)
      · calc ((Fintype.card Y : ℝ) ^ p₁) * Real.exp (-(cExcess (a - 1) p₁ * lam))
              ≤ ((Fintype.card Y : ℝ) ^ p₁) * y₁ :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₁.card : ℝ) := hcolsb
    have hIH := IH p₁ helig (S₁, K₁) hmem'
    calc C + a = (C + (a - 1)) + 1 := by omega
      _ ≤ D (subgame (interlaceFun W p₁) S₁ K₁) + 1 := Nat.add_le_add_right hIH 1
      _ ≤ D (subgame (interlaceFun W p)
            (RC.1.filter fun r => α r = true) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild true

/-! ## The MAIN Bob step at `a = 1`

Note §4 "Main statement: the level `a = 1`": "If Bob speaks, keep a child with
defect at most `Def(K) + ln 2` and maximum-project it to two coordinates. The
projected defect is at most `(2/p)(Def(K) + ln 2) ≤ 2λ + ln 2 ≤ -2 ln y`,
where the last inequality follows from (2). The two-copy top rung in `(Two)`
gives child complexity at least `C`. Thus the parent has complexity at least
`C+1`."

Proof route (the `one_bit_down_base` skeleton at `ℓ = 2`, rung `(Two)`-top
instead of `(Three)`):
1. `exists_denser_child`: Bob's denser fiber has density `≥ y_p/2`, i.e.
   defect budget `c_1(p)λ + ln 2`;
2. `member_max_projection` at `ℓ = 2`, `T = A_1`: projected defect
   `≤ (2/p)(c_1(p)λ + ln 2)`, rows still `≥ A_1` per block;
3. budget: `(2/p)·c_1(p) ≤ 2` (`c_1(p) = p-1 ≤ p`) and `(2/p)·ln 2 ≤ ln 2`
   (`p ≥ 2`), then `2λ + ln 2 ≤ 3λ + (7/5)·ln 2 ≤ -2 ln y` (margin (2),
   `λ > 0`): projected density `≥ y²`;
4. `rowThreshold m x 1 = ⌈m·(2x)⌉₊` (ring identity inside the ceiling): the
   projected member lands in `bracketGE X Y 2 (2x) (y²)`;
5. `TwoCopyBundle.top_rung` + `Dfamily.anti_mono`/`.singleton`: child `≥ C`;
   `hchild` adds Bob's bit: parent `≥ C+1`.

JUDGE FLAGS.
* `hp : 2 ≤ p` is `p > 2^(a-1)` at `a = 1` (the doubled form `2^1 < 2p`
  reduced); the note: "then `p ≥ 2`".
* NO `hx0`/`hx`: unlike the `(Three)` route (whose `three_copy_base` needs
  `x ≤ 1/4` for the row-step side condition), the `(Two)` top rung is consumed
  DIRECTLY, and step 4's threshold identity is sign-free ceiling arithmetic.
  Flagged: the judge may reinstate the note's global `0 < x ≤ 1/4` for
  uniformity.
* `hY` omitted (derivable from `hTwo` + `hC` as in `one_bit_down_base`);
  `hC : 3 ≤ C` is the note's global regime, though only `1 ≤ C` is consumed
  here (for the `hY` derivation) — same weakness pattern as flagged on
  `nonconstant`, not changed.
* `hmargin` in the general-`y` form (2), as everywhere in E1/E2. -/

/-- **Note §4, MAIN Bob step at `a = 1`.** If Bob speaks first, the denser
child maximum-projected to TWO coordinates lands in the `(Two)` top rung:
a MAIN state at level `1` has complexity `≥ C+1`. -/
theorem main_bob_step_a1 {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p : ℕ) (x y lam : ℝ)
    (hp : 2 ≤ p)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam) (hX : 1 ≤ Fintype.card X) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p 1 x lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (subgame (interlaceFun W p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (subgame (interlaceFun W p) RC.1 RC.2)) :
    C + 1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  -- `hY` is derivable: empty `Y` (with `p ≥ 2`) empties the column set, so
  -- `hchild` would read `D + 1 ≤ D`.
  have hY : 1 ≤ Fintype.card Y := by
    by_contra hY0
    have hY0' : Fintype.card Y = 0 := by omega
    have hYempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0'
    have hnoc : ∀ c : Fin p → Y, False :=
      fun c => hYempty.false (c ⟨0, by omega⟩)
    have hempty2 : RC.2 = ∅ := by
      ext c
      exact (hnoc c).elim
    have h := hchild true
    rw [hempty2, Finset.filter_empty] at h
    omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- arithmetic facts about the level-1 budget `c_1(p) = p - 1`
  have hc1 : cExcess 1 p = (p : ℝ) - 1 := by
    unfold cExcess
    norm_num
  have hc_nonneg : 0 ≤ cExcess 1 p := by rw [hc1]; linarith
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hyc_one : Real.exp (-(cExcess 1 p * lam + Real.log 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cExcess 1 p * lam := mul_nonneg hc_nonneg hlam.le
    linarith
  -- Bob's first bit: one fiber keeps at least half the columns —
  -- column density `y_p / 2`, i.e. defect budget `+ ln 2`
  obtain ⟨b, hb⟩ := exists_denser_child RC.2 β
  have hKb_cols :
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess 1 p * lam + Real.log 2)) ≤
        (((RC.2.filter fun c => β c = b).card : ℝ)) := by
    have hsplit :
        Real.exp (-(cExcess 1 p * lam + Real.log 2)) =
          Real.exp (-(cExcess 1 p * lam)) / 2 := by
      rw [show -(cExcess 1 p * lam + Real.log 2) =
          -(cExcess 1 p * lam) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess 1 p * lam + Real.log 2))
          = (((Fintype.card Y : ℝ) ^ p) *
              Real.exp (-(cExcess 1 p * lam))) / 2 := by
            rw [hsplit]; ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  -- maximum projection to TWO coordinates (`ℓ = 2`, `T = A_1`)
  obtain ⟨R', C', hrows', hcols', hDle⟩ :=
    member_max_projection W p 2 (rowThreshold (Fintype.card X) x 1)
      (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
      (by norm_num) hp (Real.exp_pos _) hyc_one hX hY
      RC.1 (RC.2.filter fun c => β c = b) hrows hKb_cols
  -- budget: `(2/p)(c_1(p)λ + ln 2) ≤ 2λ + ln 2 ≤ 3λ + (7/5)ln 2 ≤ -2 ln y`
  have hc_scaled : 2 / (p : ℝ) * cExcess 1 p ≤ 2 := by
    rw [hc1, div_mul_eq_mul_div, div_le_iff₀ hp0]
    nlinarith
  have hlog_scaled : 2 / (p : ℝ) * Real.log 2 ≤ Real.log 2 := by
    have h2p : 2 / (p : ℝ) ≤ 1 := by
      rw [div_le_one hp0]; linarith
    calc
      2 / (p : ℝ) * Real.log 2 ≤ 1 * Real.log 2 :=
        mul_le_mul_of_nonneg_right h2p hlog2
      _ = Real.log 2 := one_mul _
  have hbudget :
      2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2) ≤ -2 * Real.log y := by
    calc
      2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2)
          = (2 / (p : ℝ) * cExcess 1 p) * lam +
              2 / (p : ℝ) * Real.log 2 := by ring
      _ ≤ 2 * lam + Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hc_scaled hlam.le) hlog_scaled
      _ ≤ 3 * lam + (7 / 5) * Real.log 2 := by linarith
      _ ≤ -2 * Real.log y := hmargin
  -- hence the projected density dominates `y²`
  have hrpow_eq :
      Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2))) (2 / (p : ℝ)) =
        Real.exp (-(cExcess 1 p * lam + Real.log 2) * (2 / (p : ℝ))) := by
    change (Real.exp _) ^ (2 / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hy_sq_exp : y ^ 2 = Real.exp (2 * Real.log y) := by
    calc
      y ^ 2 = (Real.exp (Real.log y)) ^ 2 := by rw [Real.exp_log hy0]
      _ = Real.exp (2 * Real.log y) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hy2_le :
      y ^ 2 ≤
        Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
          (2 / (p : ℝ)) := by
    rw [hy_sq_exp, hrpow_eq, Real.exp_le_exp,
      show -(cExcess 1 p * lam + Real.log 2) * (2 / (p : ℝ)) =
        -(2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2)) from by ring]
    linarith
  -- the projected member lands in `bracketGE X Y 2 (2x) (y²)`
  have hmem2 : (R', C') ∈ bracketGE X Y 2 (2 * x) (y ^ 2) := by
    refine ⟨?_, ?_⟩
    · intro j hj
      refine le_trans (le_of_eq ?_) (hrows' j hj)
      unfold rowThreshold
      congr 1
      ring
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ 2) * y ^ 2
            ≤ ((Fintype.card Y : ℝ) ^ 2) *
                Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
                  (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hy2_le (by positivity)
        _ ≤ (C'.card : ℝ) := by exact_mod_cast hcols'
  -- chain through the `(Two)` TOP rung, then Bob's bit closes
  have hchain :
      C ≤ D (subgame (interlaceFun W p)
        RC.1 (RC.2.filter fun c => β c = b)) := by
    calc
      C ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) :=
        le_trans hTwo (min_le_left _ _)
      _ ≤ Dfamily (interlaceFun W 2) {(R', C')} :=
        Dfamily.anti_mono _ (Set.singleton_subset_iff.mpr hmem2)
          (Set.singleton_nonempty _)
      _ = D (subgame (interlaceFun W 2) R' C') := Dfamily.singleton _ _
      _ ≤ _ := hDle
  calc
    C + 1 ≤ D (subgame (interlaceFun W p)
        RC.1 (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hchain 1
    _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild b

/-! ## The MAIN Bob step at `a ≥ 2`

Note §4 "Main statement: induction": "If Bob speaks, the denser child has
defect at most `c_a(p)λ + ln 2 ≤ c_a(p)λ + B(p)` by (5). It is therefore a
one-bit-down state at the SAME level `a`, whose complexity is at least
`C+a-1`."

Proof route — NO projection at all (contrast with the `(12)` Bob step):
1. `exists_denser_child`: Bob's denser fiber `(RC.1, RC.2.filter (β · = b))`
   has density `≥ y_p/2 = e^{-(c_a(p)λ + ln 2)}`;
2. `Bdef_ge_log2` (5): `ln 2 ≤ B(p)` (`p ≥ 2` from `hp`), so the fiber's
   density is `≥ e^{-(c_a(p)λ + B(p))}` — it is a member of
   `obdState X Y p a x lam` at the SAME level `a` and copy count `p` (its
   rows are the parent's, untouched);
3. `one_bit_down` (`eth:thm-obd`, PROVED): the fiber has complexity
   `≥ C + (a-1)`; `hchild b` adds Bob's bit: parent `≥ C + a`.

JUDGE FLAGS.
* `hp : 2 ^ (a - 1) < p` in E2's ℕ form — equivalent to the doubled form for
  `a ≥ 2` (see file header) and forwarded verbatim to `one_bit_down`.
* Hypothesis set = `one_bit_down`'s (the fiber consumes it wholesale; in
  particular `hx0`, `hx`, `hY` are all genuinely forwarded), and its
  conclusion-side `ha : 2 ≤ a` keeps `C + (a-1) + 1 = C + a` ℕ-exact.
* `stateDensity_subset_obdState` (Induction.lean:1542) is NOT sufficient here:
  the parent is a main state, but the DENSER CHILD (post-filter) is what must
  be an `obdState` member — the `ln 2 ≤ B(p)` slack is spent on Bob's bit, so
  membership is via steps 1–2, not the subset glue. -/

/-- **Note §4, MAIN Bob step at `a ≥ 2`.** If Bob speaks first, the denser
child is a one-bit-down `(12)` state at the SAME level `a` (budget
`c_a(p)λ + ln 2 ≤ c_a(p)λ + B(p)`, note (5)); `one_bit_down` gives it
`≥ C+a-1`, so a MAIN state at level `a` has complexity `≥ C+a`. -/
theorem main_bob_step {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x y lam : ℝ)
    (ha : 2 ≤ a) (hp : 2 ^ (a - 1) < p)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p a x lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (subgame (interlaceFun W p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (subgame (interlaceFun W p) RC.1 RC.2)) :
    C + a ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hpow2 : 2 ≤ 2 ^ (a - 1) := by
    calc
      (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ≤ p := by omega
  -- note (5): `ln 2 ≤ B(p)`
  have hlog2B : Real.log 2 ≤ Bdef p := Bdef_ge_log2 p hp2
  -- Bob's first bit: one fiber keeps at least half the columns
  obtain ⟨b, hb⟩ := exists_denser_child RC.2 β
  -- the denser fiber is a `(12)` state at the SAME level `a`, copy count `p`
  have hmem' : (RC.1, RC.2.filter fun c => β c = b) ∈
      obdState X Y p a x lam := by
    refine ⟨hrows, ?_⟩
    have hhalf : Real.exp (-(cExcess a p * lam + Bdef p)) ≤
        Real.exp (-(cExcess a p * lam + Real.log 2)) := by
      rw [Real.exp_le_exp]
      linarith
    have hsplit :
        Real.exp (-(cExcess a p * lam + Real.log 2)) =
          Real.exp (-(cExcess a p * lam)) / 2 := by
      rw [show -(cExcess a p * lam + Real.log 2) =
          -(cExcess a p * lam) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess a p * lam + Bdef p))
          ≤ ((Fintype.card Y : ℝ) ^ p) *
              Real.exp (-(cExcess a p * lam + Real.log 2)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = (((Fintype.card Y : ℝ) ^ p) *
            Real.exp (-(cExcess a p * lam))) / 2 := by
          rw [hsplit]; ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  -- `one_bit_down` (`eth:thm-obd`) on the fiber, then Bob's bit closes
  have hobd := one_bit_down W C p a x y lam ha hp hx0 hx hy0 hy1 hlam hX hY hC
    hmargin hTwo (RC.1, RC.2.filter fun c => β c = b) hmem'
  calc
    C + a = (C + (a - 1)) + 1 := by omega
    _ ≤ D (subgame (interlaceFun W p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hobd 1
    _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild b

/-! ## `eth:thm-main` — Theorem 1, the assembled induction (note (11))

Note §4 Theorem 1: assume `(Near)`, `(Two)`, and (2); let `a ≥ 0` satisfy
`2^a·x ≤ 1`. Every restriction of `Interlace(W,p)` with `p > 2^(a-1)`, at
least `A_a` rows in every active block, and `Def(K) ≤ c_a(p)·λ` has
communication complexity at least `C+a`.

Proof route: induction on `a` (plain `Nat.rec`, `p` and the member universally
quantified inside):
* `a = 0`: `terminal_a0_member` (`1 ≤ p` from the doubled `hp`).
* `a+1 ≥ 1`: the state is nonconstant — `main_nonconstant` (Bases.lean:283,
  PROVED; needs `1 ≤ C` from `hC`, `x ≤ 1` from `hx`) — so
  `subgame_first_bit_dichotomy` yields a first bit;
  - Alice: `main_alice_step` at level `a+1`, its `IH` being the induction
    hypothesis (at `a = 0` reshaped through `terminal_a0_member`);
  - Bob, `a+1 = 1`: `main_bob_step_a1` (`2 ≤ p` from the doubled `hp`);
  - Bob, `a+1 ≥ 2`: `main_bob_step` (doubled `hp` halves to E2's form).

JUDGE FLAGS.
* `hp : 2 ^ a < 2 * p` — the ℕ-truncation-safe rendering of the note's
  `p > 2^(a-1)` valid at EVERY level including `a = 0` (see file header). This
  is the ONE place E3 deliberately deviates from E2's `2 ^ (a - 1) < p`
  spelling (which is wrong at `a = 0`).
* `hax` carried for fidelity to the note's Theorem 1; expected unconsumed in
  the per-member proof (see file header).
* Hypothesis set is the UNION of the branch needs (mirroring `one_bit_down`):
  `hNear` (terminal + nonconstancy) AND `hTwo`+`hmargin` (Bob branches),
  `hx0`/`hx`, `hlam`, `hX`, `hY` (redundantly derivable, kept for E2 parity),
  `hC : 3 ≤ C`.
* Conclusion `C + a` is ℕ-clean (no subtraction anywhere).
* Per-member form = the note's "every restriction … has complexity at least
  `C+a`" (11), and the shape Theorem 2 (E4) consumes on its chosen good-block
  projection. -/

/-- **`eth:thm-main` (note §4 Theorem 1, (11)).** Assume `(Near)`, `(Two)`,
and the margin (2). For `a ≥ 0` with `2^a·x ≤ 1` and `p > 2^(a-1)`, every
member of the level-`a` MAIN state family (rows `≥ A_a` per block, defect
`≤ c_a(p)·λ`) has communication complexity at least `C + a`. -/
theorem theorem_one {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x y lam : ℝ)
    (hp : 2 ^ a < 2 * p) (hax : (2 : ℝ) ^ a * x ≤ 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : NearFull W C x lam) (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p a x lam) :
    C + a ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  -- `hax` is unconsumed in the per-member proof (as flagged); drop it so the
  -- induction motive does not carry it.
  clear hax
  revert p hp RC hmem
  induction a with
  | zero =>
    intro p hp RC hmem
    -- `hp : 2 ^ 0 < 2 * p` reads `1 ≤ p`
    have hp1 : 1 ≤ p := by
      have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    exact terminal_a0_member W C p x lam hp1 hx0 (by linarith) hlam hX hNear
      RC hmem
  | succ a IH =>
    intro p hp RC hmem
    have hpow_succ : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by
      rw [pow_succ]; ring
    have hpow1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
    have hp1 : 1 ≤ p := by omega
    -- nonconstancy: a first bit exists
    have hnc : 1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) :=
      main_nonconstant W C p (a + 1) x lam hp1 hx0 (by linarith) hlam hX
        (by omega) hNear RC hmem
    rcases subgame_first_bit_dichotomy (interlaceFun W p) RC.1 RC.2 hnc with
      ⟨α, hchild⟩ | ⟨β, hchild⟩
    · -- Alice speaks: the MAIN Alice step, IH = the induction hypothesis
      exact main_alice_step W C p (a + 1) x lam (by omega) hp hlam hX hY
        RC hmem α hchild IH
    · -- Bob speaks: split on the level
      rcases Nat.eq_zero_or_pos a with rfl | ha1
      · -- level `a + 1 = 1`: the `(Two)` top-rung Bob step
        have hp2 : 2 ≤ p := by omega
        exact main_bob_step_a1 W C p x y lam hp2 hy0 hy1 hlam hX hC hmargin
          hTwo RC hmem β hchild
      · -- level `a + 1 ≥ 2`: the one-bit-down Bob step
        have hp' : 2 ^ a < p := by omega
        exact main_bob_step W C p (a + 1) x y lam (by omega) hp' hx0 hx hy0
          hy1 hlam hX hY hC hmargin hTwo RC hmem β hchild

/-- **Theorem 1, family form (note (11) through `stateComp`).** The
`Dfamily`-min rendering scaffolded in `EthBridge.Defs`: every member bound
(from `theorem_one`) plus nonemptiness of the family — witnessed by
`(univ, univ)` under `hax` and `0 ≤ c_a(p)·λ` (from `hp`+`hlam`), cf. the
`stateDensity` inhabitation unit test — gives `C + a ≤ stateComp`. This is
where `hax` is genuinely consumed. -/
theorem theorem_one_family {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x y lam : ℝ)
    (hp : 2 ^ a < 2 * p) (hax : (2 : ℝ) ^ a * x ≤ 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : NearFull W C x lam) (hTwo : TwoCopyBundle W C x y) :
    C + a ≤ stateComp X Y W p a x lam := by
  classical
  -- `0 ≤ c_a(p)·λ`, from `hp` (doubled form) + `hlam`
  have hcast : (2 : ℝ) ^ a < 2 * (p : ℝ) := by exact_mod_cast hp
  have hzpow : (2 : ℝ) ^ ((a : ℤ) - 1) = (2 : ℝ) ^ a / 2 := by
    rw [show (a : ℤ) - 1 = (a : ℤ) + (-1) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_neg_one]
    ring
  have hc_pos : 0 < cExcess a p := by
    unfold cExcess
    rw [hzpow]
    linarith
  -- the family is nonempty: `(univ, univ)` is a member under `hax` (this is
  -- where `hax` is genuinely consumed), cf. the `stateDensity` inhabitation
  -- unit test
  have hwit : ((Finset.univ : Finset (Fin p × X)),
      (Finset.univ : Finset (Fin p → Y))) ∈ stateDensity X Y p a x lam := by
    refine ⟨IsEquipartitionedGE.univ _ _ ?_, ?_⟩
    · -- row threshold: `A_a ≤ |X|` under `2^a·x ≤ 1`
      unfold rowThreshold
      refine Nat.ceil_le.mpr ?_
      have hstep : (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x) ≤
          (Fintype.card X : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hax (by positivity)
      calc (Fintype.card X : ℝ) * (2 : ℝ) ^ a * x
            = (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * x) := by ring
        _ ≤ (Fintype.card X : ℝ) * 1 := hstep
        _ = (Fintype.card X : ℝ) := mul_one _
    · -- density: the bound is `≤ n^p` since `0 ≤ c_a(p)·λ`
      have hexp : Real.exp (-(cExcess a p * lam)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ cExcess a p * lam := mul_nonneg hc_pos.le hlam.le
        linarith
      have hcard : (Finset.univ : Finset (Fin p → Y)).card =
          Fintype.card Y ^ p := by
        rw [Finset.card_univ, Fintype.card_pi_const]
      rw [hcard]
      calc ((Fintype.card Y : ℝ) ^ p) * Real.exp (-(cExcess a p * lam))
            ≤ ((Fintype.card Y : ℝ) ^ p) * 1 :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = ((Fintype.card Y ^ p : ℕ) : ℝ) := by push_cast; ring
  -- descend: the `Dfamily` min is attained at a member; bound it by
  -- `theorem_one`
  unfold stateComp Dfamily
  have hne : { d : ℕ | ∃ RC ∈ stateDensity X Y p a x lam,
      d = D (subgame (interlaceFun W p) RC.1 RC.2) }.Nonempty :=
    ⟨_, ⟨_, hwit, rfl⟩⟩
  obtain ⟨RC, hRC, heq⟩ := Nat.sInf_mem hne
  rw [heq]
  exact theorem_one W C p a x y lam hp hax hx0 hx hy0 hy1 hlam hX hY hC
    hmargin hNear hTwo RC hRC

end EthBridge
