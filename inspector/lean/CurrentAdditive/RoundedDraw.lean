import CurrentAdditive.ProjectionTVBridge
import Paper2.ClassicalSeparation
import Paper2.CappedSamplerCouplingAdaptive
import Paper2.CappedSamplerCouplingPrefix

/-! Fixed-bit rounded sampling from v37 and selected v38,
    `source/appendices/access.tex`, equation `eq:rounded-draw`.
    In v38 the joint error appears in the unnumbered fixed-bit portion of
    the proof of `lem:sample-access` (lines 83--115). -/

namespace CurrentAdditive.RoundedDraw

open Paper2
open CurrentAdditive.FourthMoment.ProjectionTVBridge

def draw (a M : ℕ) (ha : 0 < a) (hM : 0 < M) (u : Fin M) : Fin a :=
  ⟨a * u.val / M, by
    apply (Nat.div_lt_iff_lt_mul hM).2
    have hu := u.isLt
    nlinarith⟩

private theorem ceilDiv_add_mul (x q a : ℕ) (ha : 0 < a) :
    (x + q * a) ⌈/⌉ a = x ⌈/⌉ a + q := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  have heq : x + q * a + a - 1 = (x + a - 1) + a * q := by
    have : 1 ≤ a := ha
    rw [mul_comm q a]
    omega
  rw [heq, Nat.add_mul_div_left _ q ha]

private theorem ceilDiv_step (x r a : ℕ) (ha : 0 < a) (hr : r < a) :
    (x + r) ⌈/⌉ a = x ⌈/⌉ a ∨
      (x + r) ⌈/⌉ a = x ⌈/⌉ a + 1 := by
  have hlow : x ⌈/⌉ a ≤ (x + r) ⌈/⌉ a :=
    (ceilDiv_le_iff_le_mul ha).2 (by
      have := (ceilDiv_le_iff_le_mul ha).1
        (le_refl ((x + r) ⌈/⌉ a))
      omega)
  have hhigh : (x + r) ⌈/⌉ a ≤ x ⌈/⌉ a + 1 :=
    (ceilDiv_le_iff_le_mul ha).2 (by
      have := (ceilDiv_le_iff_le_mul ha).1 (le_refl (x ⌈/⌉ a))
      nlinarith)
  omega

private theorem ceilDiv_stride (x M a : ℕ) (ha : 0 < a) :
    (x + M) ⌈/⌉ a - x ⌈/⌉ a = M / a ∨
    (x + M) ⌈/⌉ a - x ⌈/⌉ a = M / a + 1 := by
  let q := M / a
  let r := M % a
  have hM : M = q * a + r := by
    dsimp [q, r]
    have := Nat.mod_add_div M a
    nlinarith
  have hr : r < a := Nat.mod_lt _ ha
  have hstep := ceilDiv_step x r a ha hr
  have hshift : (x + M) ⌈/⌉ a = (x + r) ⌈/⌉ a + q := by
    have harg : x + M = (x + r) + q * a := by omega
    rw [harg, ceilDiv_add_mul (x + r) q a ha]
  have hres : (x + M) ⌈/⌉ a - x ⌈/⌉ a = q ∨
      (x + M) ⌈/⌉ a - x ⌈/⌉ a = q + 1 := by
    rw [hshift]
    rcases hstep with hs | hs
    · left
      rw [hs]
      exact Nat.add_sub_cancel_left _ _
    · right
      rw [hs]
      calc
        x ⌈/⌉ a + 1 + q - x ⌈/⌉ a = 1 + q := by
          rw [add_assoc]
          exact Nat.add_sub_cancel_left _ _
        _ = q + 1 := by ac_rfl
  simpa only [q] using hres

theorem draw_eq_iff (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (u : Fin M) (j : Fin a) :
    draw a M ha hM u = j ↔
      (j.val * M) ⌈/⌉ a ≤ u.val ∧
        u.val < ((j.val + 1) * M) ⌈/⌉ a := by
  rw [Fin.ext_iff]
  change a * u.val / M = j.val ↔ _
  constructor
  · intro h
    constructor
    · apply (ceilDiv_le_iff_le_mul ha).2
      have := (Nat.le_div_iff_mul_le hM).1 (le_of_eq h.symm)
      nlinarith
    · apply lt_of_not_ge
      intro hcontra
      have hh := (ceilDiv_le_iff_le_mul ha).1 hcontra
      have hj : j.val + 1 ≤ a * u.val / M :=
        (Nat.le_div_iff_mul_le hM).2 (by nlinarith)
      omega
  · rintro ⟨hlo, hhi⟩
    have hl := (ceilDiv_le_iff_le_mul ha).1 hlo
    have hh : a * u.val < (j.val + 1) * M := by
      by_contra h
      have hc := (ceilDiv_le_iff_le_mul ha).2 (Nat.le_of_not_lt h)
      omega
    apply Nat.le_antisymm
    · have hlt := (Nat.div_lt_iff_lt_mul hM).2 hh
      omega
    · exact (Nat.le_div_iff_mul_le hM).2 (by nlinarith)

def fibre (a M : ℕ) (ha : 0 < a) (hM : 0 < M) (j : Fin a) :
    Finset (Fin M) :=
  Finset.univ.filter (fun u => draw a M ha hM u = j)

theorem fibre_card (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (j : Fin a) :
    (fibre a M ha hM j).card =
      ((j.val + 1) * M) ⌈/⌉ a - (j.val * M) ⌈/⌉ a := by
  classical
  let lo := (j.val * M) ⌈/⌉ a
  let hi := ((j.val + 1) * M) ⌈/⌉ a
  have hhi : hi ≤ M :=
    (ceilDiv_le_iff_le_mul ha).2 (by
      have hj : j.val + 1 ≤ a := j.isLt
      exact Nat.mul_le_mul_right M hj |>.trans_eq (by ac_rfl))
  have hc : (fibre a M ha hM j).card = (Finset.Ico lo hi).card := by
    apply Finset.card_bij (fun u _ => u.val)
    · intro u hu
      have heq : draw a M ha hM u = j := (Finset.mem_filter.mp hu).2
      exact Finset.mem_Ico.mpr ((draw_eq_iff a M ha hM u j).1 heq)
    · intro u hu v hv heq
      exact Fin.ext heq
    · intro x hx
      have hxM : x < M := lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 hhi
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (draw_eq_iff a M ha hM ⟨x, hxM⟩ j).2
        (Finset.mem_Ico.mp hx)⟩
  simpa only [Nat.card_Ico, lo, hi] using hc

theorem fibre_card_floor_or_ceil (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (j : Fin a) :
    (fibre a M ha hM j).card = M / a ∨
      (fibre a M ha hM j).card = M / a + 1 := by
  rw [fibre_card]
  have harg : (j.val + 1) * M = j.val * M + M := by ring
  rw [harg]
  exact ceilDiv_stride (j.val * M) M a ha

/-- Exact floor-or-ceiling statement, including the divisible case where the
floor and ceiling coincide. -/
theorem fibre_card_exact_floor_or_ceil (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (j : Fin a) :
    (fibre a M ha hM j).card = M / a ∨
      (fibre a M ha hM j).card = M ⌈/⌉ a := by
  let q := M / a
  let r := M % a
  have hMqr : M = q * a + r := by
    dsimp [q, r]
    have := Nat.mod_add_div M a
    nlinarith
  by_cases hr0 : r = 0
  · left
    rw [fibre_card]
    have harg : (j.val + 1) * M = j.val * M + M := by ring
    have hdiv : M = q * a := by omega
    rw [harg, hdiv, ceilDiv_add_mul (j.val * (q * a)) q a ha]
    have hquot : q * a / a = q := by
      simpa only [mul_comm] using Nat.mul_div_cancel_left q ha
    rw [hquot]
    exact Nat.add_sub_cancel_left _ _
  · have hr : r < a := Nat.mod_lt M ha
    have hrceil : r ⌈/⌉ a = 1 := by
      apply Nat.le_antisymm
      · exact (ceilDiv_le_iff_le_mul ha).2 (by omega)
      · by_contra h
        have hz : r ⌈/⌉ a = 0 := by omega
        have hle := (ceilDiv_le_iff_le_mul ha).1 (show r ⌈/⌉ a ≤ 0 by omega)
        omega
    have hceil : M ⌈/⌉ a = q + 1 := by
      have harg : M = r + q * a := by omega
      rw [harg, ceilDiv_add_mul r q a ha, hrceil]
      omega
    rcases fibre_card_floor_or_ceil a M ha hM j with hf | hc
    · exact Or.inl hf
    · exact Or.inr (by simpa [q, hceil] using hc)

noncomputable def roundedLaw (a M : ℕ) (ha : 0 < a) (hM : 0 < M) :
    FiniteLaw (Fin a) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact mapLaw (FiniteLaw.uniform (Fin M)) (draw a M ha hM)

noncomputable def idealUniform (a : ℕ) (ha : 0 < a) :
    FiniteLaw (Fin a) := by
  letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact FiniteLaw.uniform (Fin a)

theorem roundedLaw_weight (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (j : Fin a) :
    (roundedLaw a M ha hM).weight j =
      ((fibre a M ha hM j).card : ℝ) / M := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  change (FiniteLaw.uniform (Fin M)).prob
    (fun u => draw a M ha hM u = j) = _
  simpa [fibre] using FiniteLaw.uniform_prob_finset (fibre a M ha hM j)

theorem roundedLaw_pointwise (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (j : Fin a) :
    |(roundedLaw a M ha hM).weight j - (1 : ℝ) / a| ≤ (1 : ℝ) / M := by
  let q := M / a
  let r := M % a
  have hMqr : M = q * a + r := by
    dsimp [q, r]
    have := Nat.mod_add_div M a
    nlinarith
  have hr : r < a := Nat.mod_lt M ha
  have hq := fibre_card_floor_or_ceil a M ha hM j
  rw [roundedLaw_weight]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hrR : (r : ℝ) ≤ a := by exact_mod_cast hr.le
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hMqrR : (M : ℝ) = q * a + r := by exact_mod_cast hMqr
  rcases hq with hq | hq
  · rw [hq]
    apply abs_le.mpr
    constructor <;> field_simp <;> nlinarith
  · rw [hq]
    push_cast
    apply abs_le.mpr
    constructor <;> field_simp <;> nlinarith

theorem roundedLaw_event (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (E : Fin a → Prop) :
    |(roundedLaw a M ha hM).prob E -
      (idealUniform a ha).prob E| ≤ (a : ℝ) / M := by
  letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  classical
  have hpoint (j : Fin a) :
      |(roundedLaw a M ha hM).weight j -
        (idealUniform a ha).weight j| ≤ (1 : ℝ) / M := by
    simpa [idealUniform, FiniteLaw.uniform] using roundedLaw_pointwise a M ha hM j
  unfold FiniteLaw.prob
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin a, ((if E j then (roundedLaw a M ha hM).weight j else 0) -
          (if E j then (idealUniform a ha).weight j else 0))| ≤
      ∑ j : Fin a,
        |(if E j then (roundedLaw a M ha hM).weight j else 0) -
          (if E j then (idealUniform a ha).weight j else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin a, (1 : ℝ) / M := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : E j
      · simpa [hj] using hpoint j
      · simp [hj]
    _ = (a : ℝ) / M := by simp [div_eq_mul_inv]

theorem roundedLaw_map_event {T : Type*} [Fintype T]
    (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (f : Fin a → T) (E : T → Prop) :
    |(mapLaw (roundedLaw a M ha hM) f).prob E -
      (mapLaw (idealUniform a ha) f).prob E| ≤ (a : ℝ) / M := by
  letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  rw [mapLaw_prob, mapLaw_prob]
  exact roundedLaw_event a M ha hM (fun j => E (f j))

private theorem weighted_pointwise_error {X : Type*} [Fintype X]
    (μ ν : FiniteLaw X) (g : X → ℝ) (δ : ℝ)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hd : ∀ x, |μ.weight x - ν.weight x| ≤ δ) :
    |(∑ x, μ.weight x * g x) - (∑ x, ν.weight x * g x)| ≤
      (Fintype.card X : ℝ) * δ := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hterm (x : X) : |(μ.weight x - ν.weight x) * g x| ≤ δ := by
    rw [abs_mul, abs_of_nonneg (hg x).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hg x).2).trans (hd x)
  calc
    |∑ x, (μ.weight x * g x - ν.weight x * g x)| =
      |∑ x, (μ.weight x - ν.weight x) * g x| := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ ≤ ∑ x, |(μ.weight x - ν.weight x) * g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : X, δ := Finset.sum_le_sum (fun x _ => hterm x)
    _ = (Fintype.card X : ℝ) * δ := by simp

private theorem weighted_continuation_error {X : Type*} [Fintype X]
    (ν : FiniteLaw X) (f g : X → ℝ) (δ : ℝ)
    (hd : ∀ x, |f x - g x| ≤ δ) :
    |(∑ x, ν.weight x * f x) - (∑ x, ν.weight x * g x)| ≤ δ := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (ν.weight x * f x - ν.weight x * g x)| =
      |∑ x, ν.weight x * (f x - g x)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ ≤ ∑ x, |ν.weight x * (f x - g x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ν.weight x * δ := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (ν.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hd x) (ν.nonneg x)
    _ = δ := by rw [← Finset.sum_mul, ν.total, one_mul]

/-- A fixed reservoir of `n` independent `M`-way tickets. -/
def Tape (M : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin M × Tape M n

instance tapeFintype (M n : ℕ) : Fintype (Tape M n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Fin M × Tape M n))

noncomputable def tapeLaw (M : ℕ) (hM : 0 < M) :
    (n : ℕ) → FiniteLaw (Tape M n)
  | 0 => { weight := fun _ => 1, nonneg := by intros; norm_num,
           total := by simp [Tape] }
  | n + 1 => by
      letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      exact (FiniteLaw.uniform (Fin M)).prod (tapeLaw M hM n)

def runRounded {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (M : ℕ) (hM : 0 < M) (hD : ∀ s, 0 < D s) :
    (n : ℕ) → S → Tape M n → S
  | 0, s, _ => s
  | n + 1, s, t =>
      runRounded D next M hM hD n
        (next s (draw (D s) M (hD s) hM t.1)) t.2

theorem runRounded_prob_succ {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (M : ℕ) (hM : 0 < M) (hD : ∀ s, 0 < D s)
    (n : ℕ) (s : S) (E : S → Prop) :
    (tapeLaw M hM (n + 1)).prob
        (fun t => E (runRounded D next M hM hD (n + 1) s t)) =
      ∑ j : Fin (D s), (roundedLaw (D s) M (hD s) hM).weight j *
        (tapeLaw M hM n).prob
          (fun t => E (runRounded D next M hM hD n (next s j) t)) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let H : Fin M → Tape M n → Prop := fun u t =>
    E (runRounded D next M hM hD n
      (next s (draw (D s) M (hD s) hM u)) t)
  change ((FiniteLaw.uniform (Fin M)).prod (tapeLaw M hM n)).prob
      (fun t => H t.1 t.2) = _
  rw [FiniteLaw.prod_prob (FiniteLaw.uniform (Fin M)) (tapeLaw M hM n) H]
  let g : Fin (D s) → ℝ := fun j =>
    (tapeLaw M hM n).prob
      (fun t => E (runRounded D next M hM hD n (next s j) t))
  change (∑ u : Fin M, (FiniteLaw.uniform (Fin M)).weight u *
    g (draw (D s) M (hD s) hM u)) =
      ∑ j : Fin (D s), (roundedLaw (D s) M (hD s) hM).weight j * g j
  simpa only [FourthMoment.expect, roundedLaw] using
    (mapLaw_expect (FiniteLaw.uniform (Fin M))
      (draw (D s) M (hD s) hM) g).symm

/-- Adaptive first-disagreement accounting, expressed as all-event total
variation. `n` fresh uniform tickets are reserved even if a branch finishes
early; the next alphabet and transition may depend on the entire history. -/
theorem adaptive_event_error {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (M A : ℕ) (hM : 0 < M) (hD : ∀ s, 0 < D s)
    (hA : ∀ s, D s ≤ A) (n : ℕ) (s : S) (E : S → Prop) :
    |(tapeLaw M hM n).prob
        (fun t => E (runRounded D next M hM hD n s t)) -
      Paper2.CappedSampler.Adaptive.idealMass D next hD n s E| ≤
        (n : ℝ) * (A : ℝ) / M := by
  induction n generalizing s with
  | zero =>
      classical
      have hcard : Fintype.card (Tape M 0) = 1 := by
        change Fintype.card Unit = 1
        simp
      simp [tapeLaw, runRounded, Paper2.CappedSampler.Adaptive.idealMass,
        FiniteLaw.prob, hcard]
  | succ n ih =>
      let α := D s
      let μ := roundedLaw α M (hD s) hM
      let ν := idealUniform α (hD s)
      let f : Fin α → ℝ := fun j =>
        (tapeLaw M hM n).prob
          (fun t => E (runRounded D next M hM hD n (next s j) t))
      let g : Fin α → ℝ := fun j =>
        Paper2.CappedSampler.Adaptive.idealMass D next hD n (next s j) E
      have hr : (tapeLaw M hM (n + 1)).prob
          (fun t => E (runRounded D next M hM hD (n + 1) s t)) =
          ∑ j : Fin α, μ.weight j * f j := by
        exact runRounded_prob_succ D next M hM hD n s E
      have hi : Paper2.CappedSampler.Adaptive.idealMass
          D next hD (n + 1) s E =
          ∑ j : Fin α, ν.weight j * g j := by
        change (∑ j : Fin α,
          (Paper2.CappedSampler.uniformTicket α (hD s)).weight j * g j) = _
        apply Finset.sum_congr rfl
        intro j _
        simp [ν, idealUniform, FiniteLaw.uniform,
          Paper2.CappedSampler.uniformTicket]
      have hpoint (j : Fin α) : |μ.weight j - ν.weight j| ≤ (1 : ℝ) / M := by
        simpa [μ, ν, idealUniform, FiniteLaw.uniform] using
          roundedLaw_pointwise α M (hD s) hM j
      have hf (j : Fin α) : 0 ≤ f j ∧ f j ≤ 1 :=
        ⟨(tapeLaw M hM n).prob_nonneg _,
          (tapeLaw M hM n).prob_le_one _⟩
      have hfirst : |(∑ j : Fin α, μ.weight j * f j) -
          (∑ j : Fin α, ν.weight j * f j)| ≤ (α : ℝ) / M := by
        simpa [div_eq_mul_inv, α] using
          weighted_pointwise_error μ ν f ((1 : ℝ) / M) hf hpoint
      have hnext (j : Fin α) : |f j - g j| ≤ (n : ℝ) * (A : ℝ) / M :=
        ih (next s j)
      have hsecond : |(∑ j : Fin α, ν.weight j * f j) -
          (∑ j : Fin α, ν.weight j * g j)| ≤
          (n : ℝ) * (A : ℝ) / M :=
        weighted_continuation_error ν f g _ hnext
      rw [hr, hi]
      have hα : (α : ℝ) ≤ A := by exact_mod_cast hA s
      have hdiv : (α : ℝ) / M ≤ (A : ℝ) / M := by
        exact div_le_div_of_nonneg_right hα (Nat.cast_nonneg M)
      calc
        |(∑ j : Fin α, μ.weight j * f j) -
          (∑ j : Fin α, ν.weight j * g j)| ≤
            |(∑ j : Fin α, μ.weight j * f j) -
              (∑ j : Fin α, ν.weight j * f j)| +
            |(∑ j : Fin α, ν.weight j * f j) -
              (∑ j : Fin α, ν.weight j * g j)| := by
                exact abs_sub_le _ _ _
        _ ≤ (α : ℝ) / M + (n : ℝ) * (A : ℝ) / M := add_le_add hfirst hsecond
        _ ≤ (A : ℝ) / M + (n : ℝ) * (A : ℝ) / M := by linarith
        _ = (n + 1 : ℕ) * (A : ℝ) / M := by push_cast; ring

/-- The concrete manuscript budget gives error at most one in two hundred
for every event in the joint result. -/
theorem adaptive_event_error_200 {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (b A N : ℕ) (hD : ∀ s, 0 < D s)
    (hA : ∀ s, D s ≤ A) (hbudget : 200 * A * N ≤ 2 ^ b)
    (s : S) (E : S → Prop) :
    |(tapeLaw (2 ^ b) (by positivity) N).prob
        (fun t => E (runRounded D next (2 ^ b) (by positivity) hD N s t)) -
      Paper2.CappedSampler.Adaptive.idealMass D next hD N s E| ≤
        (1 : ℝ) / 200 := by
  have hbase := adaptive_event_error D next (2 ^ b) A
    (by positivity) hD hA N s E
  apply hbase.trans
  have hbudgetR : (200 : ℝ) * (A : ℝ) * (N : ℝ) ≤ (2 ^ b : ℝ) := by
    exact_mod_cast hbudget
  have hpow : (0 : ℝ) < (2 ^ b : ℝ) := by positivity
  push_cast
  apply (div_le_iff₀ hpow).2
  nlinarith

/-- The physical reservoir, one fresh `b`-bit block per possible draw. -/
def BitBlocks (b : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => (Fin b → Bool) × BitBlocks b n

instance bitBlocksFintype (b n : ℕ) : Fintype (BitBlocks b n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype ((Fin b → Bool) × BitBlocks b n))

noncomputable def bitBlocksLaw (b : ℕ) :
    (n : ℕ) → FiniteLaw (BitBlocks b n)
  | 0 => { weight := fun _ => 1, nonneg := by intros; norm_num,
           total := by simp [BitBlocks] }
  | n + 1 => (Paper2.CappedSampler.fairBits b).prod (bitBlocksLaw b n)

def encodeBlocks (b : ℕ) :
    (n : ℕ) → BitBlocks b n → Tape (2 ^ b) n
  | 0, _ => ()
  | n + 1, t =>
      (Paper2.CappedSampler.bitsTicketEquiv b t.1, encodeBlocks b n t.2)

/-- Binary conversion preserves the complete joint law of the reserved
blocks, not just their individual marginals. -/
theorem bitBlocks_prob (b n : ℕ) (E : Tape (2 ^ b) n → Prop) :
    (bitBlocksLaw b n).prob (fun bits => E (encodeBlocks b n bits)) =
      (tapeLaw (2 ^ b) (by positivity) n).prob E := by
  induction n with
  | zero =>
      classical
      have hc : Fintype.card (BitBlocks b 0) = 1 := by
        change Fintype.card Unit = 1
        simp
      have hE : ∀ x : Tape (2 ^ b) 0, E x ↔ E () := by
        intro x
        cases x
        rfl
      simp [bitBlocksLaw, tapeLaw, encodeBlocks, FiniteLaw.prob, hE, Tape, hc]
  | succ n ih =>
      letI : Nonempty (Fin (2 ^ b)) := ⟨⟨0, by positivity⟩⟩
      let H : (Fin b → Bool) → BitBlocks b n → Prop :=
        fun x y => E (Paper2.CappedSampler.bitsTicketEquiv b x,
          encodeBlocks b n y)
      change ((Paper2.CappedSampler.fairBits b).prod
        (bitBlocksLaw b n)).prob (fun t => H t.1 t.2) = _
      rw [FiniteLaw.prod_prob (Paper2.CappedSampler.fairBits b)
        (bitBlocksLaw b n) H]
      have htail (x : Fin b → Bool) :
          (bitBlocksLaw b n).prob (H x) =
            (tapeLaw (2 ^ b) (by positivity) n).prob
              (fun y => E (Paper2.CappedSampler.bitsTicketEquiv b x, y)) :=
        by simpa [H] using
          ih (fun y => E (Paper2.CappedSampler.bitsTicketEquiv b x, y))
      simp_rw [htail]
      have hfib (j : Fin (2 ^ b)) :
          (Paper2.CappedSampler.fairBits b).prob
            (fun x => Paper2.CappedSampler.bitsTicketEquiv b x = j) =
            (FiniteLaw.uniform (Fin (2 ^ b))).weight j := by
        rw [Paper2.CappedSampler.fairBits_ticket_singleton]
        simp [FiniteLaw.uniform]
      let g : Fin (2 ^ b) → ℝ := fun j =>
        (tapeLaw (2 ^ b) (by positivity) n).prob (fun y => E (j, y))
      have hsum := FiniteLaw.sum_mul_comp_of_fibres
        (Paper2.CappedSampler.fairBits b)
        (FiniteLaw.uniform (Fin (2 ^ b)))
        (Paper2.CappedSampler.bitsTicketEquiv b) hfib g
      have hprod := FiniteLaw.prod_prob
        (FiniteLaw.uniform (Fin (2 ^ b)))
        (tapeLaw (2 ^ b) (by positivity) n)
        (fun j y => E (j, y))
      calc
        (∑ x,
          (Paper2.CappedSampler.fairBits b).weight x *
            (tapeLaw (2 ^ b) (by positivity) n).prob
              (fun y => E (Paper2.CappedSampler.bitsTicketEquiv b x, y))) =
            ∑ j, (FiniteLaw.uniform (Fin (2 ^ b))).weight j * g j := hsum
        _ = (tapeLaw (2 ^ b) (by positivity) (n + 1)).prob E := by
          simpa [tapeLaw, g] using hprod.symm

def runBitsRounded {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (b : ℕ) (hD : ∀ s, 0 < D s)
    (n : ℕ) (s : S) (bits : BitBlocks b n) : S :=
  runRounded D next (2 ^ b) (by positivity) hD n s (encodeBlocks b n bits)

theorem bitBlocks_adaptive_event_error_200 {S : Type*} (D : S → ℕ)
    (next : (s : S) → Fin (D s) → S)
    (b A N : ℕ) (hD : ∀ s, 0 < D s)
    (hA : ∀ s, D s ≤ A) (hbudget : 200 * A * N ≤ 2 ^ b)
    (s : S) (E : S → Prop) :
    |(bitBlocksLaw b N).prob (fun bits => E (runBitsRounded D next b hD N s bits)) -
      Paper2.CappedSampler.Adaptive.idealMass D next hD N s E| ≤
        (1 : ℝ) / 200 := by
  have hbits := bitBlocks_prob b N
    (fun tickets => E (runRounded D next (2 ^ b) (by positivity) hD N s tickets))
  rw [show (bitBlocksLaw b N).prob
      (fun bits => E (runBitsRounded D next b hD N s bits)) =
      (tapeLaw (2 ^ b) (by positivity) N).prob
        (fun tickets => E (runRounded D next (2 ^ b) (by positivity) hD N s tickets))
      by simpa [runBitsRounded] using hbits]
  exact adaptive_event_error_200 D next b A N hD hA hbudget s E

#print axioms draw_eq_iff
#print axioms fibre_card_exact_floor_or_ceil
#print axioms roundedLaw_event
#print axioms roundedLaw_map_event
#print axioms adaptive_event_error_200
#print axioms bitBlocks_prob
#print axioms bitBlocks_adaptive_event_error_200

end CurrentAdditive.RoundedDraw
