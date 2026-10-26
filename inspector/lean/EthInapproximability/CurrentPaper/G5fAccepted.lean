import EthInapproximability.CurrentPaper.EffectiveIteration

/-!
# Segment 1 groundwork: `Parameters.Accepted` as integer comparisons (private lane owner:b-g5-6)

Lock v8 `F-parameter-choices.tex:73-76` (eq:paper-tail-graph) and `B-effectivity-details.tex:107-111`:
"Evaluate the formulas ..., computing ceiling logarithms by integer comparisons. Check domains and
(eq:paper-tail-graph) ...; no transcendental comparison or cutoff computation is needed."

This module is NOT a physical tester. It proves the arithmetic fact a tester needs: the second
integer check `2^40 c_src s q^2 t_2^4 <= q_2` (all factors but `c_src` powers of two) is equivalent to
one comparison of exponents plus `clog c_src`, so the whole acceptance predicate is a Boolean
combination of comparisons between numbers of size polynomial in `scale`, `b`, `clog c_src` and
`clog (12 |E|)`. At a level of the physical run, the only level-dependent inputs are the scale, the
rows and the columns (`accepted_run_iff`): `sourceConstant = c`, `incomingDepth = b` and
`edges = |E|` are fixed by `Iteration.parameters`.
-/

namespace EthInapproximability.CurrentPaper.G5fAccepted

open Parameters

/-- `clog 2 (2^b x) = b + clog 2 x` for `x ≥ 1`. -/
theorem clog_two_pow_mul (b x : ℕ) (hx : 1 ≤ x) :
    Nat.clog 2 (2 ^ b * x) = b + Nat.clog 2 x := by
  have key : ∀ y, (Nat.clog 2 (2 ^ b * x) ≤ y ↔ b + Nat.clog 2 x ≤ y) := by
    intro y
    rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
    constructor
    · intro h
      have hby : b ≤ y := by
        have h1 : 2 ^ b ≤ 2 ^ y := le_trans (Nat.le_mul_of_pos_right _ hx) h
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h1
      have e : 2 ^ y = 2 ^ b * 2 ^ (y - b) := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h
      have hx' : x ≤ 2 ^ (y - b) := Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos b)
      have := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hx'
      omega
    · intro h
      have hx' : x ≤ 2 ^ (y - b) :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (by omega)
      have e : 2 ^ y = 2 ^ b * 2 ^ (y - b) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      exact Nat.mul_le_mul_left _ hx'
  exact le_antisymm ((key _).mpr le_rfl) (by
    have := (key (Nat.clog 2 (2 ^ b * x))).mp le_rfl
    exact this)

/-- `C 2^X ≤ 2^Y ↔ C = 0 ∨ X + clog C ≤ Y`. -/
theorem mul_two_pow_le_iff (C X Y : ℕ) :
    C * 2 ^ X ≤ 2 ^ Y ↔ C = 0 ∨ X + Nat.clog 2 C ≤ Y := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · subst hC; simp
  · have hC0 : C ≠ 0 := by omega
    simp only [hC0, false_or]
    constructor
    · intro h
      have hXY : X ≤ Y := by
        have h1 : 2 ^ X ≤ 2 ^ Y := le_trans (Nat.le_mul_of_pos_left _ hC) h
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h1
      have e : 2 ^ Y = 2 ^ (Y - X) * 2 ^ X := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h
      have hc : C ≤ 2 ^ (Y - X) := Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos X)
      have := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hc
      omega
    · intro h
      have hc : C ≤ 2 ^ (Y - X) :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (by omega)
      have e : 2 ^ Y = 2 ^ (Y - X) * 2 ^ X := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      exact Nat.mul_le_mul_right _ hc

/-- **The acceptance predicate as integer comparisons** (for `edges ≥ 1`). -/
theorem accepted_iff (i : Input) (hE : 1 ≤ i.edges) :
    Accepted i ↔
      2 ≤ i.rows ∧ 2 ≤ i.columns ∧
      256 * scale i ^ 2 + 2 + 10000 * auxiliaryLog i ^ 2 ≤ i.incomingDepth ∧
      (i.sourceConstant = 0 ∨
        40 + 2 * (1000 * scale i ^ 2) + 4 * (100000000 * scale i ^ 4) +
          Nat.clog 2 i.sourceConstant ≤ Nat.clog 2 (12 * i.edges)) := by
  have hsec : secondExponent i = binExponent i + Nat.clog 2 (12 * i.edges) := by
    unfold secondExponent bins
    rw [show 12 * 2 ^ binExponent i * i.edges = 2 ^ binExponent i * (12 * i.edges) by ring]
    exact clog_two_pow_mul _ _ (by omega)
  have hlhs : 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 =
      i.sourceConstant * 2 ^ (binExponent i +
        (40 + 2 * (1000 * scale i ^ 2) + 4 * (100000000 * scale i ^ 4))) := by
    unfold bins outerWidth balanceOrder outerExponent balanceExponent
    rw [← pow_mul, ← pow_mul]
    rw [show binExponent i + (40 + 2 * (1000 * scale i ^ 2) + 4 * (100000000 * scale i ^ 4)) =
      40 + binExponent i + 1000 * scale i ^ 2 * 2 + 100000000 * scale i ^ 4 * 4 by ring]
    rw [pow_add, pow_add, pow_add]
    ring
  have h4 : 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 ≤
      secondWidth i ↔
      (i.sourceConstant = 0 ∨
        40 + 2 * (1000 * scale i ^ 2) + 4 * (100000000 * scale i ^ 4) +
          Nat.clog 2 i.sourceConstant ≤ Nat.clog 2 (12 * i.edges)) := by
    rw [hlhs, secondWidth, hsec, mul_two_pow_le_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
  unfold Accepted firstExponent binExponent
  rw [h4]

/-- At a level of the physical run, only the scale, the rows and the columns depend on the level. -/
theorem accepted_run_iff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (j : ℕ) (hE : 1 ≤ Fintype.card E) :
    Accepted (EffectiveIteration.runParameters G c b initial j) ↔
      2 ≤ (Iteration.run G c b initial j).matrix.rows ∧
      2 ≤ (Iteration.run G c b initial j).matrix.columns ∧
      256 * scale (EffectiveIteration.runParameters G c b initial j) ^ 2 + 2 +
        10000 * Nat.clog 2 (scale (EffectiveIteration.runParameters G c b initial j)) ^ 2 ≤ b ∧
      (c = 0 ∨
        40 + 2 * (1000 * scale (EffectiveIteration.runParameters G c b initial j) ^ 2) +
          4 * (100000000 * scale (EffectiveIteration.runParameters G c b initial j) ^ 4) +
          Nat.clog 2 c ≤ Nat.clog 2 (12 * Fintype.card E)) :=
  accepted_iff _ hE

#print axioms clog_two_pow_mul
#print axioms mul_two_pow_le_iff
#print axioms accepted_iff
#print axioms accepted_run_iff

/-- The level-independent part of the acceptance test, as a predicate of the scale `s` with the fixed
data `b = incomingDepth`, `c = sourceConstant`, `e = edges`. -/
def Good (b c e s : ℕ) : Prop :=
  256 * s ^ 2 + 2 + 10000 * Nat.clog 2 s ^ 2 ≤ b ∧
    (c = 0 ∨ 40 + 2 * (1000 * s ^ 2) + 4 * (100000000 * s ^ 4) + Nat.clog 2 c ≤ Nat.clog 2 (12 * e))

/-- `Good` is antitone in the scale: one threshold comparison per level suffices. -/
theorem good_anti {b c e s s' : ℕ} (hs : s ≤ s') (h : Good b c e s') : Good b c e s := by
  obtain ⟨h1, h2⟩ := h
  have hl : Nat.clog 2 s ≤ Nat.clog 2 s' := Nat.clog_mono_right 2 hs
  have q2 : s ^ 2 ≤ s' ^ 2 := Nat.pow_le_pow_left hs 2
  have q4 : s ^ 4 ≤ s' ^ 4 := Nat.pow_le_pow_left hs 4
  have l2 : Nat.clog 2 s ^ 2 ≤ Nat.clog 2 s' ^ 2 := Nat.pow_le_pow_left hl 2
  refine ⟨by omega, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (by omega)

/-- At a level of the physical run: the literal domain checks plus `Good` of that level's scale. -/
theorem accepted_run_iff_good {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (j : ℕ) (hE : 1 ≤ Fintype.card E) :
    Accepted (EffectiveIteration.runParameters G c b initial j) ↔
      2 ≤ (Iteration.run G c b initial j).matrix.rows ∧
      2 ≤ (Iteration.run G c b initial j).matrix.columns ∧
      Good b c (Fintype.card E) (scale (EffectiveIteration.runParameters G c b initial j)) :=
  accepted_run_iff G c b initial j hE

#print axioms good_anti
#print axioms accepted_run_iff_good

instance (b c e : ℕ) : DecidablePred (Good b c e) := fun s => by
  unfold Good; infer_instance

theorem good_le {b c e s : ℕ} (h : Good b c e s) : s ≤ b := by
  have h1 := h.1
  have : s ≤ s ^ 2 := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · simp [h0]
    · nlinarith
  omega

/-- The greatest good scale `≤ b` (the threshold; `0` if none is good). -/
def Sstar (b c e : ℕ) : ℕ := Nat.findGreatest (Good b c e) b

/-- `Good` of a scale is `Good` of `0` plus ONE comparison with the threshold. -/
theorem good_iff_le_Sstar (b c e s : ℕ) :
    Good b c e s ↔ Good b c e 0 ∧ s ≤ Sstar b c e := by
  constructor
  · intro h
    exact ⟨good_anti (Nat.zero_le s) h, Nat.le_findGreatest (good_le h) h⟩
  · rintro ⟨h0, hs⟩
    have hS : Good b c e (Sstar b c e) := Nat.findGreatest_spec (Nat.zero_le b) h0
    exact good_anti hs hS

/-- `scale ≤ S` as literal comparisons of the six public words with `2^S`. -/
theorem scale_le_iff (i : Input) (S : ℕ) :
    scale i ≤ S ↔ 2 ^ 24 ≤ S ∧ i.sourceConstant ≤ 2 ^ S ∧ i.nextDepth ≤ 2 ^ S ∧
      i.cost ≤ 2 ^ S ∧ Nat.clog 2 i.rows ≤ 2 ^ S ∧ Nat.clog 2 i.columns ≤ 2 ^ S ∧
      Nat.clog 2 (i.edges + 2) ≤ 2 ^ S ∧ 2 ≤ 2 ^ S := by
  unfold scale scaleBound namingLength
  rw [max_le_iff, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  simp only [max_le_iff]
  tauto

/-- **The per-level acceptance test as unary comparisons against ONE level-independent threshold
word `2^S`, `S = Sstar b c |E|`.** The first bracket is level-independent (computed once from
`b`, `c`, `|E|`); the rest reads only the level's raw words 2, 3, 4 (unary `y_j + j`, rows, columns). -/
theorem accepted_run_iff_threshold {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (j : ℕ) (hE : 1 ≤ Fintype.card E) :
    Accepted (EffectiveIteration.runParameters G c b initial j) ↔
      (Good b c (Fintype.card E) 0 ∧ 2 ^ 24 ≤ Sstar b c (Fintype.card E) ∧
        c ≤ 2 ^ Sstar b c (Fintype.card E) ∧ b ≤ 2 ^ Sstar b c (Fintype.card E) ∧
        Nat.clog 2 (Fintype.card E + 2) ≤ 2 ^ Sstar b c (Fintype.card E)) ∧
      2 ≤ (Iteration.run G c b initial j).matrix.rows ∧
      2 ≤ (Iteration.run G c b initial j).matrix.columns ∧
      (Iteration.run G c b initial j).budget + j ≤ 2 ^ Sstar b c (Fintype.card E) ∧
      Nat.clog 2 (Iteration.run G c b initial j).matrix.rows ≤ 2 ^ Sstar b c (Fintype.card E) ∧
      Nat.clog 2 (Iteration.run G c b initial j).matrix.columns ≤
        2 ^ Sstar b c (Fintype.card E) := by
  rw [accepted_run_iff_good G c b initial j hE, good_iff_le_Sstar, scale_le_iff]
  have h2 : ∀ S : ℕ, 2 ^ 24 ≤ S → 2 ≤ 2 ^ S := fun S hS =>
    le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
  change _ ↔ _ ∧ _ ∧ _ ∧ (Iteration.run G c b initial j).budget + j ≤ _ ∧ _
  constructor
  · rintro ⟨hr, hc, hg0, h24, hc', hb', hcost, hrl, hcl, hel, -⟩
    exact ⟨⟨hg0, h24, hc', hb', hel⟩, hr, hc, hcost, hrl, hcl⟩
  · rintro ⟨⟨hg0, h24, hc', hb', hel⟩, hr, hc, hcost, hrl, hcl⟩
    exact ⟨hr, hc, hg0, h24, hc', hb', hcost, hrl, hcl, hel, h2 _ h24⟩

#print axioms good_iff_le_Sstar
#print axioms scale_le_iff
#print axioms accepted_run_iff_threshold

end EthInapproximability.CurrentPaper.G5fAccepted
