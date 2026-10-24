import CurrentAdditive.V39GeneralHalfMajority

/-!
Strict constants for the SAME 147-run physical classifier. The old
Hoeffding theorem already bounds failure by exp(-6); only its final
rounding to 1/100 discarded strictness. No new machine or random tapes.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39GeneralHalfMajority

open Paper2 Paper2.FiniteLaw Paper2.MedianOwner
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification
open CurrentAdditive.V39HalfMidpoint
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem exp_neg_six_lt : Real.exp (-6) < 1 / 100 := by
  have h1 := Real.exp_one_gt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7182818283 : ℝ) ^ 6 < Real.exp 1 ^ 6 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hbig : (100 : ℝ) < Real.exp 6 := by
    rw [h6]
    nlinarith [hpow]
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos 6) (by norm_num)]
  simpa using hbig

theorem iid_half_bad_lt {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (Bad : α → Prop) (hBad : μ.prob Bad ≤ 1 / 3) :
    (μ.iid reps).prob (fun x => reps ≤ 2 * Fintype.card {i : Fin reps // Bad (x i)}) <
      1 / 100 := by
  have h := iid_half_bad_le_exp μ Bad hBad reps (by decide)
  have he : (-2 * (reps : ℝ) * (1 / 7 : ℝ) ^ 2) = -6 := by norm_num [reps]
  rw [he] at h
  exact lt_of_le_of_lt h exp_neg_six_lt

theorem iid_majority_good_gt {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (Good : α → Prop) (hGood : 2 / 3 ≤ μ.prob Good) :
    99 / 100 < (μ.iid reps).prob
      (fun x => reps < 2 * Fintype.card {i : Fin reps // Good (x i)}) := by
  have hBad : μ.prob (fun a => ¬ Good a) ≤ 1 / 3 := by
    rw [prob_not]
    linarith
  have h := iid_half_bad_lt μ (fun a => ¬ Good a) hBad
  have hsub : ∀ x : Fin reps → α,
      ¬ (reps < 2 * Fintype.card {i : Fin reps // Good (x i)}) →
        reps ≤ 2 * Fintype.card {i : Fin reps // ¬ Good (x i)} := by
    intro x hx
    have hsum : Fintype.card {i : Fin reps // Good (x i)} +
        Fintype.card {i : Fin reps // ¬ Good (x i)} = reps := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      have hc := Fintype.card_subtype_le (fun i : Fin reps => Good (x i))
      simp only [Fintype.card_fin] at hc
      omega
    omega
  have hm := FiniteLaw.prob_mono (μ.iid reps) hsub
  rw [prob_not] at hm
  have h' : (μ.iid reps).prob
      (fun a => reps ≤ 2 * Fintype.card {i : Fin reps // ¬ Good (a i)}) < 1 / 100 := by
    convert h
  linarith

/-- The existing segment law and the same midpoint event transfer, now
retaining the strict numerical Hoeffding bound. -/
theorem median_midpoint_strictR (dec : List Bool → Option ℝ) (s : ℕ)
    (out : (Fin s → Bool) → List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k)
    (hE : 2 / 3 ≤ (uniformTape s).prob (fun g => RunGoodR dec c a (out g))) :
    (c ≤ B → 99 / 100 < (uniformTape (reps * s)).prob (fun t =>
      MajBelow dec (fun i => out (seg reps s t i)) ((B : ℝ) + (k : ℝ) / 2))) ∧
    (B + k ≤ c → 99 / 100 < (uniformTape (reps * s)).prob (fun t =>
      ¬ MajBelow dec (fun i => out (seg reps s t i)) ((B : ℝ) + (k : ℝ) / 2))) := by
  have hmaj := iid_majority_good_gt (uniformTape s) (fun g => RunGoodR dec c a (out g)) hE
  have hT : ∀ P : (Fin reps → Fin s → Bool) → Prop,
      (∀ x, reps < 2 * Fintype.card {i : Fin reps // RunGoodR dec c a (out (x i))} → P x) →
      99 / 100 < (uniformTape (reps * s)).prob (fun t => P (seg reps s t)) := by
    intro P hP
    rw [segment_prob reps s P]
    exact lt_of_lt_of_le hmaj (FiniteLaw.prob_mono _ hP)
  have hcardG : ∀ x : Fin reps → Fin s → Bool,
      Fintype.card {i : Fin reps // RunGoodR dec c a (out (x i))} =
        (Finset.univ.filter fun i => RunGoodR dec c a (out (x i))).card := fun x =>
    Fintype.card_subtype _
  constructor
  · intro hcB
    refine hT (fun x => MajBelow dec (fun i => out (x i)) ((B : ℝ) + (k : ℝ) / 2)) ?_
    intro x hx
    unfold MajBelow
    rw [Fintype.card_subtype]
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, ha⟩ := hi
    exact ⟨v, hv, midpoint_yes_real v a c B k hcB ha hk⟩
  · intro hBc
    refine hT (fun x => ¬ MajBelow dec (fun i => out (x i)) ((B : ℝ) + (k : ℝ) / 2)) ?_
    intro x hx
    rw [majBelow_iff (by decide : 0 < reps), not_lt]
    apply le_of_lt
    apply lt_lowerMedian_of_majority
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, ha⟩ := hi
    rw [hv]
    show (((B : ℝ) + (k : ℝ) / 2 : ℝ) : WithTop ℝ) < ((v : ℝ) : WithTop ℝ)
    rw [WithTop.coe_lt_coe]
    have hc : ((B : ℝ) + k) ≤ c := by exact_mod_cast hBc
    have h1 := (abs_le.mp ha).1
    linarith

/-- This is the exact same `E.classifier`, not a newly amplified machine.
It has 147 tapes and compares each output only with the public m/2.
The local numerical success hypothesis can have any input-dependent u. -/
theorem GeneralEstimator.fixed_midpoint_strict_law (E : GeneralEstimator)
    (word : List Bool) (D B k : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hgap : 2 * u < (k : ℝ))
    (haccurate : 2 / 3 ≤ E.estimator.prob word
      (fun out => |E.value out - (D : ℝ)| ≤ u)) :
    (D ≤ B →
      99 / 100 < E.classifier.prob (natField (2 * B + k) ++ word) (· = [true])) ∧
    (B + k ≤ D →
      E.classifier.prob (natField (2 * B + k) ++ word) (· = [true]) < 1 / 100) := by
  let w := natField (2 * B + k) ++ word
  let A := (HeaderStrip.selectedEstimator E.estimator).toPrefix
  let dec := fun out => some (E.value out)
  let θ := (B : ℝ) + (k : ℝ) / 2
  have hj : ∀ out, E.comparator.judge w out = decide (Below dec θ out) := by
    intro out
    have h := E.comparator.judge_header (2 * B + k) word out
    have hm : ((2 * B + k : ℕ) : ℝ) / 2 = θ := by dsimp [θ]; push_cast; ring
    rw [hm] at h
    simpa [w, dec, Below] using h
  have hp : E.classifier.prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        MajBelow dec (fun i => A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) θ) := by
    rw [E.classifier_prob, GeneralEstimator.majority, medAlgJudge_prob]
    congr 1
    funext t
    simp only [MajBelow, hj, decide_eq_true_eq]
    rfl
  have ha : 2 / 3 ≤ (uniformTape (A.tapeLength w.length)).prob
      (fun g => RunGoodR dec D u (A.output w (List.ofFn g))) := by
    change 2 / 3 ≤ A.prob w (fun out => ∃ v, some (E.value out) = some v ∧ |v - (D : ℝ)| ≤ u)
    dsimp only [A, w]
    rw [HeaderStrip.selectedEstimator_toPrefix_prob]
    simpa using haccurate
  have h := median_midpoint_strictR dec (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) D u B k hgap ha
  constructor
  · intro hD
    rw [hp]
    exact h.1 hD
  · intro hD
    have hh := h.2 hD
    rw [Paper2.Unit4Shell.Amplification.prob_not] at hh
    rw [hp]
    linarith

#print axioms exp_neg_six_lt
#print axioms iid_half_bad_lt
#print axioms iid_majority_good_gt
#print axioms median_midpoint_strictR
#print axioms GeneralEstimator.fixed_midpoint_strict_law

end CurrentAdditive.V39GeneralHalfMajority
