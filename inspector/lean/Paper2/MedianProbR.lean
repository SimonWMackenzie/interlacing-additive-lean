import Paper2.MedianProb

/-!
# WP-U18a (ii), probability half for an arbitrary real-valued output decoder

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117-125.

The same statements as `MedianProb`, for any decoder `dec : List Bool → Option ℝ` (so that the
codec chosen by lane `a-model-owner-1`, `Paper2.AModel.decodeDyadic`, D-A3 (ii), can be plugged in
without a conversion). Reuses this lane's `segment_prob`, `seg`, `lowerMedian_mem_window` and the
admitted `Paper2.Unit4Shell.Amplification.{reps, iid_majority_good_ge, lowerMedian,
lowerMedian_lt_iff, lt_lowerMedian_of_majority, midpoint_yes_real}`.
-/

namespace Paper2.MedianOwner

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification

/-- Value of an undecodable output: `⊤`. -/
def topValR : Option ℝ → WithTop ℝ
  | none => ⊤
  | some v => (v : WithTop ℝ)

/-- The event "the output decodes to a value below `θ`". -/
def Below (dec : List Bool → Option ℝ) (θ : ℝ) (out : List Bool) : Prop :=
  ∃ v, dec out = some v ∧ v < θ

open Classical in
/-- The accept predicate of the median machine: a strict majority of the `r` outputs is `Below θ`. -/
def MajBelow {r : ℕ} (dec : List Bool → Option ℝ) (outs : Fin r → List Bool) (θ : ℝ) : Prop :=
  r < 2 * Fintype.card {i : Fin r // Below dec θ (outs i)}

/-- The majority test is exactly the lower-median test (`⊤` for undecodable outputs). -/
theorem majBelow_iff {r : ℕ} (hr : 0 < r) (dec : List Bool → Option ℝ) (outs : Fin r → List Bool)
    (θ : ℝ) : MajBelow dec outs θ ↔
      lowerMedian hr (fun i => topValR (dec (outs i))) < (θ : WithTop ℝ) := by
  classical
  rw [lowerMedian_lt_iff, MajBelow, Fintype.card_subtype]
  have : (Finset.univ.filter fun i => Below dec θ (outs i)) =
      (Finset.univ.filter fun i => topValR (dec (outs i)) < (θ : WithTop ℝ)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Below]
    cases h : dec (outs i) with
    | none => simp [topValR]
    | some v => simp [topValR]
  rw [this]

/-- The additive window of radius `a` around `c`, on `WithTop ℝ`. -/
def WindowR (c : ℕ) (a : ℝ) (x : WithTop ℝ) : Prop :=
  ∃ q : ℝ, x = (q : WithTop ℝ) ∧ |q - c| ≤ a

theorem windowR_convex (c : ℕ) (a : ℝ) :
    ∀ x y z, WindowR c a x → WindowR c a z → x ≤ y → y ≤ z → WindowR c a y := by
  rintro x y z ⟨qx, rfl, hx⟩ ⟨qz, rfl, hz⟩ hxy hyz
  induction y using WithTop.recTopCoe with
  | top => exact absurd hyz (by simp)
  | coe qy =>
    refine ⟨qy, rfl, ?_⟩
    have h1 : qx ≤ qy := WithTop.coe_le_coe.mp hxy
    have h2 : qy ≤ qz := WithTop.coe_le_coe.mp hyz
    rw [abs_le] at hx hz ⊢
    constructor <;> linarith [hx.1, hz.2]

/-- The per-run success event of D-A3 (I:71-73) for decoder `dec`. -/
def RunGoodR (dec : List Bool → Option ℝ) (c : ℕ) (a : ℝ) (out : List Bool) : Prop :=
  ∃ v, dec out = some v ∧ |v - c| ≤ a

open Classical in
/-- **Median amplification and the midpoint test** (I:117-125), for any decoder: with per-run
success probability `≥ 2/3`, with probability `≥ 99/100` over the `reps·s` tape the lower median
is within `a` of `c`, the majority (= median) test at `B + k/2` accepts when `c ≤ B`, and rejects
when `B + k ≤ c` (`2a < k`). -/
theorem median_midpoint_testR (dec : List Bool → Option ℝ) (s : ℕ)
    (out : (Fin s → Bool) → List Bool) (c : ℕ) (a : ℝ) (B k : ℕ) (hk : 2 * a < k)
    (hE : 2 / 3 ≤ (uniformTape s).prob (fun g => RunGoodR dec c a (out g))) :
    (99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        WindowR c a (lowerMedian (by decide : 0 < reps)
          (fun i => topValR (dec (out (seg reps s t i))))))) ∧
    (c ≤ B → 99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        MajBelow dec (fun i => out (seg reps s t i)) ((B : ℝ) + (k : ℝ) / 2))) ∧
    (B + k ≤ c → 99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        ¬ MajBelow dec (fun i => out (seg reps s t i)) ((B : ℝ) + (k : ℝ) / 2))) := by
  have hmaj := iid_majority_good_ge (uniformTape s) (fun g => RunGoodR dec c a (out g)) hE
  have hT : ∀ P : (Fin reps → Fin s → Bool) → Prop,
      (∀ x, reps < 2 * Fintype.card {i : Fin reps // RunGoodR dec c a (out (x i))} → P x) →
      99 / 100 ≤ (uniformTape (reps * s)).prob (fun t => P (seg reps s t)) := by
    intro P hP
    rw [segment_prob reps s P]
    exact hmaj.trans (FiniteLaw.prob_mono _ hP)
  have hcardG : ∀ x : Fin reps → Fin s → Bool,
      Fintype.card {i : Fin reps // RunGoodR dec c a (out (x i))} =
        (Finset.univ.filter fun i => RunGoodR dec c a (out (x i))).card := fun x =>
    Fintype.card_subtype _
  refine ⟨?_, ?_, ?_⟩
  · refine hT (fun x => WindowR c a (lowerMedian (by decide : 0 < reps)
        (fun i => topValR (dec (out (x i)))))) ?_
    intro x hx
    apply lowerMedian_mem_window _ _ _ (windowR_convex c a)
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, ha⟩ := hi
    exact ⟨v, by rw [hv]; rfl, ha⟩
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

open Classical in
/-- **Two-stage error union** (I:121-123, "The sum of reduction and estimation errors is less
than 1/2"), for any decoder: reduction tape `b` under any law `ρ`, independent of the estimator tape
of length `reps·s` (D-A1); the estimator's input, target `c b`, public integer `B b` and intended
answer `ans b` may depend on `b`. If the reduction is good except with probability `ε` and, on a good
reduction tape, one run is within `a` of `c b` with probability `≥ 2/3`, the median-midpoint test
answers `ans b` except with probability at most `ε + 1/100` (with the admitted `error_budget`,
`ε = (1/2)^11` gives an error below `1/3`). -/
theorem median_two_stageR (dec : List Bool → Option ℝ) {β : Type*} [Fintype β] (ρ : FiniteLaw β)
    (s : ℕ) (out : β → (Fin s → Bool) → List Bool) (c B : β → ℕ) (ans : β → Bool) (a : ℝ) (k : ℕ)
    (hk : 2 * a < k) (GoodTape : β → Prop) (ε : ℝ)
    (hρ : ρ.prob (fun b => ¬ GoodTape b) ≤ ε)
    (hgood : ∀ b, GoodTape b → (ans b = true → c b ≤ B b) ∧ (ans b = false → B b + k ≤ c b))
    (hE : ∀ b, GoodTape b →
      2 / 3 ≤ (uniformTape s).prob (fun g => RunGoodR dec (c b) a (out b g))) :
    (ρ.prod (uniformTape (reps * s))).prob (fun x =>
        ¬ (MajBelow dec (fun i => out x.1 (seg reps s x.2 i)) ((B x.1 : ℝ) + (k : ℝ) / 2) ↔
          ans x.1 = true)) ≤ ε + 1 / 100 := by
  apply FiniteLaw.two_stage_failure_le ρ (uniformTape (reps * s)) GoodTape
    (fun b t => ¬ (MajBelow dec (fun i => out b (seg reps s t i)) ((B b : ℝ) + (k : ℝ) / 2) ↔
      ans b = true)) ε (1 / 100) hρ ?_ (by norm_num)
  intro b hb
  beta_reduce
  obtain ⟨_, hyes, hno⟩ := median_midpoint_testR dec s (out b) (c b) a (B b) k hk (hE b hb)
  cases hans : ans b with
  | true =>
    have h := hyes ((hgood b hb).1 hans)
    have hc : (uniformTape (reps * s)).prob (fun t =>
        ¬ (MajBelow dec (fun i => out b (seg reps s t i)) ((B b : ℝ) + (k : ℝ) / 2) ↔
          true = true)) = (uniformTape (reps * s)).prob (fun t =>
        ¬ MajBelow dec (fun i => out b (seg reps s t i)) ((B b : ℝ) + (k : ℝ) / 2)) := by
      congr 1; funext t; simp
    rw [hc, prob_not]; linarith
  | false =>
    have h := hno ((hgood b hb).2 hans)
    have hc : (uniformTape (reps * s)).prob (fun t =>
        ¬ (MajBelow dec (fun i => out b (seg reps s t i)) ((B b : ℝ) + (k : ℝ) / 2) ↔
          false = true)) = (uniformTape (reps * s)).prob (fun t =>
        ¬ ¬ MajBelow dec (fun i => out b (seg reps s t i)) ((B b : ℝ) + (k : ℝ) / 2)) := by
      congr 1; funext t; simp
    rw [hc, prob_not]; linarith

end Paper2.MedianOwner
