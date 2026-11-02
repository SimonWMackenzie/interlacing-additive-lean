import Paper2.A4Amplification
import Paper2.A4Definitions
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# WP-U18a (ii), probability half: segments, the dyadic codec, and the median midpoint test

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12.

Source (lock v12 `sections/01-introduction.tex`):
* I:71-75 "A randomized estimator must succeed with probability at least 2/3 on every input.
  The numerical output must permit polynomial-time comparison with binary rationals of polynomial
  length, as required by the decision procedure using the estimator."
* I:117-125, proof of `intro:corollary`: "Choose a fixed integer k>2a. Amplify the estimator's
  success probability to 99/100 by a constant number of independent calls and a median.
  Accept the source exactly when its estimate is below B+k/2. On a correct estimate the YES and
  good NO cases lie on opposite sides of this threshold. The sum of reduction and estimation
  errors is less than 1/2, giving a BPP algorithm for satisfiability."

Decisions implemented: D-A1 (the tape of the composed machine is uniform over a fixed length, split
into `reps` disjoint segments of length `s`; `segment_prob` is the segment lemma "segments of a uniform
tape are uniform and independent"), D-A3 / D-Y3 (the estimator output is a dyadic rational;
`decodeDyadic` is this lane's own signed-integer-and-exponent `natField` codec, since lane
`a-model-owner-1` had not landed a codec when this file was written).

Reused admitted declarations (by exact name): `Paper2.Unit4Shell.Definitions.uniformTape`,
`Paper2.Unit4Shell.Amplification.{reps, iid_majority_good_ge, lowerMedian, lowerMedian_spec,
lowerMedian_lt_iff, lt_lowerMedian_of_majority, midpoint_yes_real, dyadic_lt_midpoint_iff}`,
`Paper2.FiniteLaw.{prob, iid, prod, prob_mono, two_stage_failure_le}`,
`EthInapproximability.CurrentPaper.EncodedCommunication.{natField, readNat, readNat_append}`.

Nothing here closes a ledger row by itself.
-/

namespace Paper2.MedianOwner

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification
open EthInapproximability.CurrentPaper.EncodedCommunication

/-! ## The dyadic codec (D-A3 option (ii); I:73-75) -/

/-- Value of the dyadic word with sign `neg`, magnitude `m` and exponent `e`: `(±m)/2^e`.
Implements D-A3 (ii) "Output: a dyadic rational (binary fraction)" (AUTHOR_DECISIONS_2026-09-27.md). -/
def dyadicValue (neg : Bool) (m e : ℕ) : ℚ := (if neg then -(m : ℚ) else (m : ℚ)) / 2 ^ e

/-- Encoding of a dyadic rational: one sign bit, then `natField m`, then `natField e`.
Implements D-A3 (ii); lock I:73-75 ("comparison with binary rationals of polynomial length"). -/
def encodeDyadic (neg : Bool) (m e : ℕ) : List Bool := neg :: (natField m ++ natField e)

/-- Decoder of `encodeDyadic`; every other word decodes to `none`.
Implements D-A3 (ii); lock I:71-75. -/
def decodeDyadic : List Bool → Option ℚ
  | [] => none
  | neg :: rest =>
      match readNat rest with
      | none => none
      | some (m, rest') =>
          match readNat rest' with
          | some (e, []) => some (dyadicValue neg m e)
          | _ => none

theorem decodeDyadic_encode (neg : Bool) (m e : ℕ) :
    decodeDyadic (encodeDyadic neg m e) = some (dyadicValue neg m e) := by
  have h2 : readNat (natField e) = some (e, []) := by
    simpa using readNat_append e []
  simp [encodeDyadic, decodeDyadic, readNat_append, h2]

/-- Conversion lemma: every decoded value is `z / 2^e` for an integer `z`. -/
theorem decodeDyadic_dyadic {w : List Bool} {v : ℚ} (h : decodeDyadic w = some v) :
    ∃ z : ℤ, ∃ e : ℕ, v = (z : ℚ) / 2 ^ e := by
  match w, h with
  | neg :: rest, h =>
    simp only [decodeDyadic] at h
    split at h
    · exact absurd h (by simp)
    · rename_i m rest' _
      split at h
      · rename_i e _
        refine ⟨if neg then -(m : ℤ) else (m : ℤ), e, ?_⟩
        have := Option.some.inj h
        subst this
        unfold dyadicValue
        split <;> simp
      · exact absurd h (by simp)

/-- Midpoint comparison of a decoded value as one integer comparison
(reuses the admitted `dyadic_lt_midpoint_iff`). -/
theorem decodeDyadic_lt_midpoint_iff {w : List Bool} {v : ℚ} (h : decodeDyadic w = some v)
    (B k : ℕ) : ∃ z : ℤ, ∃ e : ℕ, v = (z : ℚ) / 2 ^ e ∧
      (v < (B : ℚ) + (k : ℚ) / 2 ↔ 2 * z < 2 ^ e * (2 * (B : ℤ) + k)) := by
  obtain ⟨z, e, rfl⟩ := decodeDyadic_dyadic h
  exact ⟨z, e, rfl, dyadic_lt_midpoint_iff z e B k⟩

/-! ## Segments of a uniform tape (the segment lemma, D-A1) -/

/-- Segment `i` of a tape of length `r*s`: positions `s*i, …, s*i+s-1`. -/
def seg (r s : ℕ) (t : Fin (r * s) → Bool) (i : Fin r) : Fin s → Bool :=
  fun j => t (finProdFinEquiv (i, j))

/-- The segment split is a bijection. -/
def segEquiv (r s : ℕ) : (Fin (r * s) → Bool) ≃ (Fin r → Fin s → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

theorem segEquiv_apply (r s : ℕ) (t : Fin (r * s) → Bool) : segEquiv r s t = seg r s t := by
  funext i j
  simp [segEquiv, seg, Equiv.arrowCongr_apply]

/-- **Segment lemma** (D-A1): under the uniform law on tapes of length `r*s`, the `r` segments are
independent and each is uniform on tapes of length `s`, i.e. the pushforward of `uniformTape (r*s)`
under the split is `(uniformTape s).iid r`. -/
theorem segment_prob (r s : ℕ) (E : (Fin r → Fin s → Bool) → Prop) :
    (uniformTape (r * s)).prob (fun t => E (seg r s t)) = ((uniformTape s).iid r).prob E := by
  classical
  unfold FiniteLaw.prob
  have hw : ∀ x : Fin r → Fin s → Bool,
      ((uniformTape s).iid r).weight x = (1 / 2 : ℝ) ^ (r * s) := by
    intro x
    simp only [FiniteLaw.iid, uniformTape, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm]
  simp only [hw]
  have hsum := Equiv.sum_comp (segEquiv r s)
    (fun x => if E x then (1 / 2 : ℝ) ^ (r * s) else 0)
  simp only [segEquiv_apply] at hsum
  rw [← hsum]
  rfl

/-- The list view of a segment: `List.ofFn (seg r s t i)` is the `i`-th length-`s` chunk of the
tape word. -/
theorem ofFn_seg (r s : ℕ) (t : Fin (r * s) → Bool) (i : Fin r) :
    List.ofFn (seg r s t i) = ((List.ofFn t).drop (s * i)).take s := by
  have hi := i.isLt
  have hlen : s ≤ r * s - s * i := by
    have : s * (i + 1) ≤ s * r := Nat.mul_le_mul_left s hi
    rw [Nat.mul_comm r s]; rw [Nat.mul_succ] at this; omega
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, seg]
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

/-! ## The majority count, the lower median, and the midpoint test -/

/-- Value of an undecodable output: `⊤` (never below a threshold). -/
def topVal : Option ℚ → WithTop ℚ
  | none => ⊤
  | some v => (v : WithTop ℚ)

open Classical in
/-- Number of runs whose decoded output is below `θ`. -/
noncomputable def belowCount {r : ℕ} (vals : Fin r → Option ℚ) (θ : ℚ) : ℕ :=
  Fintype.card {i : Fin r // ∃ v, vals i = some v ∧ v < θ}

/-- The accept bit of the median machine: a strict majority of decoded outputs is below `θ`. -/
def medianAccepts {r : ℕ} (vals : Fin r → Option ℚ) (θ : ℚ) : Prop :=
  r < 2 * belowCount vals θ

/-- The majority test is exactly the lower-median test (undecodable outputs count as `⊤`),
by the admitted `lowerMedian_lt_iff`. -/
theorem medianAccepts_iff {r : ℕ} (hr : 0 < r) (vals : Fin r → Option ℚ) (θ : ℚ) :
    medianAccepts vals θ ↔ lowerMedian hr (fun i => topVal (vals i)) < (θ : WithTop ℚ) := by
  classical
  rw [lowerMedian_lt_iff, medianAccepts, belowCount, Fintype.card_subtype]
  have : (Finset.univ.filter fun i => ∃ v, vals i = some v ∧ v < θ) =
      (Finset.univ.filter fun i => topVal (vals i) < (θ : WithTop ℚ)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : vals i with
    | none => simp [topVal]
    | some v => simp [topVal]
  rw [this]

open Classical in
/-- If a strict majority of samples lies in an order-convex window, so does the lower median. -/
theorem lowerMedian_mem_window {β : Type*} [LinearOrder β] {r : ℕ} (hr : 0 < r) (v : Fin r → β)
    (W : β → Prop) (hconv : ∀ x y z, W x → W z → x ≤ y → y ≤ z → W y)
    (hmaj : r < 2 * (Finset.univ.filter fun i => W (v i)).card) :
    W (lowerMedian hr v) := by
  classical
  obtain ⟨_, hmajm, hmin⟩ := lowerMedian_spec hr v
  -- lower witness: the two strict majorities intersect
  have hlow : ∃ i, W (v i) ∧ v i ≤ lowerMedian hr v := by
    by_contra hno
    push Not at hno
    have hdisj : Disjoint (Finset.univ.filter fun i => W (v i))
        (Finset.univ.filter fun i => v i ≤ lowerMedian hr v) := by
      rw [Finset.disjoint_filter]
      intro i _ hW hle
      exact absurd hle (not_le.mpr (hno i hW))
    have := Finset.card_union_of_disjoint hdisj
    have hle := Finset.card_le_univ ((Finset.univ.filter fun i => W (v i)) ∪
      (Finset.univ.filter fun i => v i ≤ lowerMedian hr v))
    simp only [Fintype.card_fin] at hle
    omega
  -- upper witness: the largest window sample
  have hne : (Finset.univ.filter fun i => W (v i)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨j, hj, hjmax⟩ := (Finset.univ.filter fun i => W (v i)).exists_max_image v hne
  have hWj : W (v j) := (Finset.mem_filter.mp hj).2
  have hup : lowerMedian hr v ≤ v j := by
    apply hmin j
    refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hjmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  obtain ⟨i, hWi, hi⟩ := hlow
  exact hconv _ _ _ hWi hWj hi hup

/-- The additive window of radius `a` around `c`, on `WithTop ℚ`. -/
def Window (c : ℕ) (a : ℝ) (x : WithTop ℚ) : Prop :=
  ∃ q : ℚ, x = (q : WithTop ℚ) ∧ |(q : ℝ) - c| ≤ a

theorem window_convex (c : ℕ) (a : ℝ) :
    ∀ x y z, Window c a x → Window c a z → x ≤ y → y ≤ z → Window c a y := by
  rintro x y z ⟨qx, rfl, hx⟩ ⟨qz, rfl, hz⟩ hxy hyz
  induction y using WithTop.recTopCoe with
  | top => exact absurd hyz (by simp)
  | coe qy =>
    refine ⟨qy, rfl, ?_⟩
    have h1 : qx ≤ qy := WithTop.coe_le_coe.mp hxy
    have h2 : qy ≤ qz := WithTop.coe_le_coe.mp hyz
    have h1' : (qx : ℝ) ≤ qy := by exact_mod_cast h1
    have h2' : (qy : ℝ) ≤ qz := by exact_mod_cast h2
    rw [abs_le] at hx hz ⊢
    constructor <;> linarith [hx.1, hz.2]

/-- The per-run success event of D-A3 (I:71-73): the output decodes to a value within `a` of `c`. -/
def RunGood (c : ℕ) (a : ℝ) (out : List Bool) : Prop :=
  ∃ v, decodeDyadic out = some v ∧ |(v : ℝ) - c| ≤ a

theorem runGood_window (c : ℕ) (a : ℝ) (out : List Bool) (h : RunGood c a out) :
    Window c a (topVal (decodeDyadic out)) := by
  obtain ⟨v, hv, ha⟩ := h
  exact ⟨v, by rw [hv]; rfl, ha⟩

/-- The midpoint threshold `B + k/2` of I:120. -/
def midpoint (B k : ℕ) : ℚ := (B : ℚ) + (k : ℚ) / 2

open Classical in
/-- **Median amplification and the midpoint test, one estimator input** (I:117-125).
`out g` is the estimator's output word on its (fixed) input with segment tape `g`; the composed
machine's tape is uniform of length `reps * s` and run `i` reads segment `i`. If one run is
correct (within `a` of `c`) with probability at least `2/3`, then with probability at least
`99/100`: the lower median of the decoded outputs is within `a` of `c`; on `c ≤ B` the majority
(= median) test accepts; on `B + k ≤ c` it rejects (`2a < k`). -/
theorem median_midpoint_test (s : ℕ) (out : (Fin s → Bool) → List Bool) (c : ℕ) (a : ℝ)
    (B k : ℕ) (hk : 2 * a < k)
    (hE : 2 / 3 ≤ (uniformTape s).prob (fun g => RunGood c a (out g))) :
    (99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        Window c a (lowerMedian (by decide : 0 < reps)
          (fun i => topVal (decodeDyadic (out (seg reps s t i))))))) ∧
    (c ≤ B → 99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        medianAccepts (fun i => decodeDyadic (out (seg reps s t i))) (midpoint B k))) ∧
    (B + k ≤ c → 99 / 100 ≤ (uniformTape (reps * s)).prob (fun t =>
        ¬ medianAccepts (fun i => decodeDyadic (out (seg reps s t i))) (midpoint B k))) := by
  have hmaj := iid_majority_good_ge (uniformTape s) (fun g => RunGood c a (out g)) hE
  -- the majority event, transported through the segment lemma
  have hT : ∀ P : (Fin reps → Fin s → Bool) → Prop,
      (∀ x, reps < 2 * Fintype.card {i : Fin reps // RunGood c a (out (x i))} → P x) →
      99 / 100 ≤ (uniformTape (reps * s)).prob (fun t => P (seg reps s t)) := by
    intro P hP
    rw [segment_prob reps s P]
    exact hmaj.trans (FiniteLaw.prob_mono _ hP)
  have hcardG : ∀ x : Fin reps → Fin s → Bool,
      Fintype.card {i : Fin reps // RunGood c a (out (x i))} =
        (Finset.univ.filter fun i => RunGood c a (out (x i))).card := fun x =>
    Fintype.card_subtype _
  refine ⟨?_, ?_, ?_⟩
  · refine hT (fun x => Window c a (lowerMedian (by decide : 0 < reps)
        (fun i => topVal (decodeDyadic (out (x i)))))) ?_
    intro x hx
    apply lowerMedian_mem_window _ _ _ (window_convex c a)
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact runGood_window c a _ hi
  · intro hcB
    refine hT (fun x => medianAccepts (fun i => decodeDyadic (out (x i))) (midpoint B k)) ?_
    intro x hx
    unfold medianAccepts belowCount
    rw [Fintype.card_subtype]
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, ha⟩ := hi
    refine ⟨v, hv, ?_⟩
    have h1 := midpoint_yes_real (v : ℝ) a c B k hcB ha hk
    have h2 : ((v : ℚ) : ℝ) < (((B : ℚ) + (k : ℚ) / 2 : ℚ) : ℝ) := by push_cast; exact h1
    exact Rat.cast_lt.mp h2
  · intro hBc
    refine hT (fun x => ¬ medianAccepts (fun i => decodeDyadic (out (x i))) (midpoint B k)) ?_
    intro x hx
    rw [medianAccepts_iff (by decide : 0 < reps), not_lt]
    apply le_of_lt
    apply lt_lowerMedian_of_majority
    rw [hcardG] at hx
    refine lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, ha⟩ := hi
    rw [hv]
    show ((midpoint B k : ℚ) : WithTop ℚ) < ((v : ℚ) : WithTop ℚ)
    rw [WithTop.coe_lt_coe]
    have hc : ((B : ℝ) + k) ≤ c := by exact_mod_cast hBc
    have h1 := (abs_le.mp ha).1
    have : ((midpoint B k : ℚ) : ℝ) < (v : ℝ) := by
      unfold midpoint; push_cast; linarith
    exact_mod_cast this

open Classical in
/-- **Two-stage error union** (I:121-123, "The sum of reduction and estimation errors"):
reduction tape `b` under any law `ρ` (independent of the estimator tape of length `reps*s`, D-A1),
estimator input and output depending on `b`. If the reduction is good except with probability
`ε` and, on a good reduction tape, one run is correct with probability `≥ 2/3`, then the composed
median-midpoint test answers `ans b` (accept for `true`, reject for `false`) except with
probability at most `ε + 1/100`. With the admitted `error_budget`, `ε = (1/2)^11` gives an error
below `1/3`. -/
theorem median_two_stage {β : Type*} [Fintype β] (ρ : FiniteLaw β) (s : ℕ)
    (out : β → (Fin s → Bool) → List Bool) (c B : β → ℕ) (ans : β → Bool) (a : ℝ) (k : ℕ)
    (hk : 2 * a < k) (GoodTape : β → Prop) (ε : ℝ)
    (hρ : ρ.prob (fun b => ¬ GoodTape b) ≤ ε)
    (hgood : ∀ b, GoodTape b → (ans b = true → c b ≤ B b) ∧ (ans b = false → B b + k ≤ c b))
    (hE : ∀ b, GoodTape b → 2 / 3 ≤ (uniformTape s).prob (fun g => RunGood (c b) a (out b g))) :
    (ρ.prod (uniformTape (reps * s))).prob (fun x =>
        ¬ (medianAccepts (fun i => decodeDyadic (out x.1 (seg reps s x.2 i)))
            (midpoint (B x.1) k) ↔ ans x.1 = true)) ≤ ε + 1 / 100 := by
  apply FiniteLaw.two_stage_failure_le ρ (uniformTape (reps * s)) GoodTape
    (fun b t => ¬ (medianAccepts (fun i => decodeDyadic (out b (seg reps s t i)))
            (midpoint (B b) k) ↔ ans b = true)) ε (1 / 100) hρ ?_ (by norm_num)
  intro b hb
  beta_reduce
  obtain ⟨_, hyes, hno⟩ := median_midpoint_test s (out b) (c b) a (B b) k hk (hE b hb)
  cases hans : ans b with
  | true =>
    have h := hyes ((hgood b hb).1 hans)
    have hc : (uniformTape (reps * s)).prob (fun t =>
        ¬ (medianAccepts (fun i => decodeDyadic (out b (seg reps s t i))) (midpoint (B b) k) ↔
          true = true)) = (uniformTape (reps * s)).prob (fun t =>
        ¬ medianAccepts (fun i => decodeDyadic (out b (seg reps s t i))) (midpoint (B b) k)) := by
      congr 1; funext t; simp
    rw [hc, prob_not]; linarith
  | false =>
    have h := hno ((hgood b hb).2 hans)
    have hc : (uniformTape (reps * s)).prob (fun t =>
        ¬ (medianAccepts (fun i => decodeDyadic (out b (seg reps s t i))) (midpoint (B b) k) ↔
          false = true)) = (uniformTape (reps * s)).prob (fun t =>
        ¬ ¬ medianAccepts (fun i => decodeDyadic (out b (seg reps s t i))) (midpoint (B b) k)) := by
      congr 1; funext t; simp
    rw [hc, prob_not]; linarith

end Paper2.MedianOwner
