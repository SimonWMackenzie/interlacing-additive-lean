import Paper2.MedianProbR
import Paper2.AModelPrefix
import Paper2.A4Shells
import Paper2.AEndpoint

/-!
# Lane `owner:a-decider-2` (Paper A, lock v12), segment 2, generic half: the error of the
growing-gap decider from the tape layout, the median/majority identity and a law-level statement

Private module, 27 September 2026. Nothing here is admitted; no ledger row is closed.

Lock v12 `01-introduction.tex:117-122` (proof of `intro:corollary`, reused by the proof of
`thm:quantitative`, `06-reduction.tex:136-137`, "The midpoint test from \cref{intro:corollary}
decides the formula with bounded error"): "Amplify the estimator's success probability to $99/100$
by a constant number of independent calls and a median. Accept the source exactly when its
estimate is below $B+k/2$."

Content.
* `estOf dec θ out`: the real value an estimator output is read as (the decoded value, or `θ` when
  the word does not decode); `estOf_lt_iff`: it is below `θ` iff the output is `Below dec θ`.
* `accepts_iff_majBelow`: the admitted law-level acceptance event `Shells.accepts` (lower median
  of the 147 real estimates below `Bud + k/2`) at the estimate `estOf` is EXACTLY lane a-median-1's
  majority event `MajBelow` (the bit the median machine prints).
* `bitsEquiv`: a tape model satisfying the admitted `AEndpoint.uniformExact` is in bijection with
  `Fin r → Bool`, weights preserved.
* `layout`, `layout_prob`: the canonical decider-tape layout `[reduction bits r][147 blocks of s][rest]`
  of ONE uniform tape of length `R ≥ r + 147 s`; its pushforward is the reduction law times the
  147-fold uniform estimator law.
-/

namespace Paper2.ADecider

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification
open Paper2.MedianOwner

/-- The real estimate read from an estimator output word: the decoded value, or `θ` (the
threshold itself, which the midpoint test does not count as "below") when the word does not
decode. -/
noncomputable def estOf (dec : List Bool → Option ℝ) (θ : ℝ) (out : List Bool) : ℝ :=
  match dec out with
  | some v => v
  | none => θ

theorem estOf_lt_iff (dec : List Bool → Option ℝ) (θ : ℝ) (out : List Bool) :
    estOf dec θ out < θ ↔ Below dec θ out := by
  unfold estOf Below
  cases h : dec out with
  | none => simp
  | some v => simp

/-- A successful run (decodes within `a` of `c`) gives an estimate within `a` of `c`. -/
theorem est_of_runGood (dec : List Bool → Option ℝ) (θ : ℝ) (c : ℕ) (a : ℝ) (out : List Bool)
    (h : RunGoodR dec c a out) : |estOf dec θ out - c| ≤ a := by
  obtain ⟨v, hv, ha⟩ := h
  unfold estOf
  rw [hv]
  exact ha

/-- **The admitted law-level acceptance event is the majority event printed by the median
machine.** -/
theorem accepts_iff_majBelow {β α : Type*} (dec : List Bool → Option ℝ)
    (out : β → α → List Bool) (Bud k : ℕ) (x : β × (Fin reps → α)) :
    Paper2.Unit4Shell.Shells.accepts
        (fun b g => estOf dec ((Bud : ℝ) + (k : ℝ) / 2) (out b g)) Bud k x ↔
      MajBelow dec (fun i => out x.1 (x.2 i)) ((Bud : ℝ) + (k : ℝ) / 2) := by
  classical
  unfold Paper2.Unit4Shell.Shells.accepts
  rw [lowerMedian_lt_iff, MajBelow, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin reps =>
        estOf dec ((Bud : ℝ) + (k : ℝ) / 2) (out x.1 (x.2 i)) < (Bud : ℝ) + (k : ℝ) / 2) =
      (Finset.univ.filter fun i => Below dec ((Bud : ℝ) + (k : ℝ) / 2) (out x.1 (x.2 i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, estOf_lt_iff]
  rw [this]

/-! ## Tape models with the admitted `uniformExact` property -/

section Bits

variable {τ : Type} (r : ℕ) (bits : τ → List Bool)

/-- The bit vector of a tape of exact length `r`. -/
def bitVec (hlen : ∀ t, (bits t).length = r) (t : τ) : Fin r → Bool :=
  fun i => (bits t)[i.val]'(by rw [hlen t]; exact i.isLt)

theorem ofFn_bitVec (hlen : ∀ t, (bits t).length = r) (t : τ) :
    List.ofFn (bitVec r bits hlen t) = bits t := by
  apply List.ext_getElem
  · simp [hlen t]
  · intro i h1 h2
    simp [bitVec]

theorem bitVec_bijective (hlen : ∀ t, (bits t).length = r) (hinj : Function.Injective bits)
    (hsurj : ∀ w : List Bool, w.length = r → ∃ t, bits t = w) :
    Function.Bijective (bitVec r bits hlen) := by
  constructor
  · intro t t' h
    apply hinj
    rw [← ofFn_bitVec r bits hlen t, ← ofFn_bitVec r bits hlen t', h]
  · intro g
    obtain ⟨t, ht⟩ := hsurj (List.ofFn g) (by simp)
    refine ⟨t, ?_⟩
    apply List.ofFn_injective
    rw [ofFn_bitVec, ht]

/-- The bijection `τ ≃ (Fin r → Bool)` of a `uniformExact` tape model. -/
noncomputable def bitsEquiv (hlen : ∀ t, (bits t).length = r) (hinj : Function.Injective bits)
    (hsurj : ∀ w : List Bool, w.length = r → ∃ t, bits t = w) : τ ≃ (Fin r → Bool) :=
  Equiv.ofBijective _ (bitVec_bijective r bits hlen hinj hsurj)

theorem ofFn_bitsEquiv (hlen : ∀ t, (bits t).length = r) (hinj : Function.Injective bits)
    (hsurj : ∀ w : List Bool, w.length = r → ∃ t, bits t = w) (t : τ) :
    List.ofFn (bitsEquiv r bits hlen hinj hsurj t) = bits t :=
  ofFn_bitVec r bits hlen t

end Bits

/-! ## The canonical layout of one decider tape -/

/-- **The canonical layout** of a decider tape of length `R ≥ r + reps * s`: the first `r` bits,
read as a reduction tape through the inverse bit bijection `e.symm`, and `reps` consecutive blocks
of `s` bits (block `j`, position `l` is tape position `r + (l + s * j)`); the rest is ignored. -/
def layout {τ : Type} {r s R : ℕ} (e : τ ≃ (Fin r → Bool)) (h : r + reps * s ≤ R)
    (t : Fin R → Bool) : τ × (Fin reps → Fin s → Bool) :=
  (e.symm (fun i => t ⟨i.val, by omega⟩),
    fun j l => t ⟨r + (l.val + s * j.val), by
      have hj := j.isLt
      have hl := l.isLt
      have : l.val + s * j.val < reps * s := by
        calc l.val + s * j.val < s + s * j.val := by omega
          _ = s * (j.val + 1) := by ring
          _ ≤ s * reps := Nat.mul_le_mul_left _ hj
          _ = reps * s := by ring
      omega⟩)

/-- **Layout lemma.** For a tape model `μ` on `τ` whose weights are the uniform weights `2^-r`
along a bijection `e : τ ≃ (Fin r → Bool)` (the admitted `uniformExact` shape), the canonical layout
pushes the uniform law on length-`R` tapes forward to `μ × (uniformTape s)^reps`. -/
theorem layout_prob {τ : Type} [Fintype τ] (μ : FiniteLaw τ) {r s R : ℕ}
    (e : τ ≃ (Fin r → Bool)) (hw : ∀ t, μ.weight t = (1 / 2 : ℝ) ^ r)
    (h : r + reps * s ≤ R) (P : τ × (Fin reps → Fin s → Bool) → Prop) :
    (uniformTape R).prob (fun t => P (layout e h t)) =
      (μ.prod ((uniformTape s).iid reps)).prob P := by
  obtain ⟨x, rfl⟩ : ∃ x, R = (r + reps * s) + x := ⟨R - (r + reps * s), by omega⟩
  -- step C: transport the first coordinate along `e`
  have hC : ((uniformTape r).prod ((uniformTape s).iid reps)).prob
      (fun y => P (e.symm y.1, y.2)) = (μ.prod ((uniformTape s).iid reps)).prob P := by
    apply AModel.prob_equiv ((uniformTape r).prod ((uniformTape s).iid reps))
      (μ.prod ((uniformTape s).iid reps)) (Equiv.prodCongr e.symm (Equiv.refl _))
    intro y
    simp only [FiniteLaw.prod, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, hw]
    rfl
  -- step B: split the first `r + reps*s` bits
  have hB := AModel.uniformTape_split_prob r reps s (fun y => P (e.symm y.1, y.2))
  -- step A: the prefix of length `r + reps*s`
  have hA := AModel.uniformTape_prefix_prob (r + reps * s) x
    (fun u => P (e.symm (AModel.splitEquiv r reps s u).1, (AModel.splitEquiv r reps s u).2))
  rw [← hC, ← hB, ← hA]
  refine congrArg _ (funext fun t => congrArg P (Prod.ext ?_ ?_))
  · show e.symm _ = e.symm _
    congr 1
  · funext j l
    show t _ = _
    rw [AModel.splitEquiv_snd]
    congr 1

end Paper2.ADecider

#print axioms Paper2.ADecider.estOf_lt_iff
#print axioms Paper2.ADecider.est_of_runGood
#print axioms Paper2.ADecider.accepts_iff_majBelow
#print axioms Paper2.ADecider.bitsEquiv
#print axioms Paper2.ADecider.ofFn_bitsEquiv
#print axioms Paper2.ADecider.layout_prob
