import Paper2.SubexpTape
-- root successor copy (30 September 2026, for the R22 batch): on top of a-carrier-owner-2's R22 copy: the header sentence 'Everything else is unchanged' and the toOld docstring 'same fields', both false once the extend field was added (readback:a-carrier-2 defect DC1) corrected; no other change.

/-!
# Paper A (lock v12), lane `owner:a-eth-2`, segment 1: the R20-repaired effective tape carrier

Lock v12 `sections/06-reduction.tex:95-102` (`def:reth`):
"Randomized sparse ETH asserts that, for some fixed constant $c_s$, there is no bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$."

ROOT DECISION R20 (`MODEL_REPAIR_2026-09-27.md`, last section): the carrier
`SubexpTape.Algorithm` of lane `a-eth-owner-1` is ratified WITH the M2 repair: "The length
machine's clock must be polynomial in its input and output,
`lenTime m <= C * (m + tapeLen m + 1)^E` for fixed constants".

`ETape.Algorithm` is `SubexpTape.Algorithm` with the field `lenTimeSubexp` REPLACED by two fixed
natural constants `lenC`, `lenE` and the requirement `lenPoly`, and (root decision R22) with the field
`extend` (extension invariance) added. Everything else is unchanged:
ONE finite machine and ONE computable subexponential tape length `tapeLen |x|` fixed before the
input, worst-case clock on every tape of exactly that length, on the actual pair encoding.

Re-derived here: the old field (`lenTime_subexp`, from `lenPoly` and `tapeSubexp`), hence the
forgetful map `toOld` into the a-eth-owner-1 carrier with DEFINITIONALLY equal probabilities
(every lemma proved there for `SubexpTape.Algorithm` applies through `toOld`); `toPrefix`;
`ReadsPrefix` / `prob_of_readsPrefix`; the concrete constructor `withExpLen` (the proved length
machine `Paper2.AEth.lenMachine`, clock `BL (m+1)^2 + 20 expLen m <= (BL+20)(m + expLen m + 1)^2`).

The length computation within the decider's own clock (`lenCap`, `lenCap_decides`): running the
fixed length machine for `lenCap x = lenC (|x| + min (tapeLen |x|) (time x) + 1)^lenE` steps
either halts with `1^(tapeLen |x|)` or certifies `time x < tapeLen |x|`; under the `extend` field
the run never depends on the tape's end. `ETapeETH.whole_budget` bounds `lenCap + time` by the D-A6 budget.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

/-- `⌈2^(a x)⌉^E ≤ 2^E ⌈2^(b x)⌉` when `a E ≤ b` (the exponent bookkeeping of polynomial
composition with a `⌈2^(εm)⌉` budget). -/
theorem ceil_pow_le {a b x : ℝ} (E : ℕ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hab : a * E ≤ b) :
    ⌈(2 : ℝ) ^ (a * x)⌉₊ ^ E ≤ 2 ^ E * ⌈(2 : ℝ) ^ (b * x)⌉₊ := by
  have hy1 : (1 : ℝ) ≤ (2 : ℝ) ^ (a * x) := Real.one_le_rpow (by norm_num) (mul_nonneg ha hx)
  have hc : (⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ) ≤ 2 * (2 : ℝ) ^ (a * x) :=
    le_of_lt (Nat.ceil_lt_two_mul (by linarith))
  have hpow : ((⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ)) ^ E ≤ (2 * (2 : ℝ) ^ (a * x)) ^ E :=
    pow_le_pow_left₀ (by positivity) hc E
  have he : ((2 : ℝ) ^ (a * x)) ^ E = (2 : ℝ) ^ (a * x * E) :=
    (Real.rpow_mul_natCast (by norm_num) _ _).symm
  have hle : (2 : ℝ) ^ (a * x * E) ≤ (2 : ℝ) ^ (b * x) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : a * x * E = (a * E) * x := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hab hx
  have hceil : (2 : ℝ) ^ (b * x) ≤ (⌈(2 : ℝ) ^ (b * x)⌉₊ : ℝ) := Nat.le_ceil _
  have key : ((⌈(2 : ℝ) ^ (a * x)⌉₊ ^ E : ℕ) : ℝ) ≤ ((2 ^ E * ⌈(2 : ℝ) ^ (b * x)⌉₊ : ℕ) : ℝ) := by
    push_cast
    calc ((⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ)) ^ E ≤ (2 * (2 : ℝ) ^ (a * x)) ^ E := hpow
      _ = 2 ^ E * ((2 : ℝ) ^ (a * x)) ^ E := by rw [mul_pow]
      _ = 2 ^ E * (2 : ℝ) ^ (a * x * E) := by rw [he]
      _ ≤ 2 ^ E * (⌈(2 : ℝ) ^ (b * x)⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans hle hceil) (by positivity)
  exact_mod_cast key

theorem one_le_ceil_two_rpow (y : ℝ) : 1 ≤ ⌈(2 : ℝ) ^ y⌉₊ := by
  have : (0 : ℝ) < (2 : ℝ) ^ y := by positivity
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    linarith)

theorem eps_div_mul_le (ε : ℝ) (hε : 0 < ε) (E : ℕ) : ε / (E + 1) * E ≤ ε := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **A fixed polynomial in `m` and a subexponential `g m` is subexponential.** -/
theorem subexp_poly_comp {g h : ℕ → ℕ} (C E : ℕ) (hg : Paper2.AEth.Subexp g)
    (hh : ∀ m, h m ≤ C * (m + g m + 1) ^ E) : Paper2.AEth.Subexp h := by
  intro ε hε
  have hε₀ : 0 < ε / (E + 1) := by positivity
  obtain ⟨C₀, d, m₀, hC₀⟩ := hg (ε / (E + 1)) hε₀
  refine ⟨C * ((C₀ + 1) ^ E * 2 ^ E), (d + 1) * E, m₀, fun m hm => ?_⟩
  have hgm := hC₀ m hm
  have hX := one_le_ceil_two_rpow (ε / (E + 1) * m)
  have hXE := ceil_pow_le (x := (m : ℝ)) E hε₀.le (Nat.cast_nonneg m) (eps_div_mul_le ε hε E)
  generalize ⌈(2 : ℝ) ^ (ε / (E + 1) * m)⌉₊ = X at hgm hX hXE
  generalize ⌈(2 : ℝ) ^ (ε * m)⌉₊ = Y at hXE ⊢
  have hP : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  generalize hPd : (m + 1) ^ d = P at hgm hP
  have hpow : (m + 1) ^ ((d + 1) * E) = (P * (m + 1)) ^ E := by
    rw [pow_mul, pow_succ, hPd]
  have hXP : 1 ≤ X * P := by simpa using Nat.mul_le_mul hX hP
  have h1 : (m + 1) * 1 ≤ (m + 1) * (X * P) := Nat.mul_le_mul_left _ hXP
  have h2 : C₀ * X * P * 1 ≤ C₀ * X * P * (m + 1) := Nat.mul_le_mul_left _ (by omega)
  have hbase : m + g m + 1 ≤ (C₀ + 1) * X * (P * (m + 1)) := by
    have e : (C₀ + 1) * X * (P * (m + 1)) = C₀ * X * P * (m + 1) + (m + 1) * (X * P) := by ring
    rw [e]
    omega
  have hstep : (m + g m + 1) ^ E ≤ ((C₀ + 1) * X * (P * (m + 1))) ^ E :=
    Nat.pow_le_pow_left hbase E
  rw [hpow]
  calc h m ≤ C * (m + g m + 1) ^ E := hh m
    _ ≤ C * ((C₀ + 1) * X * (P * (m + 1))) ^ E := Nat.mul_le_mul_left _ hstep
    _ = C * ((C₀ + 1) ^ E * X ^ E * (P * (m + 1)) ^ E) := by rw [mul_pow, mul_pow]
    _ ≤ C * ((C₀ + 1) ^ E * (2 ^ E * Y) * (P * (m + 1)) ^ E) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_left _ hXE
    _ = C * ((C₀ + 1) ^ E * 2 ^ E) * Y * (P * (m + 1)) ^ E := by ring

namespace ETape

/-- **The R20-repaired effective tape randomized algorithm** (lock `def:reth`; R19, R20; D-A1,
D-A6). Fixed before the input: the finite machines `lenMachine`, `machine`, the tape length
`tapeLen` (subexponential in the input length), and the constants `lenC`, `lenE` of the length
machine's polynomial clock in its input and output (`lenPoly`, the R20 repair of M2). -/
structure Algorithm where
  /-- the tape length, a function of the input length only -/
  tapeLen : ℕ → ℕ
  /-- the fixed machine computing the tape length in unary -/
  lenMachine : BitMachine.Machine
  /-- the clock of `lenMachine` -/
  lenTime : ℕ → ℕ
  /-- R20: fixed constants of the length machine's polynomial clock -/
  lenC : ℕ
  lenE : ℕ
  lenRuns : ∀ m, lenMachine.OutputsWithin (List.replicate m true)
    (List.replicate (tapeLen m) true) (lenTime m)
  /-- R20: the length machine is polynomial in its input and output -/
  lenPoly : ∀ m, lenTime m ≤ lenC * (m + tapeLen m + 1) ^ lenE
  tapeSubexp : Paper2.AEth.Subexp tapeLen
  /-- the ONE finite decision machine -/
  machine : BitMachine.Machine
  /-- the declared worst-case clock (valid on every tape) -/
  time : List Bool → ℕ
  /-- the printed word -/
  output : List Bool → List Bool → List Bool
  runs : ∀ x (t : Fin (tapeLen x.length) → Bool),
    machine.OutputsWithin (pair x (List.ofFn t)) (output x (List.ofFn t)) (time x)
  /-- extension invariance, the R22 repair: the run within `time x` never depends on the tape's
  end (appending any `u` to a tape of exactly `tapeLen |x|` bits keeps the output and clock) -/
  extend : ∀ x (t u : List Bool), t.length = tapeLen x.length →
    machine.OutputsWithin (pair x (t ++ u)) (output x t) (time x)

namespace Algorithm

variable (A : Algorithm)

/-- The old field `lenTimeSubexp` is DERIVED from the R20 requirement. -/
theorem lenTime_subexp : Paper2.AEth.Subexp A.lenTime :=
  subexp_poly_comp A.lenC A.lenE A.tapeSubexp A.lenPoly

/-- Forget the R20 constants and the R22 field `extend`: the a-eth-owner-1 carrier. -/
def toOld : Paper2.AEth.SubexpTape.Algorithm where
  tapeLen := A.tapeLen
  lenMachine := A.lenMachine
  lenTime := A.lenTime
  lenRuns := A.lenRuns
  tapeSubexp := A.tapeSubexp
  lenTimeSubexp := A.lenTime_subexp
  machine := A.machine
  time := A.time
  output := A.output
  runs := A.runs

/-- Event probability of the printed word under the uniform tape of length `tapeLen |x|`. -/
def prob (x : List Bool) (E : List Bool → Prop) : ℝ :=
  (uniformTape (A.tapeLen x.length)).prob (fun t => E (A.output x (List.ofFn t)))

theorem prob_toOld (x : List Bool) (E : List Bool → Prop) :
    A.toOld.prob x E = A.prob x E := rfl

/-- Bounded-error decision with error `err` (accept = printed word `[true]`). -/
def Decides (L : BinaryLanguage) (err : ℝ) : Prop :=
  ∀ x, (x ∈ L → 1 - err ≤ A.prob x (· = [true])) ∧ (x ∉ L → A.prob x (· = [true]) ≤ err)

theorem decides_toOld (L : BinaryLanguage) (err : ℝ) :
    A.Decides L err ↔ A.toOld.Decides L err := Iff.rfl

/-- The older prefix carrier (same machine, tape, clock, output). -/
def toPrefix : Paper2.AModel.PrefixAlgorithm := A.toOld.toPrefix

theorem prob_toPrefix (x : List Bool) (E : List Bool → Prop) :
    A.toPrefix.prob x E = A.prob x E := rfl

/-- Semantic prefix reading (as in the old carrier). -/
def ReadsPrefix (r : List Bool → ℕ) : Prop :=
  ∀ x, r x ≤ A.tapeLen x.length ∧ ∃ G : List Bool → List Bool,
    ∀ t : Fin (A.tapeLen x.length) → Bool, A.output x (List.ofFn t) = G ((List.ofFn t).take (r x))

theorem readsPrefix_toOld (r : List Bool → ℕ) : A.ReadsPrefix r ↔ A.toOld.ReadsPrefix r :=
  Iff.rfl

/-- Re-derived from the old carrier's `prob_of_readsPrefix` through `toOld`. -/
theorem prob_of_readsPrefix {r : List Bool → ℕ} (hA : A.ReadsPrefix r) (x : List Bool)
    (E : List Bool → Prop) :
    ∃ G : List Bool → List Bool,
      A.prob x E = (uniformTape (r x)).prob (fun s => E (G (List.ofFn s))) :=
  A.toOld.prob_of_readsPrefix hA x E

/-- **The length budget within the decider's own clock.** -/
def lenCap (x : List Bool) : ℕ :=
  A.lenC * (x.length + min (A.tapeLen x.length) (A.time x) + 1) ^ A.lenE

/-- If the tape is not longer than the clock, the length machine finishes within `lenCap`. -/
theorem lenCap_runs (x : List Bool) (h : A.tapeLen x.length ≤ A.time x) :
    A.lenMachine.OutputsWithin (List.replicate x.length true)
      (List.replicate (A.tapeLen x.length) true) (A.lenCap x) := by
  refine BitMachine.outputsWithin_mono A.lenMachine (A.lenRuns x.length) ?_
  refine le_trans (A.lenPoly x.length) ?_
  unfold lenCap
  rw [min_eq_left h]

/-- **Physical length decision within `lenCap`.** Running the fixed length machine on `1^|x|`
for exactly `lenCap x` steps either halts with output `1^(tapeLen |x|)`, or has not halted and
then certifies `time x < tapeLen |x|`; under the `extend` field the run never depends on the
tape's end. -/
theorem lenCap_decides (x : List Bool) :
    ((A.lenMachine.run (A.lenCap x) (A.lenMachine.init (List.replicate x.length true))).l = none ∧
      (A.lenMachine.run (A.lenCap x)
        (A.lenMachine.init (List.replicate x.length true))).stk A.lenMachine.output =
        List.replicate (A.tapeLen x.length) true) ∨
    ((A.lenMachine.run (A.lenCap x) (A.lenMachine.init (List.replicate x.length true))).l ≠ none ∧
      A.time x < A.tapeLen x.length) := by
  by_cases h : A.tapeLen x.length ≤ A.time x
  · exact Or.inl (BitMachine.outputsWithin_at_bound A.lenMachine (A.lenCap_runs x h))
  · by_cases hl : (A.lenMachine.run (A.lenCap x)
        (A.lenMachine.init (List.replicate x.length true))).l = none
    · refine Or.inl ⟨hl, ?_⟩
      have hw : A.lenMachine.OutputsWithin (List.replicate x.length true)
          ((A.lenMachine.run (A.lenCap x)
            (A.lenMachine.init (List.replicate x.length true))).stk A.lenMachine.output)
          (A.lenCap x) := ⟨A.lenCap x, le_refl _, hl, rfl⟩
      exact BitMachine.outputsWithin_unique A.lenMachine hw (A.lenRuns x.length)
    · exact Or.inr ⟨hl, by omega⟩

end Algorithm

/-- The proved length clock is polynomial in input and output (R20 for `withExpLen`). -/
theorem expLen_lenPoly (m : ℕ) :
    Paper2.AEth.lenTime m ≤ (Paper2.AEth.BL + 20) * (m + Paper2.AEth.expLen m + 1) ^ 2 := by
  unfold Paper2.AEth.lenTime
  have h1 : (m + 1) ^ 2 ≤ (m + Paper2.AEth.expLen m + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h2 : Paper2.AEth.expLen m ≤ (m + Paper2.AEth.expLen m + 1) ^ 2 :=
    le_trans (by omega : Paper2.AEth.expLen m ≤ m + Paper2.AEth.expLen m + 1)
      (Nat.le_self_pow (by norm_num) _)
  generalize (m + Paper2.AEth.expLen m + 1) ^ 2 = Q at h1 h2 ⊢
  generalize Paper2.AEth.BL = b
  have h3 : b * (m + 1) ^ 2 ≤ b * Q := Nat.mul_le_mul_left _ h1
  have e : (b + 20) * Q = b * Q + 20 * Q := by ring
  rw [e]
  omega

/-- **The constructor with the proved effective length** `Paper2.AEth.expLen` (length machine
`Paper2.AEth.lenMachine`, R20 constants `BL + 20`, `2`). -/
def withExpLen (machine : BitMachine.Machine) (time : List Bool → ℕ)
    (output : List Bool → List Bool → List Bool)
    (runs : ∀ x (t : Fin (Paper2.AEth.expLen x.length) → Bool),
      machine.OutputsWithin (pair x (List.ofFn t)) (output x (List.ofFn t)) (time x))
    (extend : ∀ x (t u : List Bool), t.length = Paper2.AEth.expLen x.length →
      machine.OutputsWithin (pair x (t ++ u)) (output x t) (time x)) :
    Algorithm where
  tapeLen := Paper2.AEth.expLen
  lenMachine := Paper2.AEth.lenMachine
  lenTime := Paper2.AEth.lenTime
  lenC := Paper2.AEth.BL + 20
  lenE := 2
  lenRuns := Paper2.AEth.lenMachine_outputs
  lenPoly := expLen_lenPoly
  tapeSubexp := Paper2.AEth.expLen_subexp
  machine := machine
  time := time
  output := output
  runs := runs
  extend := extend

theorem withExpLen_tapeLen (machine : BitMachine.Machine) (time : List Bool → ℕ)
    (output : List Bool → List Bool → List Bool) (runs) (extend) :
    (withExpLen machine time output runs extend).tapeLen = Paper2.AEth.expLen := rfl

end ETape

end Paper2.AEth2

end

#print axioms Paper2.AEth2.ceil_pow_le
#print axioms Paper2.AEth2.subexp_poly_comp
#print axioms Paper2.AEth2.ETape.Algorithm.lenTime_subexp
#print axioms Paper2.AEth2.ETape.Algorithm.toOld
#print axioms Paper2.AEth2.ETape.Algorithm.prob_toOld
#print axioms Paper2.AEth2.ETape.Algorithm.prob_of_readsPrefix
#print axioms Paper2.AEth2.ETape.Algorithm.lenCap_runs
#print axioms Paper2.AEth2.ETape.Algorithm.lenCap_decides
#print axioms Paper2.AEth2.ETape.expLen_lenPoly
#print axioms Paper2.AEth2.ETape.withExpLen
