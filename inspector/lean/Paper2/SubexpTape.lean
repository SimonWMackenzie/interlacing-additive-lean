import Paper2.SubexpLen
import Paper2.AModelPrefix

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 1: the effective subexponential tape carrier

Lock v12 `sections/06-reduction.tex:95-102` (`def:reth`):
"Randomized sparse ETH asserts that, for some fixed constant $c_s$, there is no bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$. The sparse source assumption is made directly; no deterministic ETH assumption
is being silently extended to randomized algorithms."

ROOT DECISION R19 (`MODEL_REPAIR_2026-09-27.md`): the older carriers
`Unit4Shell.Definitions.RandomizedAlgorithm` and `AModel.PrefixAlgorithm` are defective as class
carriers (tape length leaks advice); "The ETH model also needs an explicitly effective,
potentially subexponential tape budget".

Author decisions (`AUTHOR_DECISIONS_2026-09-27.md`): **D-A1** (one deterministic `BitMachine` on
`pair input tape`, uniform tape of a length fixed before the input, the machine reads a prefix)
and **D-A6** (the ETH shape: worst-case time `≤ 2^(εN)(|input|+1)^(O(1))` for every `ε > 0`
eventually, promise form).

`SubexpTape.Algorithm` fixes, BEFORE any input:
* ONE finite machine `machine`;
* ONE tape-length function `tapeLen : ℕ → ℕ` of the input LENGTH that is EFFECTIVE: a fixed bit
  machine `lenMachine` prints `1^(tapeLen m)` from `1^m` within `lenTime m` (`lenRuns`), and both
  `tapeLen` and `lenTime` are subexponential in `m` (`Subexp`, explicit polynomial factor);
* the machine runs on the actual pair encoding `pair x tape` for EVERY word `x` and EVERY tape of
  exactly `tapeLen |x|` bits and halts within the declared worst-case clock `time x` (`runs`).

Why the tape budget is stated in `|x|` and not in the variable count `N`: a length-only function
cannot be `≤ 2^(εN)` for all sparse inputs of one length once it is large enough for the
reduction's `2^(Θ(N/log N))` bits: sparse inputs of length `m` have `N` anywhere between
`Θ(m / log m)` (many clauses; binary literal fields) and `m - O(1)` (no clauses). The lock bounds
TIME, not random bits; how many tape bits a step can pop is program-dependent. The ETH time budget in `N` is
imposed by `SubexpETH.RandomizedSparseETH_effective` on the promise inputs.

The tape is advice-free: `tapeLen` is one fixed computable function (no input-dependent choice),
unlike `AModel.PrefixAlgorithm.tapeLength` (an arbitrary, possibly uncomputable function).

Also: `toPrefix` (same machine, tape, clock, output; probabilities definitionally equal), the
prefix and two-segment tape laws (reusing `AModel.uniformTape_take_prob` and
`AModel.uniformTape_take_drop_prob` by exact name), and `withExpLen`, the constructor with the
concrete effective length `SubexpLen.expLen` and its proved machine `lenMachine`.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth.SubexpTape

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

/-- **The effective subexponential-tape randomized algorithm** (lock `def:reth`, "bounded-error
randomized algorithm ... in worst-case time"; R19 effective tape budget; D-A1, D-A6). -/
structure Algorithm where
  /-- the tape length, a function of the input length only -/
  tapeLen : ℕ → ℕ
  /-- the fixed machine computing the tape length in unary -/
  lenMachine : BitMachine.Machine
  /-- the clock of `lenMachine` -/
  lenTime : ℕ → ℕ
  lenRuns : ∀ m, lenMachine.OutputsWithin (List.replicate m true)
    (List.replicate (tapeLen m) true) (lenTime m)
  tapeSubexp : Subexp tapeLen
  lenTimeSubexp : Subexp lenTime
  /-- the ONE finite decision machine -/
  machine : BitMachine.Machine
  /-- the declared worst-case clock (valid on every tape) -/
  time : List Bool → ℕ
  /-- the printed word -/
  output : List Bool → List Bool → List Bool
  runs : ∀ x (t : Fin (tapeLen x.length) → Bool),
    machine.OutputsWithin (pair x (List.ofFn t)) (output x (List.ofFn t)) (time x)

namespace Algorithm

variable (A : Algorithm)

/-- Event probability of the printed word under the uniform tape of length `tapeLen |x|`. -/
def prob (x : List Bool) (E : List Bool → Prop) : ℝ :=
  (uniformTape (A.tapeLen x.length)).prob (fun t => E (A.output x (List.ofFn t)))

/-- Bounded-error decision with error `err` (accept = printed word `[true]`). -/
def Decides (L : BinaryLanguage) (err : ℝ) : Prop :=
  ∀ x, (x ∈ L → 1 - err ≤ A.prob x (· = [true])) ∧ (x ∉ L → A.prob x (· = [true]) ≤ err)

/-- Forget effectivity: the same machine, tape length, clock and output as an
`AModel.PrefixAlgorithm` (the older, defective carrier). -/
def toPrefix : Paper2.AModel.PrefixAlgorithm where
  machine := A.machine
  tapeLength := A.tapeLen
  time := A.time
  output := A.output
  runs := A.runs

theorem prob_toPrefix (x : List Bool) (E : List Bool → Prop) :
    A.toPrefix.prob x E = A.prob x E := rfl

theorem decides_toPrefix (L : BinaryLanguage) (err : ℝ) :
    A.Decides L err ↔ A.toPrefix.Decides L err := Iff.rfl

/-- The printed word depends only on the first `r` tape bits (semantic prefix reading). -/
def ReadsPrefix (r : List Bool → ℕ) : Prop :=
  ∀ x, r x ≤ A.tapeLen x.length ∧ ∃ G : List Bool → List Bool,
    ∀ t : Fin (A.tapeLen x.length) → Bool, A.output x (List.ofFn t) = G ((List.ofFn t).take (r x))

/-- **Reading a prefix, only the uniform prefix law matters** (D-A1 tape lemma, reused from
`AModel.uniformTape_take_prob`). -/
theorem prob_of_readsPrefix {r : List Bool → ℕ} (hA : A.ReadsPrefix r) (x : List Bool)
    (E : List Bool → Prop) :
    ∃ G : List Bool → List Bool,
      A.prob x E = (uniformTape (r x)).prob (fun s => E (G (List.ofFn s))) := by
  obtain ⟨hle, G, hG⟩ := hA x
  refine ⟨G, ?_⟩
  unfold prob
  have h1 : (fun t : Fin (A.tapeLen x.length) → Bool => E (A.output x (List.ofFn t))) =
      (fun t => (fun w => E (G w)) ((List.ofFn t).take (r x))) := by
    funext t; rw [hG t]
  rw [h1]
  exact Paper2.AModel.uniformTape_take_prob hle (fun w => E (G w))

end Algorithm

/-- **Two consecutive segments of a uniform tape are uniform and independent** (word form):
for `r0 + r1 ≤ R`, the pair (first `r0` bits, next `r1` bits) of a uniform length-`R` tape has
the product of the uniform laws. Reuses `AModel.uniformTape_take_prob` and
`AModel.uniformTape_take_drop_prob` by exact name. -/
theorem uniform_segments_prob {r0 r1 R : ℕ} (h : r0 + r1 ≤ R)
    (F : List Bool → List Bool → Prop) :
    (uniformTape R).prob (fun t =>
        F ((List.ofFn t).take r0) (((List.ofFn t).drop r0).take r1)) =
      ((uniformTape r0).prod (uniformTape r1)).prob
        (fun x => F (List.ofFn x.1) (List.ofFn x.2)) := by
  have e : (fun t : Fin R → Bool =>
        F ((List.ofFn t).take r0) (((List.ofFn t).drop r0).take r1)) =
      (fun t => (fun w : List Bool => F (w.take r0) (w.drop r0))
        ((List.ofFn t).take (r0 + r1))) := by
    funext t
    simp only [List.take_take, List.drop_take]
    congr 2
    · omega
    · omega
  rw [e, Paper2.AModel.uniformTape_take_prob h (fun w => F (w.take r0) (w.drop r0))]
  exact Paper2.AModel.uniformTape_take_drop_prob r0 r1 F

/-- **The constructor with the proved effective length** `SubexpLen.expLen` (machine
`SubexpLen.lenMachine`, clock `SubexpLen.lenTime`, both proved subexponential). -/
def withExpLen (machine : BitMachine.Machine) (time : List Bool → ℕ)
    (output : List Bool → List Bool → List Bool)
    (runs : ∀ x (t : Fin (expLen x.length) → Bool),
      machine.OutputsWithin (pair x (List.ofFn t)) (output x (List.ofFn t)) (time x)) :
    Algorithm where
  tapeLen := expLen
  lenMachine := lenMachine
  lenTime := lenTime
  lenRuns := lenMachine_outputs
  tapeSubexp := expLen_subexp
  lenTimeSubexp := lenTime_subexp
  machine := machine
  time := time
  output := output
  runs := runs

theorem withExpLen_tapeLen (machine : BitMachine.Machine) (time : List Bool → ℕ)
    (output : List Bool → List Bool → List Bool) (runs) :
    (withExpLen machine time output runs).tapeLen = expLen := rfl

end Paper2.AEth.SubexpTape

end

#print axioms Paper2.AEth.SubexpTape.Algorithm.prob_toPrefix
#print axioms Paper2.AEth.SubexpTape.Algorithm.prob_of_readsPrefix
#print axioms Paper2.AEth.SubexpTape.uniform_segments_prob
#print axioms Paper2.AEth.SubexpTape.withExpLen
