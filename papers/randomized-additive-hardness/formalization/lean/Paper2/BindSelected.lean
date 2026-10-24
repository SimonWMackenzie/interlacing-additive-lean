import Paper2.BindClock
import Paper2.BindLaw

/-!
# Two-stage randomized composition in the selected-tape carrier

One fixed monomial outer tape, one finite machine, and a uniform numeric
every-selected-tape clock. The second-stage input is the first-stage machine's
actual printed word; its random tape is a prefix of the physically retained,
independent suffix. The all-event law is an exact mixture, followed by an
explicit two-stage error bound.
-/

noncomputable section

namespace Paper2.SelectedTape.Bind

open Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions
open Paper2.Unit4Shell.Poly
open EthInapproximability.CurrentPaper

def timeC (A B : Algorithm) : ℕ := Classical.choose (fullBound_poly A B)
def timeD (A B : Algorithm) : ℕ :=
  Classical.choose (Classical.choose_spec (fullBound_poly A B))
theorem fullBound_le_monomial (A B : Algorithm) (n : ℕ) :
    fullBound A B n ≤ timeC A B * (n + 1) ^ timeD A B :=
  Classical.choose_spec (Classical.choose_spec (fullBound_poly A B)) n

def algorithm (A B : Algorithm) : Algorithm where
  cR := outerC A B
  dR := outerD A B
  cT := timeC A B
  dT := timeD A B
  machine := machine A B
  output := output A B
  runs := by
    intro x t
    have hrun := machine_outputs A B x t
    exact BitMachine.outputsWithin_mono _ hrun
      ((clock_le_fullBound A B x t).trans (fullBound_le_monomial A B x.length))

theorem algorithm_machine (A B : Algorithm) :
    (algorithm A B).machine = machine A B := rfl

theorem algorithm_output (A B : Algorithm) (x tape : List Bool) :
    (algorithm A B).output x tape = output A B x tape := rfl

theorem algorithm_prob (A B : Algorithm) (x : List Bool)
    (E : List Bool → Prop) :
    (algorithm A B).prob x E =
      ∑ first : Fin (A.tapeLength x) → Bool,
        (uniformTape (A.tapeLength x)).weight first *
          B.prob (A.output x (List.ofFn first)) E := by
  change (uniformTape (outerLength A B x.length)).prob
    (fun t => E (output A B x (List.ofFn t))) = _
  exact mixture_prob A B x E

theorem failure_le (A B : Algorithm) (x : List Bool)
    (Good : List Bool → Prop) (Bad : List Bool → Prop) (ε₁ ε₂ : ℝ)
    (hfirst : A.prob x (fun y => ¬ Good y) ≤ ε₁)
    (hsecond : ∀ y, Good y → B.prob y Bad ≤ ε₂)
    (hε₂ : 0 ≤ ε₂) :
    (algorithm A B).prob x Bad ≤ ε₁ + ε₂ := by
  let μ := uniformTape (A.tapeLength x)
  let ν := uniformTape (suffixLength A B x.length)
  let G : (Fin (A.tapeLength x) → Bool) → Prop :=
    fun first => Good (A.output x (List.ofFn first))
  let F : (Fin (A.tapeLength x) → Bool) →
      (Fin (suffixLength A B x.length) → Bool) → Prop :=
    fun first second => Bad (mixedOutput A B x (List.ofFn first) (List.ofFn second))
  have hfirst' : μ.prob (fun first => ¬ G first) ≤ ε₁ := hfirst
  have hsecond' : ∀ first, G first → ν.prob (F first) ≤ ε₂ := by
    intro first hgood
    change ν.prob (fun second =>
      Bad (mixedOutput A B x (List.ofFn first) (List.ofFn second))) ≤ ε₂
    rw [classifier_prefix_prob A B x first Bad]
    exact hsecond _ hgood
  have h := FiniteLaw.two_stage_failure_le μ ν G F ε₁ ε₂
    hfirst' hsecond' hε₂
  rw [FiniteLaw.prod_prob] at h
  rw [algorithm_prob]
  calc
    _ = ∑ first : Fin (A.tapeLength x) → Bool,
        μ.weight first * ν.prob (F first) := by
          apply Finset.sum_congr rfl
          intro first _
          rw [classifier_prefix_prob A B x first Bad]
    _ ≤ ε₁ + ε₂ := h

#print axioms algorithm_machine
#print axioms algorithm_prob
#print axioms failure_le

end Paper2.SelectedTape.Bind
