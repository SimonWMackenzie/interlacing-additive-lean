import Paper2.SelectedTape
import Paper2.AModelPrefix

/-!
Restricted, probability-preserving adapters between the source-faithful selected-tape
carrier and the older prefix interface.  No equivalence with *arbitrary* prefix
algorithms is claimed: the reverse direction explicitly requires one literal
monomial random-bit count, fixed uniformly over all input lengths.
-/

noncomputable section

namespace Paper2.SelectedTape

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- Forget the explicit four polynomial witnesses, retaining the exact same
machine, tape length, output, and time in the older prefix interface. -/
def Algorithm.toPrefix (A : Algorithm) : Paper2.AModel.PrefixAlgorithm :=
  { machine := A.machine
    tapeLength := fun n => A.cR * (n + 1) ^ A.dR
    time := fun x => A.cT * (x.length + 1) ^ A.dT
    output := A.output
    runs := A.runs }

theorem Algorithm.toPrefix_polynomial (A : Algorithm) :
    A.toPrefix.Polynomial := by
  refine ⟨A.cR + A.cT, A.dR + A.dT, ?_⟩
  intro x
  let N := x.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hR : N ^ A.dR ≤ N ^ (A.dR + A.dT) :=
    Nat.pow_le_pow_right hN (Nat.le_add_right _ _)
  have hT : N ^ A.dT ≤ N ^ (A.dR + A.dT) :=
    Nat.pow_le_pow_right hN (Nat.le_add_left _ _)
  constructor
  · change A.cR * N ^ A.dR ≤ (A.cR + A.cT) * N ^ (A.dR + A.dT)
    calc
      A.cR * N ^ A.dR ≤ A.cR * N ^ (A.dR + A.dT) :=
        Nat.mul_le_mul_left A.cR hR
      _ ≤ (A.cR + A.cT) * N ^ (A.dR + A.dT) :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · change A.cT * N ^ A.dT ≤ (A.cR + A.cT) * N ^ (A.dR + A.dT)
    calc
      A.cT * N ^ A.dT ≤ A.cT * N ^ (A.dR + A.dT) :=
        Nat.mul_le_mul_left A.cT hT
      _ ≤ (A.cR + A.cT) * N ^ (A.dR + A.dT) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

theorem Algorithm.toPrefix_prob (A : Algorithm) (x : List Bool)
    (E : List Bool → Prop) :
    A.toPrefix.prob x E = A.prob x E := by
  rfl

theorem Algorithm.toPrefix_decides {L : BinaryLanguage} (A : Algorithm)
    (hA : A.Decides L (1 / 3)) : A.toPrefix.Decides L (1 / 3) := by
  intro x
  rw [A.toPrefix_prob]
  exact hA x

private noncomputable def prefixC (A : Paper2.AModel.PrefixAlgorithm)
    (hp : A.Polynomial) : ℕ := Classical.choose hp
private noncomputable def prefixD (A : Paper2.AModel.PrefixAlgorithm)
    (hp : A.Polynomial) : ℕ := Classical.choose (Classical.choose_spec hp)
private theorem prefixTimeBound (A : Paper2.AModel.PrefixAlgorithm)
    (hp : A.Polynomial) (x : List Bool) :
    A.time x ≤ prefixC A hp * (x.length + 1) ^ prefixD A hp :=
  (Classical.choose_spec (Classical.choose_spec hp) x).2

private noncomputable def tapeC (A : Paper2.AModel.PrefixAlgorithm)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR) : ℕ :=
  Classical.choose hR
private noncomputable def tapeD (A : Paper2.AModel.PrefixAlgorithm)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR) : ℕ :=
  Classical.choose (Classical.choose_spec hR)
private theorem tapeEq (A : Paper2.AModel.PrefixAlgorithm)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR) (n : ℕ) :
    A.tapeLength n = tapeC A hR * (n + 1) ^ tapeD A hR :=
  Classical.choose_spec (Classical.choose_spec hR) n

/-- A prefix algorithm with a specified *fixed monomial* tape length is a
selected-tape algorithm. The same physical machine and output are retained;
only the polynomial time witness is enlarged to a monomial. -/
def Algorithm.ofPrefixMonomial (A : Paper2.AModel.PrefixAlgorithm)
    (hp : A.Polynomial)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR) : Algorithm := by
  let cR := tapeC A hR
  let dR := tapeD A hR
  let cT := prefixC A hp
  let dT := prefixD A hp
  refine { cR := cR, dR := dR, cT := cT, dT := dT,
           machine := A.machine, output := A.output, runs := ?_ }
  intro x t
  have heq : A.tapeLength x.length = cR * (x.length + 1) ^ dR :=
    tapeEq A hR x.length
  let t' : Fin (A.tapeLength x.length) → Bool :=
    fun i => t (Fin.cast heq i)
  have ht : List.ofFn t' = List.ofFn t := by
    apply List.ext_getElem
    · simpa [t'] using heq
    · intro i h1 h2
      simp [t', Fin.cast]
  have hr := A.runs x t'
  rw [ht] at hr
  exact BitMachine.outputsWithin_mono _ hr (prefixTimeBound A hp x)

theorem Algorithm.ofPrefixMonomial_prob (A : Paper2.AModel.PrefixAlgorithm)
    (hp : A.Polynomial)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR)
    (x : List Bool) (E : List Bool → Prop) :
    (Algorithm.ofPrefixMonomial A hp hR).prob x E = A.prob x E := by
  change (Paper2.Unit4Shell.Definitions.uniformTape
      (tapeC A hR * (x.length + 1) ^ tapeD A hR)).prob
        (fun t => E (A.output x (List.ofFn t))) =
    (Paper2.Unit4Shell.Definitions.uniformTape (A.tapeLength x.length)).prob
        (fun t => E (A.output x (List.ofFn t)))
  exact congrArg (fun n : ℕ =>
    (Paper2.Unit4Shell.Definitions.uniformTape n).prob
      (fun t => E (A.output x (List.ofFn t))))
    (tapeEq A hR x.length).symm

theorem Algorithm.ofPrefixMonomial_decides {L : BinaryLanguage}
    (A : Paper2.AModel.PrefixAlgorithm) (hp : A.Polynomial)
    (hR : ∃ cR dR : ℕ, ∀ n, A.tapeLength n = cR * (n + 1) ^ dR)
    (hA : A.Decides L (1 / 3)) :
    (Algorithm.ofPrefixMonomial A hp hR).Decides L (1 / 3) := by
  intro x
  rw [Algorithm.ofPrefixMonomial_prob]
  exact hA x

end Paper2.SelectedTape

#print axioms Paper2.SelectedTape.Algorithm.toPrefix_polynomial
#print axioms Paper2.SelectedTape.Algorithm.toPrefix_prob
#print axioms Paper2.SelectedTape.Algorithm.ofPrefixMonomial_prob
#print axioms Paper2.SelectedTape.Algorithm.ofPrefixMonomial_decides
