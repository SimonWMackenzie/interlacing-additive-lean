import CurrentAdditive.V38SourceBridge

/-! The approved old full measure record has enough strict soundness to
forbid the selected number of colours at the SAME edge arity. It does not
instantiate the stronger epsilon field of GLSourceInput. This minimal facade
keeps exactly the compiler and finite promises used by the cloned source. -/

namespace CurrentAdditive.YaoMinimalSource

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V38Source (colourCount)
open Paper2.YaoCloneSource Paper2.YaoSourceCodec Paper2.YaoLookup
open Paper2.YaoX05Draft (GLSourceDraft forbiddenColours heavy_class)

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem newColours_eq_twice_old (t : ℕ) :
    colourCount t = 2 * forbiddenColours t := by
  have hs : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by decide)
  unfold colourCount forbiddenColours
  calc
    _ = 2 ^ (2 ^ t - 1 + 1) := by rw [Nat.sub_add_cancel hs]
    _ = _ := by rw [pow_succ]; omega

/-- The full old record, unlike its weaker named colouring corollary, already
excludes Snew colours: its strict independent-set bound is exactly 1/Snew. -/
theorem old_full_measure_no_colouring {t : ℕ} (G : GLSourceDraft t)
    (input : List Bool) (hno : input ∉ G.L) :
    ∀ colour : Fin (G.output input).1 → Fin (colourCount t),
      ∃ i c, ∀ j, colour ((G.output input).2.2 i j) = c := by
  intro colour
  have hS : 0 < colourCount t := by simp [colourCount]
  obtain ⟨c, hc⟩ := heavy_class hS (G.measure input) (G.measure_total input hno) colour
  by_contra hcon
  push Not at hcon
  have hind : ∀ i, ∃ j, (G.output input).2.2 i j ∉
      Finset.univ.filter (fun w => colour w = c) := by
    intro i
    obtain ⟨j, hj⟩ := hcon i c
    exact ⟨j, by simpa using hj⟩
  have hlt := G.sound input hno _ hind
  have hden : (2 : ℝ) * (forbiddenColours t : ℝ) = (colourCount t : ℝ) := by
    exact_mod_cast (newColours_eq_twice_old t).symm
  rw [hden] at hlt
  exact (not_lt_of_ge hc) hlt

/-- This is an interface, not an existence theorem. Its ofDraft constructor
below proves the only new finite promise from the full old strict record. -/
structure SourceInput (t : ℕ) where
  L : BinaryLanguage
  machine : BitMachine.Machine
  time : List Bool → ℕ
  output : List Bool → DraftOccSource t
  runs : ∀ input, machine.OutputsWithin input (draftOccEncode (output input)) (time input)
  poly : ∃ c d : ℕ, ∀ input, time input ≤ c * (input.length + 1) ^ d
  complete : ∀ input, input ∈ L → ∃ colour : Fin (output input).1 → Fin (2 ^ t),
    ∀ i c, 2 ^ t - 1 ≤ colourFiberCard (fun j => colour ((output input).2.2 i j)) c
  no_colour : ∀ input, input ∉ L →
    ∀ colour : Fin (output input).1 → Fin (colourCount t),
      ∃ i c, ∀ j, colour ((output input).2.2 i j) = c

def ofDraft {t : ℕ} (G : GLSourceDraft t) : SourceInput t where
  L := G.L
  machine := G.machine
  time := G.time
  output := G.output
  runs := G.runs
  poly := G.poly
  complete := G.complete
  no_colour := old_full_measure_no_colouring G

def ofStrong {t : ℕ} (G : CurrentAdditive.V38Source.GLSourceInput t) : SourceInput t where
  L := G.L
  machine := G.machine
  time := G.time
  output := G.output
  runs := G.runs
  poly := G.poly
  complete := G.complete
  no_colour := CurrentAdditive.V38Source.no_proper_colouring G

def selectedSource {t : ℕ} (G : SourceInput t) (input : List Bool) : YaoSource t :=
  cloneSource t (colourCount t) (G.output input)

theorem selectedSource_nonempty {t : ℕ} (G : SourceInput t) (input : List Bool) :
    0 < (selectedSource G input).1 := cloneVertexCount_pos _ _ _

theorem selectedSource_yes {t : ℕ} (G : SourceInput t) (input : List Bool)
    (hyes : input ∈ G.L) :
    ∃ colour : Fin (selectedSource G input).1 → Fin (2 ^ t),
      ∀ k c, 2 ^ t - 1 ≤ colourFiberCard
        (fun j => colour ((selectedSource G input).2.2 k j)) c := by
  obtain ⟨colour, hbal⟩ := G.complete input hyes
  exact ⟨liftColour ⟨0, by positivity⟩ colour,
    clone_balanced ⟨0, by positivity⟩ colour (G.output input).2.2 hbal⟩

theorem selectedSource_no {t : ℕ} (G : SourceInput t) (input : List Bool)
    (hno : input ∉ G.L) :
    ∀ colour : Fin (selectedSource G input).1 → Fin (colourCount t),
      ∃ k c, ∀ j, colour ((selectedSource G input).2.2 k j) = c :=
  clone_no_proper_colouring (by simp [colourCount])
    (G.output input).2.2 (G.no_colour input hno)

theorem selectedSource_sizes {t : ℕ} (G : SourceInput t) (input : List Bool) :
    (selectedSource G input).1 =
        max 1 ((G.output input).1 * (2 ^ t * 2 ^ t * colourCount t)) ∧
    0 < (selectedSource G input).1 ∧
    (selectedSource G input).2.1 ≤ (G.output input).2.1 *
      (2 ^ t * 2 ^ t * colourCount t) ^ (2 ^ t * 2 ^ t) :=
  cloneSource_sizes t (colourCount t) (G.output input)

/-- Existing stronger-input tables retain the exact same selected source. -/
theorem selectedSource_ofStrong {t : ℕ}
    (G : CurrentAdditive.V38Source.GLSourceInput t) (input : List Bool) :
    selectedSource (ofStrong G) input = CurrentAdditive.V38Source.selectedSource G input := rfl

#print axioms newColours_eq_twice_old
#print axioms old_full_measure_no_colouring
#print axioms ofDraft
#print axioms ofStrong
#print axioms selectedSource_yes
#print axioms selectedSource_no
#print axioms selectedSource_sizes
#print axioms selectedSource_ofStrong

end CurrentAdditive.YaoMinimalSource
