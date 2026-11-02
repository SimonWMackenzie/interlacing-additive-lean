import CurrentAdditive.V38Public
import Paper2.YaoX05Draft

/-!
Private v38 source interface. The record below is an *uninstantiated external
contract*: this file does not assert that a Guruswami--Lee compiler has been
formalized. The selected source uses Q=k=2^t, edge size K=2^t*2^t, and
S=2^(2^t). It cannot be supplied by the older `GLSourceDraft t`, whose
independent-set bound uses S=2^(2^t-1).

Source: v38 appendices/sources.tex, `yao:gl` and proof of `yao:source`.
-/

namespace CurrentAdditive.V38Source

open Paper2.YaoCloneSource Paper2.YaoLookup
open Paper2.YaoX05Draft (heavy_class)
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def colourCount (t : ℕ) : ℕ := 2 ^ (2 ^ t)

/-- Exact v38 external-source input, not an existence theorem or axiom. -/
structure GLSourceInput (t : ℕ) where
  L : BinaryLanguage
  machine : BitMachine.Machine
  time : List Bool → ℕ
  output : List Bool → DraftOccSource t
  runs : ∀ input, machine.OutputsWithin input (draftOccEncode (output input)) (time input)
  poly : ∃ c d : ℕ, ∀ input, time input ≤ c * (input.length + 1) ^ d
  complete : ∀ input, input ∈ L → ∃ colour : Fin (output input).1 → Fin (2 ^ t),
    ∀ i c, 2 ^ t - 1 ≤ colourFiberCard (fun j => colour ((output input).2.2 i j)) c
  measure : ∀ input, Fin (output input).1 → ℝ
  measure_nonneg : ∀ input w, 0 ≤ measure input w
  measure_total : ∀ input, input ∉ L → ∑ w, measure input w = 1
  sound : ∀ input, input ∉ L → ∀ I : Finset (Fin (output input).1),
    (∀ i, ∃ j, (output input).2.2 i j ∉ I) →
      ∑ w ∈ I, measure input w < 1 / (2 * (colourCount t : ℝ))

/-- The source measure promise rules out a proper S-colouring. -/
theorem no_proper_colouring {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (hno : input ∉ G.L) :
    ∀ colour : Fin (G.output input).1 → Fin (colourCount t),
      ∃ i c, ∀ j, colour ((G.output input).2.2 i j) = c := by
  intro colour
  have hS : 0 < colourCount t := by simp [colourCount]
  obtain ⟨c, hc⟩ := heavy_class hS (G.measure input)
    (G.measure_total input hno) colour
  by_contra hcon
  push Not at hcon
  have hind : ∀ i, ∃ j, (G.output input).2.2 i j ∉
      Finset.univ.filter (fun w => colour w = c) := by
    intro i
    obtain ⟨j, hj⟩ := hcon i c
    exact ⟨j, by simpa using hj⟩
  have hlt := G.sound input hno _ hind
  have hSpos : (0 : ℝ) < colourCount t := by exact_mod_cast hS
  have hstrict : 1 / (2 * (colourCount t : ℝ)) <
      1 / (colourCount t : ℝ) := by
    apply one_div_lt_one_div_of_lt hSpos
    linarith
  linarith

/-- The selected v38 clone has a nonempty vertex set, same edge arity K. -/
def selectedSource {t : ℕ} (G : GLSourceInput t) (input : List Bool) :
    Paper2.YaoSourceCodec.YaoSource t :=
  cloneSource t (colourCount t) (G.output input)

theorem selectedSource_nonempty {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) : 0 < (selectedSource G input).1 :=
  cloneVertexCount_pos _ _ _

/-- Every lifted edge keeps the original ordered colour vector. -/
theorem selectedSource_yes {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (hyes : input ∈ G.L) :
    ∃ colour : Fin (selectedSource G input).1 → Fin (2 ^ t),
      ∀ k c, 2 ^ t - 1 ≤ colourFiberCard
        (fun j => colour ((selectedSource G input).2.2 k j)) c := by
  obtain ⟨colour, hbal⟩ := G.complete input hyes
  exact ⟨liftColour ⟨0, by positivity⟩ colour,
    clone_balanced ⟨0, by positivity⟩ colour (G.output input).2.2 hbal⟩

/-- Cloning preserves the NO promise at the *new* S=2^(2^t). -/
theorem selectedSource_no {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (hno : input ∉ G.L) :
    ∀ colour : Fin (selectedSource G input).1 → Fin (colourCount t),
      ∃ k c, ∀ j, colour ((selectedSource G input).2.2 k j) = c :=
  clone_no_proper_colouring (by simp [colourCount])
    (G.output input).2.2 (no_proper_colouring G input hno)

theorem selectedSource_sizes {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (selectedSource G input).1 =
      max 1 ((G.output input).1 *
        (2 ^ t * 2 ^ t * colourCount t)) ∧
    0 < (selectedSource G input).1 ∧
    (selectedSource G input).2.1 ≤ (G.output input).2.1 *
      (2 ^ t * 2 ^ t * colourCount t) ^ (2 ^ t * 2 ^ t) :=
  cloneSource_sizes t (colourCount t) (G.output input)

#print axioms no_proper_colouring
#print axioms selectedSource_yes
#print axioms selectedSource_no
#print axioms selectedSource_sizes

end CurrentAdditive.V38Source
