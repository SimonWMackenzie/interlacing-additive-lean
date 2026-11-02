import Paper2.YaoCloneMain
import Paper2.YaoX05Draft

/-! Unit 5 segment Y12 (lane a-yao-clone-owner-1): T26 `yao:source`
(lock v12 Y:77-90, YA:85-90, YA:113-116) stated HYP-parametrically in the
admitted DRAFT record `GLSourceDraft t` (X05 / AD-1, NOT adopted, never
instantiated; no statement here asserts that a record exists).

The composed machine is the admitted sequential composition of the record's
machine and the physical clone machine of `YaoCloneMain`; its output is the
Option B code of the admitted clone source of the record's occurrence output,
with `S = forbiddenColours t = 2^(2^t-1)`.  The YES / NO / nonempty clauses are
the admitted `draft_clone_source_yes/no/nonempty`.  DRAFT: depends on AD-1 and
D-A2 through the record's fields. -/

namespace Paper2.YaoT26Draft

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoCloneMachine
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec
open Paper2.YaoX05Draft
open Paper2.YaoLookup

/-- DRAFT (AD-1): the composed source machine. -/
noncomputable def sourceMachine {t : ℕ} (G : GLSourceDraft t) : BitMachine.Machine :=
  composition G.machine (cloneMachine (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t))

/-- DRAFT (AD-1): the composed public clock. -/
def sourceTime {t : ℕ} (G : GLSourceDraft t) (input : List Bool) : ℕ :=
  G.time input + 2 * (draftOccEncode (G.output input)).length + 2 +
    cloneTime (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) (G.output input).1
      (G.output input).1 (labelsOf (G.output input))

/-- T26 (`yao:source`), HYP-parametric in the DRAFT record `G`: one fixed
machine maps every input to the Option B code of a `K`-uniform source with
distinct vertices in each edge and a nonempty vertex set; a member gets a
balanced `2^t`-colouring (at least `2^t-1` of every colour in each edge); a
non-member has no proper `2^(2^t-1)`-colouring. -/
theorem draft_yao_source {t : ℕ} (G : GLSourceDraft t) (input : List Bool) :
    (sourceMachine G).OutputsWithin input
        (encode (cloneSource t (forbiddenColours t) (G.output input))) (sourceTime G input) ∧
      0 < (cloneSource t (forbiddenColours t) (G.output input)).1 ∧
      (input ∈ G.L →
        ∃ colour : Fin (cloneSource t (forbiddenColours t) (G.output input)).1 → Fin (2 ^ t),
          ∀ k c, 2 ^ t - 1 ≤ colourFiberCard
            (fun j => colour ((cloneSource t (forbiddenColours t) (G.output input)).2.2 k j)) c) ∧
      (input ∉ G.L →
        ∀ colour : Fin (cloneSource t (forbiddenColours t) (G.output input)).1 →
            Fin (forbiddenColours t),
          ∃ k c, ∀ j, colour ((cloneSource t (forbiddenColours t) (G.output input)).2.2 k j) = c) := by
  refine ⟨?_, draft_clone_source_nonempty G input, draft_clone_source_yes G input,
    draft_clone_source_no G input⟩
  exact composition_outputsWithin G.machine _ (G.runs input)
    (clone_source_outputsWithin t (forbiddenColours t) (G.output input))

#print axioms draft_yao_source

end Paper2.YaoT26Draft
