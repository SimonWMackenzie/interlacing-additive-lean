import EthInapproximability.CurrentPaper.ComplexityReductionClosure
import Paper2.FiniteSampling

/-!
# Unit 4 (Paper A), segment A4-S6: class lemmas independent of the D-A4 option

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `01-introduction.tex`, proof of `intro:corollary`
("... $\SAT\in\coRP\subseteq\coNP$ and $\NP=\coNP$").

D-A4 (the formal `BPP`/`coRP`/`coNP` definitions in the bit-machine model) is an author
decision. The statements below therefore quantify over an arbitrary class predicate
`C : BinaryLanguage → Prop` and take the machine-level closure facts that every option must
supply (`ReductionClosed C`, `ReductionClosed InNP`) as named hypotheses. `InCoNP` and
`NPEqCoNP` are DRAFT definitions over the banked `EncodedComplexity.InNP`. Banked production
lemmas are reused by exact name (`ComplexityReductionClosure.reduces_trans`).

**None of these statements closes a ledger row** (T02, U18, X06 stay open).
-/

namespace Paper2.Unit4Shell.ClassLemmas

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- DRAFT (D-A4 open): complement of an encoded NP language. -/
def InCoNP (L : BinaryLanguage) : Prop := InNP Lᶜ

/-- DRAFT (D-A4 open): `NP = coNP` over encoded binary languages. -/
def NPEqCoNP : Prop := ∀ L : BinaryLanguage, InNP L ↔ InCoNP L

/-- DRAFT: closure of a class under the banked polynomial-time many-one reductions. Every
D-A4 option for `BPP` must prove this for its own machine model (not proved here). -/
def ReductionClosed (C : BinaryLanguage → Prop) : Prop :=
  ∀ L K : BinaryLanguage, Reduces L K → C K → C L

/-- The same reduction reduces complements. Does not close a ledger row. -/
theorem reduces_compl {L K : BinaryLanguage} (h : Reduces L K) : Reduces Lᶜ Kᶜ := by
  obtain ⟨f, hf, hc⟩ := h
  exact ⟨f, hf, fun input => by simpa using not_congr (hc input)⟩

/-- `NP ⊆ C` for every reduction-closed class containing an NP-hard language (T02:
`SAT ∈ BPP ⇒ NP ⊆ BPP`, with `C := BPP` of the chosen option). Does not close a ledger row. -/
theorem np_subset_of_hard_mem (C : BinaryLanguage → Prop) (hC : ReductionClosed C)
    {K : BinaryLanguage} (hK : NPHard K) (hmem : C K) :
    ∀ L, InNP L → C L :=
  fun L hL => hC L K (hK L hL) hmem

/-- Reduction closure of `NP` transfers to `coNP`. Does not close a ledger row. -/
theorem coNP_closed_of_NP_closed (hNP : ReductionClosed InNP) : ReductionClosed InCoNP :=
  fun L K h hK => hNP Lᶜ Kᶜ (reduces_compl h) hK

/-- `NP = coNP` from an NP-hard language in `coNP` (T02 last step), given that `NP` is closed
under the banked reductions (a machine-level obligation of the bit-machine model, named here,
not proved). Does not close a ledger row. -/
theorem np_eq_coNP_of_hard_mem_coNP (hNP : ReductionClosed InNP)
    {K : BinaryLanguage} (hK : NPHard K) (hmem : InCoNP K) : NPEqCoNP := by
  have hsub : ∀ L, InNP L → InCoNP L :=
    np_subset_of_hard_mem InCoNP (coNP_closed_of_NP_closed hNP) hK hmem
  intro L
  constructor
  · exact hsub L
  · intro hL
    have h := hsub Lᶜ hL
    simpa [InCoNP, compl_compl] using h

/-- Minimal content shared by every one-sided (`coRP`-type) option: a fixed deterministic
polynomial-time rejection indicator on `pair input tape`, a polynomial tape-length bound,
members never rejected on any tape within the bound, and every non-member rejected on some
tape within the bound. DRAFT (D-A1/D-A4 open): a concrete option must still prove its own
machine has this normal form (e.g. accept inadmissible tapes, negate the output bit). -/
def OneSidedRejectShape (L : BinaryLanguage) : Prop :=
  ∃ reject : List Bool → Bool, BitMachine.Polytime (fun code => [reject code]) ∧
    ∃ c d : ℕ, ∀ input,
      (input ∈ L → ∀ tape : List Bool, tape.length ≤ c * (input.length + 1) ^ d →
        reject (pair input tape) = false) ∧
      (input ∉ L → ∃ tape : List Bool, tape.length ≤ c * (input.length + 1) ^ d ∧
        reject (pair input tape) = true)

/-- `coRP ⊆ coNP` in the option-generic normal form: the rejecting tape is the NP witness for
the complement. Does not close a ledger row. -/
theorem coNP_of_oneSided {L : BinaryLanguage} (h : OneSidedRejectShape L) : InCoNP L := by
  obtain ⟨reject, hpoly, c, d, hL⟩ := h
  refine ⟨reject, hpoly, c, d, fun input => ?_⟩
  constructor
  · intro hin
    exact (hL input).2 hin
  · rintro ⟨tape, hlen, hrej⟩ hmem
    have := (hL input).1 hmem tape hlen
    rw [this] at hrej
    exact Bool.false_ne_true hrej

/-- Positive probability under any finite law yields a witness: a non-member rejected with
probability `≥ 1/2` (any positive bound) has a rejecting tape. Does not close a ledger row. -/
theorem exists_of_prob_pos {α : Type*} [Fintype α] (μ : Paper2.FiniteLaw α) (E : α → Prop)
    (h : 0 < μ.prob E) : ∃ a, E a := by
  classical
  by_contra hne
  have hzero : μ.prob E = 0 := by
    unfold Paper2.FiniteLaw.prob
    apply Finset.sum_eq_zero
    intro a _
    have : ¬ E a := fun hE => hne ⟨a, hE⟩
    simp [this]
  linarith

/-- Membership in a class is preserved along an equality of languages (used to move from the
decider's accepted set to `EncodedCNF.Language`). Does not close a ledger row. -/
theorem mem_of_eq (C : BinaryLanguage → Prop) {L K : BinaryLanguage} (h : L = K) (hK : C K) :
    C L := h ▸ hK

end Paper2.Unit4Shell.ClassLemmas
