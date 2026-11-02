import CurrentAdditive.V39CNFInNP
import CurrentAdditive.V39ApprovedYaoEndpoint

/-! Literal encoded CNF and the standard NP-hard promise-reduction form
for the approved actual strict-alternation compiler. The CNF verifier is
proved in the same finite-stack bit-machine model. The first helpers are
conditional on NP-hardness of the source record's arbitrary language.
ROOT_CONTRACT instead approves hardness of literal CNF: its final adapter
therefore specializes the source's D-A2 language field explicitly to literal
CNF, as selected by AUTHOR_DECISIONS_2026-09-27. The external record and that
specialization remain uninstantiated inputs; no record existence is proved.
-/

noncomputable section
set_option autoImplicit false

namespace CurrentAdditive.V39LiteralYaoNPJoin

open EthInapproximability.CurrentPaper
open EncodedCommunication EncodedComplexity
open Paper2.YaoX05Draft

/-- The target uses the existing canonical matrix/threshold encoding and
the existing Alice-first strict-alternation cost, with malformed words out. -/
def strictAliceLanguage : BinaryLanguage :=
  {word | ∃ i : Instance, decodeInstance word=some i ∧
    Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold}

theorem encoded_membership (i : Instance) (hi : i.Valid) :
    encodeInstance i ∈ strictAliceLanguage ↔
      Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold := by
  constructor
  · rintro ⟨j,hj,hcost⟩
    rw [decode_encode i hi] at hj
    cases Option.some.inj hj
    exact hcost
  · intro hcost
    exact ⟨i,decode_encode i hi,hcost⟩

/-- A genuine polynomial reduction into the approved source is composed
with its actual encoded matrix compiler, including its threshold. -/
theorem fixed_gap_of_reduces (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (L : BinaryLanguage) (hred : Reduces L G.L) :
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ L → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ L → (F input).threshold+k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  obtain ⟨f,hf,hcorrect⟩ := hred
  obtain ⟨F,hF,hvalid,hgap⟩ := V39ApprovedYaoEndpoint.fixed_gap_reduction k hk G
  refine ⟨fun input => F (f input),BitMachineComposition.polytime_comp hf hF,
    fun input => hvalid (f input),fun input => ?_⟩
  exact ⟨fun hin => (hgap (f input)).1 ((hcorrect input).mp hin),
    fun hout => (hgap (f input)).2 (fun hin => hout ((hcorrect input).mpr hin))⟩

/-- The NP-hardness promise is stated in the original bit-machine model:
every language in NP reduces to the same approved matrix compiler family. -/
theorem np_hard_fixed_gap_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hard : NPHard G.L) :
    ∀ L : BinaryLanguage, InNP L →
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ L → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ L → (F input).threshold+k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  intro L hL
  exact fixed_gap_of_reduces k hk G L (hard L hL)

/-- Unconditional literal-CNF membership discharges the complete input-side
NP premise. The two implications use one composed actual instance function. -/
theorem literal_cnf_fixed_gap_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hard : NPHard G.L) :
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ EncodedCNF.Language → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ EncodedCNF.Language → (F input).threshold+k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) :=
  fixed_gap_of_reduces k hk G EncodedCNF.Language
    (V39CNFInNP.literal_cnf_reduces_to_nphard G.L hard)

theorem fixed_gap_reduces_to_language (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (L : BinaryLanguage) (hred : Reduces L G.L) : Reduces L strictAliceLanguage := by
  obtain ⟨F,hF,hvalid,hgap⟩ := fixed_gap_of_reduces k hk G L hred
  refine ⟨fun input => encodeInstance (F input),hF,fun input => ?_⟩
  rw [encoded_membership _ (hvalid input)]
  constructor
  · exact (hgap input).1
  · intro hl
    by_contra hn
    have hh := (hgap input).2 hn
    omega

/-- A literal language-level NP-hardness conclusion. The witness compiler
is the same composed canonical instance compiler as the fixed-gap theorem. -/
theorem strict_alice_nphard (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hard : NPHard G.L) : NPHard strictAliceLanguage := by
  intro L hL
  exact fixed_gap_reduces_to_language k hk G L (hard L hL)

theorem literal_cnf_reduces_to_strict_alice (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hard : NPHard G.L) : Reduces EncodedCNF.Language strictAliceLanguage :=
  fixed_gap_reduces_to_language k hk G EncodedCNF.Language
    (V39CNFInNP.literal_cnf_reduces_to_nphard G.L hard)

/-- General alternative for an arbitrary source language. A reduction is
explicit here; the selected-CNF specialization below needs no such supplier. -/
theorem strict_alice_nphard_of_cnf_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hardCNF : NPHard EncodedCNF.Language)
    (cnfToSource : Reduces EncodedCNF.Language G.L) : NPHard strictAliceLanguage := by
  exact ComplexityReductionClosure.npHard_of_reduces hardCNF
    (fixed_gap_reduces_to_language k hk G EncodedCNF.Language cnfToSource)

theorem literal_cnf_gap_of_source_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (cnfToSource : Reduces EncodedCNF.Language G.L) :
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ EncodedCNF.Language → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ EncodedCNF.Language → (F input).threshold+k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) :=
  fixed_gap_of_reduces k hk G EncodedCNF.Language cnfToSource

/-- D-A2 fixes the source language to literal encoded CNF. This is the exact
same approved compiler; only its source-language propositions are rewritten.
The source record and its language specialization are not instantiated here. -/
theorem approved_cnf_fixed_gap_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hL : G.L=EncodedCNF.Language) :
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ EncodedCNF.Language → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ EncodedCNF.Language → (F input).threshold+k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  simpa only [hL] using V39ApprovedYaoEndpoint.fixed_gap_reduction k hk G

theorem approved_cnf_reduces_to_strict_alice (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hL : G.L=EncodedCNF.Language) : Reduces EncodedCNF.Language strictAliceLanguage :=
  fixed_gap_reduces_to_language k hk G EncodedCNF.Language
    (by simpa only [hL] using ComplexityReductionClosure.reduces_refl EncodedCNF.Language)

/-- The approved visible Cook--Levin hypothesis is transported along the
selected language equality; no NP-hardness of an arbitrary language is added. -/
theorem approved_cnf_strict_alice_nphard (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k))
    (hL : G.L=EncodedCNF.Language) (hardCNF : NPHard EncodedCNF.Language) :
    NPHard strictAliceLanguage :=
  strict_alice_nphard k hk G (by simpa only [hL] using hardCNF)

end CurrentAdditive.V39LiteralYaoNPJoin

#print axioms CurrentAdditive.V39LiteralYaoNPJoin.fixed_gap_of_reduces
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.np_hard_fixed_gap_reduction
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.literal_cnf_fixed_gap_reduction
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.strict_alice_nphard
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.literal_cnf_reduces_to_strict_alice
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.strict_alice_nphard_of_cnf_reduction
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.approved_cnf_fixed_gap_reduction
#print axioms CurrentAdditive.V39LiteralYaoNPJoin.approved_cnf_strict_alice_nphard
