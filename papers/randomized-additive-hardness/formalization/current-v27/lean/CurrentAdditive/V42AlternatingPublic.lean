import CurrentAdditive.V42AlternatingLookup
import CurrentAdditive.V39LiteralYaoNPJoin
import CurrentAdditive.V39PermittedOriginalDetYao

/-! V42 complete strictly alternating source-to-physical-printer trace.
New NO implications flow through V42.no_short_lookup_v42. The pre-existing
field arithmetic, actual source/array/table functions, physical machine clocks,
comparison extraction and four-convention midpoint law are retained exactly.
-/

noncomputable section
namespace CurrentAdditive.SmallBias.V42
open Classical
open Paper2.Yao Paper2.YaoLookup Paper2.YaoLowerBound Workspace.Types.Protocol
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.YaoMinimalSource
open CurrentAdditive.V38Encoded (edgeBits edgeCount_le_capacity)
open CurrentAdditive.V39SourceRenderer (sourceInstance selectedModulus sourceInstance_Dalt)
open CurrentAdditive.V38Source (colourCount)
open Paper2.YaoSourceCodec Paper2.YaoCloneSource
open CurrentAdditive.V39ActualYaoEndpoint
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39MinimalActualEndpoint (matrixWord midpointNumerator sourceWord sourceDecider)
open CurrentAdditive.V39PermittedNumericalExtraction (PermittedEstimator)
open CurrentAdditive.V39PermittedDeterministicExtraction (PermittedDeterministicEstimator)
open CurrentAdditive.V39PermittedYaoExtraction (RawAccurate extract_selected)
open CurrentAdditive.V39PermittedOriginalDetYao (DeterministicAccurate extract_deterministic_selected)
open CurrentAdditive.V39YaoEndpointJoin (estimatorParameter estimatorParameter_valid estimatorParameter_gap)
open Paper2 Paper2.YaoBppDraft Paper2.YaoX05Draft

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem concrete_matrix_yes_no
    {V E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t) : ℕ) : ℚ) /
      v38ArrayBiasQ b t ≤ (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    let W := v38PrintedPairWord b t d modulus
    let M := matrixV38 (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b)) W
    (∀ colour : V → Fin (2 ^ t),
      (∀ e c, 2 ^ t - 1 ≤
        colourFiberCard (fun i => colour (edges e i)) c) →
      Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
    ((∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c) →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Dalt .alice M) := by
  letI : Fintype (QuotientField d modulus) :=
    quotientFintype d modulus hmonic hdegree
  letI : CharP (QuotientField d modulus) 2 :=
    quotientCharP d modulus (Fact.out)
  have hbit (x y : Fin (2 ^ d))
      (j : Fin (2 ^ b * (2 ^ t * 2 ^ t))) :
      BitPrinter.bit d modulus x.val y.val j.val =
        vectorWord (fieldBasis d modulus hmonic hdegree)
          (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j :=
    printed_bit_eq_vectorWord d modulus _ hd hmodulus htop hmonic hdegree x y j
  have heq := v38PrintedPairWord_eq_fieldWord b t d modulus
    (fieldBasis d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hbit
  have hsource := v38PairFieldWord_hasPattern b t d
    (fieldBasis d modulus hmonic hdegree)
    (quotient_card d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hR
  have hpattern : HasPatternBound
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (v38PrintedPairWord b t d modulus)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) := by
    rw [heq]
    exact hsource
  constructor
  · intro colour hbalanced
    exact upper_bound_matrixV38 ht edges index _ _ colour hbalanced
  · intro hno
    exact lower_bound_complete_addresses ht edges index hno _ _ hpattern

theorem public_printed_matrix_yes_no
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (v38FieldDegree b t)
        (v38PositionCount b t) = some output ∧
      TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (v38FieldDegree b t)
        modulus (v38PositionCount b t) ∧
      (let M := matrixV38 (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (v38PrintedPairWord b t (v38FieldDegree b t) modulus)
       (∀ colour : V → Fin (2 ^ t),
         (∀ e c, 2 ^ t - 1 ≤
           colourFiberCard (fun i => colour (edges e i)) c) →
         Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
       ((∀ colour : V → Fin (2 ^ (2 ^ t)),
         ∃ e c, ∀ i, colour (edges e i) = c) →
         (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Dalt .alice M)) := by
  let d := v38FieldDegree b t
  obtain ⟨modulus, hfound⟩ :=
    TrialSearch.firstPassing_total d (v38FieldDegree_pos b t ht)
  have hirr := TrialSearch.firstPassing_correct (v38FieldDegree_pos b t ht) hfound
  obtain ⟨tail, htail, hcandidate⟩ := TrialSearch.firstPassing_is_candidate hfound
  have hlt : modulus < 2 ^ (d + 1) := by
    rw [hcandidate]
    exact monicBits_lt _ tail htail
  have htop : modulus.testBit d = true := by
    rw [hcandidate]
    exact monicBits_topBit _ tail htail
  have hmonic : (polynomial (d + 1) modulus).Monic := by
    rw [hcandidate]
    exact monicBits_monic _ tail htail
  have hdegree : (polynomial (d + 1) modulus).natDegree = d := by
    rw [hcandidate]
    exact monicBits_degree _ tail htail
  letI : Fact (Irreducible (polynomial (d + 1) modulus)) := ⟨hirr⟩
  obtain ⟨output, houtput⟩ := TrialSearch.makeList_total d
    (v38PositionCount b t) (v38FieldDegree_pos b t ht)
  have hout : output = StreamingPrinter.labelledWords d modulus
      (v38PositionCount b t) := by
    unfold TrialSearch.makeList at houtput
    simp only [hfound, Option.map_some, Option.some.injEq] at houtput
    exact houtput.symm
  refine ⟨output, modulus, houtput, hfound, hout, ?_⟩
  exact concrete_matrix_yes_no b t d modulus ht
    (v38FieldDegree_pos b t ht) hlt htop hmonic hdegree
    (by simpa only [v38PositionCount] using v38FieldDegree_bias b t)
    edges index

theorem selectedInstance_costs {t : ℕ} (G : SourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := selectedSource G input
    let b := edgeBits src.2.1
    let inst := sourceInstance src
    (input ∈ G.L →
      Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table) ≤
        2 * b + 4 * t + 2) ∧
    (input ∉ G.L →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤
        Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table)) := by
  dsimp only
  let src := selectedSource G input
  let b := edgeBits src.2.1
  let index := Fin.castLEEmb (edgeCount_le_capacity src.2.1)
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    public_printed_matrix_yes_no b t ht src.2.2 index
  have hm : selectedModulus b t = modulus := by
    simp only [selectedModulus, hmodulus, Option.getD_some]
  constructor
  · intro hy
    rw [sourceInstance_Dalt, CurrentAdditive.V38Executable.table_Dalt]
    change Dalt .alice (matrixV38 (placeEdges src.2.2 index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (v38PrintedPairWord b t (v38FieldDegree b t) (selectedModulus b t))) ≤ _
    rw [hm]
    obtain ⟨colour, hbal⟩ := selectedSource_yes G input hy
    exact hyes colour hbal
  · intro hn
    rw [sourceInstance_Dalt, CurrentAdditive.V38Executable.table_Dalt]
    change _ ≤ Dalt .alice (matrixV38 (placeEdges src.2.2 index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (v38PrintedPairWord b t (v38FieldDegree b t) (selectedModulus b t)))
    rw [hm]
    have hcol : ∀ colour : Fin src.1 → Fin (2 ^ (2 ^ t)),
        ∃ k c, ∀ j, colour (src.2.2 k j) = c :=
      selectedSource_no G input hn
    exact hno hcol

theorem selectedInstance_gap {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) (input : List Bool) :
    (input ∈ G.L → Dalt .alice (ProtocolVerifier.tableGame
      (V39MinimalActualEndpoint.selectedInstance G input).rows (V39MinimalActualEndpoint.selectedInstance G input).cols
      (V39MinimalActualEndpoint.selectedInstance G input).table) ≤ (V39MinimalActualEndpoint.selectedInstance G input).threshold) ∧
    (input ∉ G.L → (V39MinimalActualEndpoint.selectedInstance G input).threshold + (2 * t - 8) ≤
      Dalt .alice (ProtocolVerifier.tableGame
        (V39MinimalActualEndpoint.selectedInstance G input).rows (V39MinimalActualEndpoint.selectedInstance G input).cols
        (V39MinimalActualEndpoint.selectedInstance G input).table)) := by
  have h := selectedInstance_costs G input ht
  have hB := (V39SourceRenderer.sourceInstance_dimensions (selectedSource G input)).2.2
  constructor
  · intro hx
    rw [hB]
    exact h.1 hx
  · intro hx
    have hh : (V39MinimalActualEndpoint.selectedInstance G input).threshold + 2 * t - 8 ≤
        Dalt .alice (ProtocolVerifier.tableGame
          (V39MinimalActualEndpoint.selectedInstance G input).rows (V39MinimalActualEndpoint.selectedInstance G input).cols
          (V39MinimalActualEndpoint.selectedInstance G input).table) := by
      simpa only [hB] using h.2 hx
    omega


/-- The replacement source uses exactly the already implemented sourceInstance;
this identity covers all entries, dimensions, indexed labels and threshold. -/
theorem source_instance_same {t : ℕ} (G : SourceInput t) :
    (fun input => sourceInstance (selectedSource G input)) =
      V39MinimalActualEndpoint.selectedInstance G := rfl

/-- Actual full encoded table and threshold are printed by the unchanged
source/clone/field/table machine, under its complete original clock. -/
theorem source_table_outputs {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    (input : List Bool) :
    (V39ApprovedYaoCompiler.sourceTableMachine G).OutputsWithin input
      (encodeInstance (sourceInstance (selectedSource G input)))
      (V39ApprovedYaoCompiler.sourceTableTime G input) :=
  V39ApprovedYaoCompiler.sourceTable_outputs G ht input

theorem source_table_polytime {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) :
    BitMachine.Polytime (fun input => encodeInstance
      (sourceInstance (selectedSource G input))) :=
  V39ApprovedYaoCompiler.instanceWord_polytime G ht

/-- Both new-source cost implications and the exact physical run share one
fully specified output function. No old fixed-gap endpoint is called. -/
theorem source_table_run_and_gap {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    (input : List Bool) :
    (V39ApprovedYaoCompiler.sourceTableMachine G).OutputsWithin input
      (encodeInstance (sourceInstance (selectedSource G input)))
      (V39ApprovedYaoCompiler.sourceTableTime G input) ∧
    (input ∈ G.L → Dalt .alice (ProtocolVerifier.tableGame
      (sourceInstance (selectedSource G input)).rows
      (sourceInstance (selectedSource G input)).cols
      (sourceInstance (selectedSource G input)).table) ≤
      (sourceInstance (selectedSource G input)).threshold) ∧
    (input ∉ G.L → (sourceInstance (selectedSource G input)).threshold+(2*t-8) ≤
      Dalt .alice (ProtocolVerifier.tableGame
      (sourceInstance (selectedSource G input)).rows
      (sourceInstance (selectedSource G input)).cols
      (sourceInstance (selectedSource G input)).table)) :=
  ⟨source_table_outputs G ht input,selectedInstance_gap G ht input⟩

/-- The actual canonical F is specified, rather than hidden behind an
existential matrix family. Its NO side uses the newly proved V42 gap. -/
theorem fixed_gap_reduction (k : ℕ) (_hk : 1 ≤ k)
    (G : GLSourceDraft (v37GapParameter k)) :
    let F := fun input => sourceInstance (selectedSource (ofDraft G) input)
    BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ G.L → Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ G.L → (F input).threshold+k ≤ Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  dsimp only
  have ht := v37GapParameter_ge_four k
  refine ⟨source_table_polytime (ofDraft G) ht,
    YaoMinimalSource.selectedInstance_valid (ofDraft G),fun input => ?_⟩
  have h := selectedInstance_gap (ofDraft G) ht input
  have hk' := v37GapParameter_gap k
  exact ⟨h.1,fun hn => (Nat.add_le_add_left hk' _).trans (h.2 hn)⟩

/-- Literal encoded CNF is the approved external source language. The same
physical F and threshold are used on both truth values. -/
theorem literal_cnf_fixed_gap_reduction (k : ℕ) (hk : 1 ≤ k)
    (G : GLSourceDraft (v37GapParameter k)) (hL : G.L=EncodedCNF.Language) :
    let F := fun input => sourceInstance (selectedSource (ofDraft G) input)
    BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ EncodedCNF.Language → Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ EncodedCNF.Language → (F input).threshold+k ≤ Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  simpa only [hL] using fixed_gap_reduction k hk G

theorem sourceDecider_decides {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hp : BitMachine.Polytime (sourceWord G))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    (sourceDecider G E hp).Decides G.L (1 / 3) := by
  intro input
  have h := E.matrix_law hu (V39MinimalActualEndpoint.selectedInstance G input)
    (YaoMinimalSource.selectedInstance_valid G input)
    (V39MinimalActualEndpoint.selectedInstance G input).threshold (2 * t - 8) hgap (hcompare input)
  have hg := selectedInstance_gap G ht input
  constructor
  · intro hx
    have hh := h.1 (hg.1 hx)
    change 99 / 100 < E.algorithm.classifier.prob (sourceWord G input) (· = [true]) at hh
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith
  · intro hx
    have hh := h.2 (hg.2 hx)
    change E.algorithm.classifier.prob (sourceWord G input) (· = [true]) < 1 / 100 at hh
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith


/-- Actual unchanged sourceWord and estimator classifier; correctness now
consumes the new V42 proof of the same selected table's gap. -/
theorem source_decides {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2*(u+2) < ((2*t-8 : ℕ) : ℝ))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    SelectedTape.InBPP G.L := by
  have hk : 0 < 2*t-8 := by
    have h : (0 : ℝ) < ((2*t-8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  have hp := V39MinimalActualEndpoint.sourceWord_polytime_of_encoded G hk
    (source_table_polytime G ht)
  exact ⟨sourceDecider G E hp,sourceDecider_decides G ht E hu hgap hp hcompare⟩

theorem source_inP {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hz : E.algorithm.estimator.cR = 0)
    (hgap : 2*(u+2) < ((2*t-8 : ℕ) : ℝ))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    ComplexityReductionClosure.InP G.L := by
  have hk : 0 < 2*t-8 := by
    have h : (0 : ℝ) < ((2*t-8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  have hp := V39MinimalActualEndpoint.sourceWord_polytime_of_encoded G hk
    (source_table_polytime G ht)
  exact actual_inP_of_decides E.algorithm hz (sourceWord G) hp G.L
    (sourceDecider_decides G ht E hu hgap hp hcompare)

/-- Any of exactly four conventions dA,dB,dFree,yFree is covered by the
same actual-table midpoint comparison law. No old hardness endpoint is used. -/
theorem permitted_randomized_np_subset_bpp (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (A : PermittedEstimator) (haccuracy : RawAccurate A μ u) :
    ∀ L, InNP L → SelectedTape.InBPP L := by
  obtain ⟨E,hcompare,_⟩ := extract_selected A haccuracy (ofDraft G)
  exact SelectedTape.np_subset_inBPP hard
    (source_decides (ofDraft G) (estimatorParameter_valid u) E hu
      (estimatorParameter_gap u) hcompare)

theorem permitted_deterministic_p_equals_np (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (A : PermittedDeterministicEstimator)
    (haccuracy : DeterministicAccurate A μ u) : PEqualsNP := by
  obtain ⟨E,hcompare,hzero⟩ := extract_deterministic_selected A haccuracy (ofDraft G)
  exact p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard
      (source_inP (ofDraft G) (estimatorParameter_valid u) E hu hzero
        (estimatorParameter_gap u) hcompare))

theorem literal_cnf_permitted_randomized (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hL : G.L=EncodedCNF.Language)
    (hardCNF : NPHard EncodedCNF.Language)
    {μ : YaoMeasure} (A : PermittedEstimator) (haccuracy : RawAccurate A μ u) :
    ∀ L, InNP L → SelectedTape.InBPP L :=
  permitted_randomized_np_subset_bpp u hu G (by simpa only [hL] using hardCNF) A haccuracy

theorem literal_cnf_permitted_deterministic (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hL : G.L=EncodedCNF.Language)
    (hardCNF : NPHard EncodedCNF.Language)
    {μ : YaoMeasure} (A : PermittedDeterministicEstimator)
    (haccuracy : DeterministicAccurate A μ u) : PEqualsNP :=
  permitted_deterministic_p_equals_np u hu G (by simpa only [hL] using hardCNF) A haccuracy

#print axioms CurrentAdditive.SmallBias.V42.concrete_matrix_yes_no
#print axioms CurrentAdditive.SmallBias.V42.public_printed_matrix_yes_no
#print axioms CurrentAdditive.SmallBias.V42.selectedInstance_costs
#print axioms CurrentAdditive.SmallBias.V42.source_table_run_and_gap
#print axioms CurrentAdditive.SmallBias.V42.literal_cnf_fixed_gap_reduction
#print axioms CurrentAdditive.SmallBias.V42.literal_cnf_permitted_randomized
#print axioms CurrentAdditive.SmallBias.V42.literal_cnf_permitted_deterministic


/-- Actual printed pair labels satisfy the source's original-law pattern
bound at its exact accuracy; no table or coloring promise is needed. -/
theorem concrete_array_pattern
    (b t d modulus : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t) : ℕ) : ℚ) /
      v38ArrayBiasQ b t ≤ (2 ^ d : ℚ)) :
    HasPatternBound (Paper2.FiniteLaw.uniform (Fin ((2^d)^2)))
      (v38PrintedPairWord b t d modulus)
      ((1/2 : ℝ)^(4*(b+3*t))) := by
  letI : Fintype (QuotientField d modulus) :=
    quotientFintype d modulus hmonic hdegree
  letI : CharP (QuotientField d modulus) 2 :=
    quotientCharP d modulus (Fact.out)
  have hbit (x y : Fin (2 ^ d))
      (j : Fin (2 ^ b * (2 ^ t * 2 ^ t))) :
      BitPrinter.bit d modulus x.val y.val j.val =
        vectorWord (fieldBasis d modulus hmonic hdegree)
          (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j :=
    printed_bit_eq_vectorWord d modulus _ hd hmodulus htop hmonic hdegree x y j
  have heq := v38PrintedPairWord_eq_fieldWord b t d modulus
    (fieldBasis d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hbit
  have hsource := v38PairFieldWord_hasPattern b t d
    (fieldBasis d modulus hmonic hdegree)
    (quotient_card d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hR
  have hpattern : HasPatternBound
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (v38PrintedPairWord b t d modulus)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) := by
    rw [heq]
    exact hsource
  exact hpattern

/-- The selected executable field/list search returns precisely R² labelled
arrays with the source accuracy, retaining duplicate arrays as labels. -/
theorem public_array_pattern (b t : ℕ) (ht : 4 ≤ t) :
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (v38FieldDegree b t) (v38PositionCount b t) = some output ∧
      TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (v38FieldDegree b t)
        modulus (v38PositionCount b t) ∧
      HasPatternBound
        (Paper2.FiniteLaw.uniform (Fin ((2^(v38FieldDegree b t))^2)))
        (v38PrintedPairWord b t (v38FieldDegree b t) modulus)
        ((1/2 : ℝ)^(4*(b+3*t))) := by
  let d := v38FieldDegree b t
  obtain ⟨modulus,hfound⟩ := TrialSearch.firstPassing_total d (v38FieldDegree_pos b t ht)
  have hirr := TrialSearch.firstPassing_correct (v38FieldDegree_pos b t ht) hfound
  obtain ⟨tail,htail,hcandidate⟩ := TrialSearch.firstPassing_is_candidate hfound
  have hlt : modulus < 2^(d+1) := by
    rw [hcandidate]
    exact monicBits_lt _ tail htail
  have htop : modulus.testBit d = true := by
    rw [hcandidate]
    exact monicBits_topBit _ tail htail
  have hmonic : (polynomial (d+1) modulus).Monic := by
    rw [hcandidate]
    exact monicBits_monic _ tail htail
  have hdegree : (polynomial (d+1) modulus).natDegree = d := by
    rw [hcandidate]
    exact monicBits_degree _ tail htail
  letI : Fact (Irreducible (polynomial (d+1) modulus)) := ⟨hirr⟩
  obtain ⟨output,houtput⟩ := TrialSearch.makeList_total d (v38PositionCount b t)
    (v38FieldDegree_pos b t ht)
  have hout : output=StreamingPrinter.labelledWords d modulus (v38PositionCount b t) := by
    unfold TrialSearch.makeList at houtput
    simp only [hfound,Option.map_some,Option.some.injEq] at houtput
    exact houtput.symm
  refine ⟨output,modulus,houtput,hfound,hout,?_⟩
  exact concrete_array_pattern b t d modulus (v38FieldDegree_pos b t ht)
    hlt htop hmonic hdegree (by simpa only [v38PositionCount] using v38FieldDegree_bias b t)

/-- Field size and accuracy are chosen only from public b,t and satisfy
n*2^r ≤ R < 2*n*2^r, with n=H*K and r=4(b+3t). -/
theorem public_array_field_bounds (b t : ℕ) (ht : 4 ≤ t) :
    v38PositionCount b t * 2^(4*(b+3*t)) ≤ 2^(v38FieldDegree b t) ∧
    2^(v38FieldDegree b t) < 2*(v38PositionCount b t * 2^(4*(b+3*t))) :=
  ⟨v38FieldDegree_lower b t,v38FieldDegree_upper b t ht⟩

#print axioms CurrentAdditive.SmallBias.V42.concrete_array_pattern
#print axioms CurrentAdditive.SmallBias.V42.public_array_pattern
#print axioms CurrentAdditive.SmallBias.V42.public_array_field_bounds

/-- Every seed label is kept and its printed word has exactly the genuine
H*K positions; equal decoded arrays are not collapsed. -/
theorem public_array_label_shape (b t modulus : ℕ) :
    (StreamingPrinter.labelledWords (v38FieldDegree b t) modulus
      (v38PositionCount b t)).length = (2^(v38FieldDegree b t))^2 ∧
    (∀ x y : ℕ, (StreamingPrinter.word (v38FieldDegree b t) modulus
      (v38PositionCount b t) x y).length = v38PositionCount b t) := by
  exact ⟨StreamingPrinter.labelledWords_length _ _ _,
    fun x y => StreamingPrinter.word_length _ _ _ x y⟩

/-- The unchanged physical source/table clock is a polynomial in the
original input length for fixed t, and is the clock in source_table_outputs. -/
theorem source_table_time_polynomial {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) :
    ∃ c d : ℕ, ∀ input, V39ApprovedYaoCompiler.sourceTableTime G input ≤
      c*(input.length+1)^d :=
  V39ApprovedYaoCompiler.sourceTableTime_poly G ht

#print axioms CurrentAdditive.SmallBias.V42.public_array_label_shape
#print axioms CurrentAdditive.SmallBias.V42.source_table_time_polynomial

end CurrentAdditive.SmallBias.V42
end
