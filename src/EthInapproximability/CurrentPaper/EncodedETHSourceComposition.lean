import EthInapproximability.CurrentPaper.EncodedETHSource
import EthInapproximability.CurrentPaper.SourceBooleanThreeCNF

/-!
# The concrete finite source composition

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.

Only the three separately cited algorithms are inputs: IPZ sparsification,
Dinur's bounded-degree short PCP, and BOT's colouring reduction. The alphabet
encoding, prefix-OR clauses, clause-gap transfer, graph normalization, list
ordering, and numeric graph serialization below are our proved constructions.

This is the finite correctness and size layer. Although the three upstream
inputs expose actual machines, their intervening Boolean/normalization/list
machines are not supplied by this module. Accordingly it is not the complete
algorithmic source theorem or the ETH endpoint.
-/

namespace EthInapproximability.CurrentPaper.EncodedETHSourceComposition

open EncodedETHSource SourceCNFSemantics

noncomputable section

def booleanFormula (D : DinurReduction) (f : ValidFormula) : ValidFormula :=
  ⟨SourceBooleanEncoding.threeCNF (D.reduce f).system D.arity_pos,
    SourceBooleanEncoding.threeCNF_valid (D.reduce f).system D.arity_pos⟩

def booleanOccurrence (D : DinurReduction) : ℕ :=
  SourceBooleanEncoding.threeOccurrence D.alphabet D.arity D.degreeBound

def booleanRatio (D : DinurReduction) : ℕ :=
  SourceBooleanEncoding.variableRatio D.alphabet D.arity

def booleanGap (D : DinurReduction) : ℚ :=
  SourceBooleanEncoding.threeGap D.alphabet D.arity D.degreeBound D.gap

def booleanSizeFactor (D : DinurReduction) : ℕ :=
  SourceBooleanEncoding.threeSizeFactor D.alphabet D.arity

theorem boolean_occurrence (D : DinurReduction) (f : ValidFormula) :
    BoundedOccurrence (booleanFormula D f).val (booleanOccurrence D) :=
  SourceBooleanEncoding.threeCNF_occurrence (D.reduce f).system D.arity_pos
    D.degreeBound (D.degree f)

theorem boolean_ratio_pos (D : DinurReduction) : 0 < booleanRatio D :=
  SourceBooleanEncoding.variableRatio_pos

theorem boolean_variable_ratio (D : DinurReduction) (f : ValidFormula) :
    (booleanFormula D f).val.variables ≤
      booleanRatio D * (booleanFormula D f).val.clauses.length :=
  SourceBooleanEncoding.threeCNF_variable_ratio (D.reduce f).system
    D.alphabet_pos D.arity_pos (D.no_isolates f)

theorem boolean_gap_pos (D : DinurReduction) : 0 < booleanGap D :=
  SourceBooleanEncoding.threeGap_pos D.alphabet_pos D.gap_pos

theorem boolean_gap_le_one (D : DinurReduction) : booleanGap D ≤ 1 := by
  have hs : (1 : ℚ) ≤ SourceBooleanEncoding.sizeFactor D.alphabet D.arity := by
    exact_mod_cast SourceBooleanEncoding.sizeFactor_pos (q := D.arity) D.alphabet_pos
  have hd : (1 : ℚ) ≤ (D.degreeBound + 1 : ℚ) *
      SourceBooleanEncoding.sizeFactor D.alphabet D.arity := by
    nlinarith
  have h₁ := div_le_self D.gap_pos.le hd
  have h₂ := div_le_self
    (div_nonneg D.gap_pos.le (le_trans (by norm_num) hd))
    (show (1 : ℚ) ≤ 3 * SourceBooleanEncoding.width D.alphabet D.arity + 2 by
      have hw : (0 : ℚ) ≤ SourceBooleanEncoding.width D.alphabet D.arity := by positivity
      linarith)
  exact h₂.trans (h₁.trans D.gap_le_one)

theorem boolean_yes (D : DinurReduction) (f : ValidFormula)
    (h : EncodedCNF.Satisfiable f.val) : EncodedCNF.Satisfiable (booleanFormula D f).val :=
  SourceBooleanEncoding.threeCNF_complete (D.reduce f).system D.arity_pos (D.complete f h)

theorem boolean_no (D : DinurReduction) (f : ValidFormula)
    (h : ¬ EncodedCNF.Satisfiable f.val) :
    FormulaGap (booleanFormula D f).val (booleanGap D) ∧
      0 < (booleanFormula D f).val.clauses.length :=
  ⟨SourceBooleanEncoding.threeCNF_gap (D.reduce f).system D.alphabet_pos D.arity_pos
    D.degreeBound D.gap D.gap_pos.le (D.no_isolates f) (D.degree f) (D.sound f h),
   SourceBooleanEncoding.threeCNF_nonempty (D.reduce f).system
    D.alphabet_pos D.arity_pos (D.nonempty_no f h)⟩

theorem boolean_size (D : DinurReduction) (f : ValidFormula) :
    (booleanFormula D f).val.variables + (booleanFormula D f).val.clauses.length ≤
      booleanSizeFactor D * (D.reduce f).constraints :=
  SourceBooleanEncoding.threeCNF_size (D.reduce f).system D.arity_pos (D.no_isolates f)

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D))

def booleanBranches (f : ValidFormula) : List ValidFormula :=
  (S.branches f).map (booleanFormula D)

def sourceGraphs (f : ValidFormula) : List BOTReduction.ValidGraph :=
  B.graphList f.val.variables (booleanBranches S D f)

def sourceBits (f : ValidFormula) : List Bool :=
  B.graphListBits f.val.variables (booleanBranches S D f)

def sourceGap : ℚ := B.gapFraction (booleanRatio D) (booleanGap D) / 2

theorem source_gap_pos : 0 < sourceGap D B :=
  div_pos (B.gapFraction_pos (boolean_ratio_pos D) (boolean_gap_pos D)) (by norm_num)

theorem source_gap_le_one : sourceGap D B ≤ 1 := by
  have hV : (1 : ℚ) ≤ booleanRatio D := by exact_mod_cast boolean_ratio_pos D
  have hB : (1 : ℚ) ≤ B.sizeConstant := by exact_mod_cast B.sizeConstant_pos
  have hprod := mul_le_mul hV hB (by norm_num : (0 : ℚ) ≤ 1) (by linarith)
  have hden : (1 : ℚ) ≤ 8 * booleanRatio D * B.sizeConstant := by nlinarith
  have h₁ := div_le_self (boolean_gap_pos D).le hden
  have h₂ := div_le_self
    (div_nonneg (boolean_gap_pos D).le (le_trans (by norm_num) hden))
    (by norm_num : (1 : ℚ) ≤ 2)
  exact h₂.trans (h₁.trans (boolean_gap_le_one D))

theorem source_count (f : ValidFormula) :
    ((sourceGraphs S D B f).length : ℝ) ≤ (2 : ℝ) ^ ((η : ℝ) * f.val.variables) := by
  simpa only [sourceGraphs, BOTReduction.graphList_count, booleanBranches, List.length_map]
    using S.count f

theorem source_yes (f : ValidFormula) (h : EncodedCNF.Satisfiable f.val) :
    ∃ g ∈ sourceGraphs S D B f, (rawGraph g.val g.property).Colourable := by
  apply B.graphList_some_yes
  · intro g hg
    obtain ⟨f', _, rfl⟩ := List.mem_map.mp hg
    exact boolean_occurrence D f'
  · obtain ⟨f', hf', hs⟩ := S.some_yes f h
    exact ⟨booleanFormula D f', List.mem_map.mpr ⟨f', hf', rfl⟩, boolean_yes D f' hs⟩

theorem source_no (f : ValidFormula) (h : ¬ EncodedCNF.Satisfiable f.val) :
    ∀ g ∈ sourceGraphs S D B f, (rawGraph g.val g.property).Gap (sourceGap D B) := by
  apply B.graphList_every_no _ _ (boolean_ratio_pos D) (boolean_gap_pos D) (boolean_gap_le_one D)
  · intro g hg
    obtain ⟨f', _, rfl⟩ := List.mem_map.mp hg
    exact boolean_occurrence D f'
  · intro g hg
    obtain ⟨f', _, rfl⟩ := List.mem_map.mp hg
    exact boolean_variable_ratio D f'
  · intro g hg
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hg
    exact (boolean_no D f' (S.every_no f h f' hf')).2
  · intro g hg
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hg
    exact (boolean_no D f' (S.every_no f h f' hf')).1

/-- No malformed graph can occur even before a runtime implementation is
supplied: every output has the existing parser's exact roundtrip. -/
theorem source_graph_roundtrip (f : ValidFormula)
    (g : BOTReduction.ValidGraph) (_hg : g ∈ sourceGraphs S D B f) :
    EncodedGraph.decode (EncodedGraph.encode g.val) = some g.val :=
  EncodedGraph.decode_encode g.val g.property

theorem source_list_roundtrip (f : ValidFormula) :
    SourceListEncoding.decode (sourceBits S D B f) =
      some ((sourceGraphs S D B f).map fun g => EncodedGraph.encode g.val) :=
  B.graphList_roundtrip _ _

theorem source_geometry (f : ValidFormula) (g : BOTReduction.ValidGraph)
    (hg : g ∈ sourceGraphs S D B f) :
    f.val.variables ≤ g.val.edges.length ∧
      ∀ v, 1 ≤ (rawGraph g.val g.property).degree v ∧
        (rawGraph g.val g.property).degree v ≤ B.degreeBound := by
  obtain ⟨bf, hbf, rfl⟩ := List.mem_map.mp hg
  obtain ⟨f', _, rfl⟩ := List.mem_map.mp hbf
  exact ⟨(B.output_edge_bounds _ _ _).1,
    B.output_degree _ _ (boolean_occurrence D f') _⟩

theorem nat_size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.lt_size_self b).le)
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

theorem nat_size_add_one_le (a : ℕ) : (a + 1).size ≤ a.size + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h := Nat.lt_size_self a
  have hp : 0 < 2 ^ a.size := by positivity
  omega

theorem nat_size_le_self (a : ℕ) : a.size ≤ a :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Uniform bounds for the two input-length factors in Dinur's stated size
theorem. They use the actual sparse-branch codec, not a unit-cost clause list. -/
theorem sparse_code_factors (f g : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hg : g ∈ S.branches f) :
    (EncodedCNF.encode g.val).length + 1 ≤
      (8 * S.density + 4) * f.val.variables * (f.val.variables.size + 1) ∧
    ((EncodedCNF.encode g.val).length + 1).size + 1 ≤
      ((8 * S.density + 3).size + 5) * (f.val.variables.size + 1) := by
  let K := 8 * S.density + 3
  let n := f.val.variables
  let L := n.size + 1
  have he : (EncodedCNF.encode g.val).length ≤ K * n * L :=
    S.branch_encoded_length f hn g hg
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hnL : 1 ≤ n * L := le_trans hn (Nat.le_mul_of_pos_right n hL)
  constructor
  · change (EncodedCNF.encode g.val).length + 1 ≤ (K + 1) * n * L
    nlinarith
  · have hsize := Nat.size_le_size he
    have ha := nat_size_add_one_le (EncodedCNF.encode g.val).length
    have hm := nat_size_mul_le (K * n) L
    have hm' := nat_size_mul_le K n
    have hsmall := nat_size_le_self L
    change ((EncodedCNF.encode g.val).length + 1).size + 1 ≤ (K.size + 5) * L
    have hnsize : n.size + 1 = L := rfl
    nlinarith

def rawSizeConstant : ℕ :=
  B.sizeConstant * booleanSizeFactor D * D.sizeConstant * (8 * S.density + 4) *
    ((8 * S.density + 3).size + 5) ^ D.sizeExponent

/-- A uniform quasilinear bound for every raw BOT graph, prior to this
paper's normalization. Every source-dependent factor is now a fixed integer. -/
theorem raw_edge_size (f g : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hg : g ∈ S.branches f) :
    (B.reduce (booleanFormula D g).val).edges.length ≤
      rawSizeConstant S D B * f.val.variables *
        (f.val.variables.size + 1) ^ (D.sizeExponent + 1) := by
  have he := B.edges (booleanFormula D g).val (booleanFormula D g).property
    (boolean_occurrence D g)
  have hb := boolean_size D g
  have hd := D.size g
  have hlen := sparse_code_factors S f g hn hg
  have hc : (D.reduce g).constraints ≤
      D.sizeConstant * ((EncodedCNF.encode g.val).length + 1) *
        (((EncodedCNF.encode g.val).length + 1).size + 1) ^ D.sizeExponent :=
    le_trans (Nat.le_add_left _ _) hd
  have hp := Nat.mul_le_mul
    (Nat.mul_le_mul_left D.sizeConstant hlen.1)
    (Nat.pow_le_pow_left hlen.2 D.sizeExponent)
  have hv : (booleanFormula D g).val.variables ≤
      booleanSizeFactor D * (D.reduce g).constraints :=
    le_trans (Nat.le_add_right _ _) hb
  calc
    (B.reduce (booleanFormula D g).val).edges.length ≤
        B.sizeConstant * (booleanSizeFactor D * (D.reduce g).constraints) :=
      he.trans (Nat.mul_le_mul_left _ hv)
    _ ≤ B.sizeConstant * (booleanSizeFactor D *
        (D.sizeConstant * ((8 * S.density + 4) * f.val.variables *
          (f.val.variables.size + 1)) *
            (((8 * S.density + 3).size + 5) * (f.val.variables.size + 1)) ^
              D.sizeExponent)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hc.trans hp))
    _ = rawSizeConstant S D B * f.val.variables *
        (f.val.variables.size + 1) ^ (D.sizeExponent + 1) := by
      unfold rawSizeConstant
      rw [mul_pow, pow_succ]
      ring

def sourceSizeExponent : ℕ := D.sizeExponent + 1 + (rawSizeConstant S D B + 4)

theorem source_total_size (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : BOTReduction.ValidGraph) (hg : g ∈ sourceGraphs S D B f) :
    g.val.vertices + g.val.edges.length ≤
      f.val.variables * (f.val.variables.size + 1) ^ sourceSizeExponent S D B := by
  obtain ⟨bf, hbf, rfl⟩ := List.mem_map.mp hg
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hbf
  apply (B.output_total_size _ _ _).trans
  apply normalized_size_absorb _ _ (rawSizeConstant S D B) _ _ hn
  · have h : 0 < f.val.variables.size := Nat.size_pos.mpr (by omega)
    omega
  · exact raw_edge_size S D B f f' hn hf'

theorem source_bits_length (f : ValidFormula) (hn : 1 ≤ f.val.variables) :
    (sourceBits S D B f).length ≤ 3 * (S.branches f).length *
      (50 * (f.val.variables + rawSizeConstant S D B * f.val.variables *
        (f.val.variables.size + 1) ^ (D.sizeExponent + 1) + 1) ^ 2 + 1) + 1 := by
  have h := B.graphListBits_length f.val.variables
    (rawSizeConstant S D B * f.val.variables *
      (f.val.variables.size + 1) ^ (D.sizeExponent + 1)) (booleanBranches S D f) ?_
  · simpa only [sourceBits, booleanBranches, List.length_map] using h
  · intro bf hbf
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hbf
    exact raw_edge_size S D B f f' hn hf'

end

end EthInapproximability.CurrentPaper.EncodedETHSourceComposition
