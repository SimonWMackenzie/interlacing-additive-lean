import EthInapproximability.CurrentPaper.SourceCNFSemantics
import EthInapproximability.CurrentPaper.SourceNormalization
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.SourceListEncoding
import EthInapproximability.CurrentPaper.SourceCSPCodec

/-!
# Source composition for the ETH reduction

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.

The BOT input below is a separately stated cited reduction, on actual bounded-
occurrence OR-3CNF formulas. It is not the paper's composed graph-source theorem.
In particular the exact-one blocks mentioned in the manuscript encode alphabet
variables; they do not change the semantics of the final OR clauses to 1-in-3.

This module proves the paper's damaged-clause arithmetic and the literal graph
normalization/serialization steps. The Boolean encoding of Dinur constraints,
list traversal by a finite machine, and the normalization machine are separate
internal obligations. No running-time theorem for that unfinished composition
is asserted here.
-/

namespace EthInapproximability.CurrentPaper.EncodedETHSource

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open SourceNormalization EncodedCNF SourceCNFSemantics

set_option maxHeartbeats 500000
set_option maxRecDepth 20000

-- Match the generic support enumeration used by `SourceNormalization`.
-- This local instance changes no imported or exported instance registration.
local instance (n : ℕ) (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  Fintype.decidableExistsFintype

noncomputable section

abbrev ValidFormula := {f : Formula // f.Valid}

def formulaListBits (fs : List ValidFormula) : List Bool :=
  SourceListEncoding.encode (fs.map fun f => EncodedCNF.encode f.val)

def sparsificationBits (branches : ValidFormula → List ValidFormula)
    (input : List Bool) : List Bool :=
  match h : EncodedCNF.decode input with
  | none => []
  | some f => formulaListBits (branches ⟨f, EncodedCNF.decode_valid h⟩)

/-- The algorithmic IPZ theorem, stated on the actual CNF codec and the
actual finite Boolean-stack machine. No graph, PCP, or normalized-source
conclusion is part of this external input. Constants may depend on `η`.

The declared variable count may decrease on a branch, but all size and count
bounds are measured against the original formula. -/
structure Sparsification (η : ℚ) where
  branches : ValidFormula → List ValidFormula
  density : ℕ
  density_pos : 1 ≤ density
  variableBound : ∀ f, ∀ g ∈ branches f, g.val.variables ≤ f.val.variables
  clauses : ∀ f, ∀ g ∈ branches f, g.val.clauses.length ≤ density * f.val.variables
  count : ∀ f, ((branches f).length : ℝ) ≤ (2 : ℝ) ^ ((η : ℝ) * f.val.variables)
  satisfiable : ∀ f, Satisfiable f.val ↔ ∃ g ∈ branches f, Satisfiable g.val
  machine : BitMachine.Machine
  timeConstant : ℕ
  timeExponent : ℕ
  runtime : ∀ input, machine.OutputsWithin input (sparsificationBits branches input)
    (timeConstant *
      ⌈(2 : ℝ) ^ ((η : ℝ) *
        (match EncodedCNF.decode input with | none => 0 | some f => f.variables))⌉₊ *
      (input.length + 1) ^ timeExponent)

namespace Sparsification

variable {η : ℚ} (S : Sparsification η)

theorem clause_length_log (c : Clause) {n : ℕ} (h : c.Valid n) :
    (EncodedCNF.encodeClause c).length ≤ 6 * n.size + 6 := by
  have h₁ := Nat.size_le_size (Nat.le_of_lt h.1)
  have h₂ := Nat.size_le_size (Nat.le_of_lt h.2.1)
  have h₃ := Nat.size_le_size (Nat.le_of_lt h.2.2)
  simp only [EncodedCNF.encodeClause, List.length_append, EncodedCNF.encodeLiteral_length,
    Nat.size_eq_bits_len]
  omega

theorem clauseFields_length_log (n : ℕ) (cs : List Clause)
    (h : ∀ c ∈ cs, c.Valid n) :
    (EncodedCNF.clauseFields cs).length ≤ cs.length * (6 * n.size + 6) := by
  induction cs with
  | nil => simp [EncodedCNF.clauseFields]
  | cons c cs ih =>
      have hc := clause_length_log c (h c (by simp))
      have ht := ih (fun d hd => h d (by simp [hd]))
      simp only [EncodedCNF.clauseFields, List.length_append, List.length_cons]
      nlinarith

theorem formula_length_log (f : Formula) (hf : f.Valid) :
    (EncodedCNF.encode f).length ≤
      f.variables + 2 + f.clauses.length * (6 * f.variables.size + 8) := by
  have hc := clauseFields_length_log f.variables f.clauses hf
  have hh := EncodedGraph.natField_length_upper f.clauses.length
  simp only [EncodedCNF.encode, EncodedGraph.unary, List.length_append,
    List.length_replicate, List.length_singleton]
  nlinarith

theorem some_yes (f : ValidFormula) (h : Satisfiable f.val) :
    ∃ g ∈ S.branches f, Satisfiable g.val := (S.satisfiable f).mp h

theorem every_no (f : ValidFormula) (h : ¬ Satisfiable f.val) :
    ∀ g ∈ S.branches f, ¬ Satisfiable g.val := by
  intro g hg hyes
  exact h ((S.satisfiable f).mpr ⟨g, hg, hyes⟩)

theorem branch_size (f : ValidFormula) (g : ValidFormula) (hg : g ∈ S.branches f) :
    g.val.variables + g.val.clauses.length ≤ (S.density + 1) * f.val.variables := by
  have hv := S.variableBound f g hg
  have hc := S.clauses f g hg
  nlinarith

/-- This is the required near-linear *binary* length of each sparse branch.
`Nat.size n` is the bit length of `n`, so the overhead is logarithmic. -/
theorem branch_encoded_length (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (EncodedCNF.encode g.val).length ≤
      (8 * S.density + 3) * f.val.variables * (f.val.variables.size + 1) := by
  have he := formula_length_log g.val g.property
  have hv := S.variableBound f g hg
  have hc := S.clauses f g hg
  have hs := Nat.size_le_size hv
  have hp := Nat.mul_le_mul hc
    (show 6 * g.val.variables.size + 8 ≤ 8 * (f.val.variables.size + 1) by omega)
  nlinarith

theorem rejects_malformed {input : List Bool} (h : EncodedCNF.decode input = none) :
    sparsificationBits S.branches input = [] := by
  unfold sparsificationBits
  split
  · rfl
  · rename_i f hf
    simp [h] at hf

end Sparsification

/-- The short bounded-degree PCP construction is a separate cited input.
Its output is the actual constant-alphabet constraint system, before our
Boolean encoding and before BOT. The quasilinear bound is in encoded input
length. Positivity is required in the NO case, so a zero-constraint output
cannot fake soundness through a vacuous fractional inequality. -/
structure DinurReduction where
  alphabet : ℕ
  alphabet_pos : 0 < alphabet
  arity : ℕ
  arity_pos : 0 < arity
  degreeBound : ℕ
  degreeBound_pos : 0 < degreeBound
  gap : ℚ
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  sizeConstant : ℕ
  sizeConstant_pos : 0 < sizeConstant
  sizeExponent : ℕ
  reduce : ValidFormula → ConstraintInstance alphabet arity
  degree : ∀ f, SourceBooleanEncoding.BoundedOccurrence (reduce f).system degreeBound
  no_isolates : ∀ f, (reduce f).vertices ≤ arity * (reduce f).constraints
  complete : ∀ f, EncodedCNF.Satisfiable f.val →
    SourceBooleanEncoding.Satisfiable (reduce f).system
  sound : ∀ f, ¬ EncodedCNF.Satisfiable f.val →
    SourceBooleanEncoding.Gap (reduce f).system gap
  nonempty_no : ∀ f, ¬ EncodedCNF.Satisfiable f.val → 0 < (reduce f).constraints
  size : ∀ f, (reduce f).vertices + (reduce f).constraints ≤
    sizeConstant * ((EncodedCNF.encode f.val).length + 1) *
      (((EncodedCNF.encode f.val).length + 1).size + 1) ^ sizeExponent
  bitFunction : List Bool → List Bool
  bitFunction_valid : ∀ f, bitFunction (EncodedCNF.encode f.val) = constraintBits (reduce f)
  bitFunction_malformed : ∀ input, EncodedCNF.decode input = none → bitFunction input = []
  polytime : BitMachine.Polytime bitFunction

namespace DinurReduction

/-- This is the list quantifier order of the paper, at the intermediate PCP
stage. The Boolean/graph stages are still not hidden inside either input. -/
theorem some_yes_every_no {η : ℚ} (S : Sparsification η) (D : DinurReduction)
    (f : ValidFormula) :
    (EncodedCNF.Satisfiable f.val → ∃ g ∈ S.branches f,
      SourceBooleanEncoding.Satisfiable (D.reduce g).system) ∧
    (¬ EncodedCNF.Satisfiable f.val → ∀ g ∈ S.branches f,
      SourceBooleanEncoding.Gap (D.reduce g).system D.gap ∧
        0 < (D.reduce g).constraints) := by
  constructor
  · intro hyes
    obtain ⟨g, hg, hs⟩ := S.some_yes f hyes
    exact ⟨g, hg, D.complete g hs⟩
  · intro hno g hg
    exact ⟨D.sound g (S.every_no f hno g hg), D.nonempty_no g (S.every_no f hno g hg)⟩

end DinurReduction

/-- Preserve ordered edge occurrences, including parallel edges. -/
def rawGraph (g : EncodedGraph.Graph) (hg : g.Valid) :
    RawGraph (Fin g.vertices) (Fin g.edges.length) where
  orderV := inferInstance
  orderE := inferInstance
  bd₀ := fun e => EncodedGraph.endpoints g hg e 0
  bd₁ := fun e => EncodedGraph.endpoints g hg e 1
  loopless := fun e h => by
    have := EncodedGraph.endpoints_injective g hg e h
    exact (by decide : (0 : Fin 2) ≠ 1) this

theorem rawGraph_bd (g : EncodedGraph.Graph) (hg : g.Valid)
    (e : Fin g.edges.length) (b : Fin 2) :
    (rawGraph g hg).bd e b = EncodedGraph.endpoints g hg e b := by
  fin_cases b <;> simp [rawGraph, RawGraph.bd]

/-- Public numeric labels follow the graph's two specified linear orders. -/
def serializeGraph {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) : EncodedGraph.Graph :=
  ⟨Fintype.card V, endpointList G⟩

theorem serializeGraph_valid {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    (serializeGraph G).Valid := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  refine ⟨(endpointPair G i).1.isLt, (endpointPair G i).2.isLt, ?_⟩
  intro h
  exact endpointPair_loopless G i (Fin.ext h)

@[simp] theorem serializeGraph_vertices {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    (serializeGraph G).vertices = Fintype.card V := rfl

@[simp] theorem serializeGraph_edges {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    (serializeGraph G).edges.length = Fintype.card E := endpointList_length G

theorem serializeGraph_roundtrip {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    EncodedGraph.decode (EncodedGraph.encode (serializeGraph G)) =
      some (serializeGraph G) :=
  EncodedGraph.decode_encode _ (serializeGraph_valid G)

def serializedEdgeEquiv {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    Fin (serializeGraph G).edges.length ≃ E :=
  (finCongr (serializeGraph_edges G)).trans (edgeEnumeration G)

theorem serialized_endpoint {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E)
    (i : Fin (serializeGraph G).edges.length) (b : Fin 2) :
    vertexEnumeration G (EncodedGraph.endpoints (serializeGraph G) (serializeGraph_valid G) i b) =
      G.bd (serializedEdgeEquiv G i) b := by
  fin_cases b <;>
    simp [EncodedGraph.endpoints, serializeGraph, endpointList, endpointPair,
      serializedEdgeEquiv, EndpointGraph.bd, List.get_eq_getElem] <;> rfl

theorem serialized_colourable_iff {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) :
    (rawGraph (serializeGraph G) (serializeGraph_valid G)).Colourable ↔ G.SourceYES := by
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨fun v => χ ((vertexEnumeration G).symm v), ?_⟩
    intro e he
    let i := (serializedEdgeEquiv G).symm e
    apply hχ i
    have h₀ := serialized_endpoint G i 0
    have h₁ := serialized_endpoint G i 1
    simp only [i, Equiv.apply_symm_apply] at h₀ h₁
    have h₀' := congrArg (vertexEnumeration G).symm h₀
    have h₁' := congrArg (vertexEnumeration G).symm h₁
    simpa only [Equiv.symm_apply_apply, ← h₀', ← h₁'] using he
  · rintro ⟨χ, hχ⟩
    refine ⟨fun v => χ (vertexEnumeration G v), ?_⟩
    intro i he
    apply hχ (serializedEdgeEquiv G i)
    simpa only [rawGraph, serialized_endpoint] using he

theorem serialized_mono_card {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E)
    (χ : Fin (serializeGraph G).vertices → Fin 3) :
    ((rawGraph (serializeGraph G) (serializeGraph_valid G)).monoFinset χ).card =
      (G.monoFinset (fun v => χ ((vertexEnumeration G).symm v))).card := by
  have hiff (i : Fin (serializeGraph G).edges.length) :
      i ∈ (rawGraph (serializeGraph G) (serializeGraph_valid G)).monoFinset χ ↔
      serializedEdgeEquiv G i ∈ G.monoFinset (fun v => χ ((vertexEnumeration G).symm v)) := by
    simp only [RawGraph.monoFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      EndpointGraph.mem_monoFinset]
    change χ (EncodedGraph.endpoints (serializeGraph G) (serializeGraph_valid G) i 0) =
      χ (EncodedGraph.endpoints (serializeGraph G) (serializeGraph_valid G) i 1) ↔ _
    rw [← serialized_endpoint G i 0, ← serialized_endpoint G i 1]
    simp only [Equiv.symm_apply_apply]
  apply Finset.card_bij (fun i _ => serializedEdgeEquiv G i)
  · exact fun i hi => (hiff i).mp hi
  · exact fun i _ j _ h => (serializedEdgeEquiv G).injective h
  · intro e he
    refine ⟨(serializedEdgeEquiv G).symm e, ?_, Equiv.apply_symm_apply _ _⟩
    apply (hiff _).mpr
    simpa only [Equiv.apply_symm_apply] using he

theorem serialized_gap {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) {γ : ℚ}
    (h : G.SourceNO γ) :
    (rawGraph (serializeGraph G) (serializeGraph_valid G)).Gap γ := by
  intro χ
  have hc := h (fun v => χ ((vertexEnumeration G).symm v))
  rw [← serialized_mono_card G χ] at hc
  simpa only [Fintype.card_fin, serializeGraph_edges] using hc

theorem serialized_degree {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E)
    (v : Fin (serializeGraph G).vertices) :
    (rawGraph (serializeGraph G) (serializeGraph_valid G)).degree v =
      G.degree (vertexEnumeration G v) := by
  let e := Equiv.prodCongr (serializedEdgeEquiv G) (Equiv.refl (Fin 2))
  have hiff (p : Fin (serializeGraph G).edges.length × Fin 2) :
      (rawGraph (serializeGraph G) (serializeGraph_valid G)).bd p.1 p.2 = v ↔
      G.vert (e p) = vertexEnumeration G v := by
    rw [rawGraph_bd]
    change EncodedGraph.endpoints (serializeGraph G) (serializeGraph_valid G) p.1 p.2 = v ↔
      G.bd (serializedEdgeEquiv G p.1) p.2 = vertexEnumeration G v
    rw [← serialized_endpoint G p.1 p.2]
    exact (vertexEnumeration G).injective.eq_iff.symm
  unfold RawGraph.degree EndpointGraph.degree EndpointGraph.incFinset
  apply Finset.card_bij (fun p _ => e p)
  · intro p hp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hiff p).mp (Finset.mem_filter.mp hp).2
  · exact fun p _ q _ h => e.injective h
  · intro p hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (hiff _).mpr ?_⟩
    simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hp).2

/-- Exactly the primitive global counting input used from BOT Theorem 14.
For a sufficiently small set of monochromatic edges the construction's
rounding loses at most eight clauses per deleted edge. The fixed constants
may depend on the input occurrence bound, but not on the input formula.

The separate `polytime` field refers to the actual all-input bit-string map.
It is an upstream input, not a claim that our normalization is polynomial. -/
structure BOTReduction (k : ℕ) where
  reduce : Formula → EncodedGraph.Graph
  valid : ∀ f, f.Valid → (reduce f).Valid
  degreeBound : ℕ
  degreeBound_pos : 1 ≤ degreeBound
  sizeConstant : ℕ
  sizeConstant_pos : 1 ≤ sizeConstant
  degree : ∀ f (hf : f.Valid), BoundedOccurrence f k →
    ∀ v, (rawGraph (reduce f) (valid f hf)).degree v ≤ degreeBound
  edges : ∀ f, f.Valid → BoundedOccurrence f k →
    (reduce f).edges.length ≤ sizeConstant * f.variables
  complete : ∀ f (hf : f.Valid), BoundedOccurrence f k → Satisfiable f →
    (rawGraph (reduce f) (valid f hf)).Colourable
  round : ∀ f (hf : f.Valid), BoundedOccurrence f k →
    ∀ χ : Fin (reduce f).vertices → Fin 3,
      8 * ((rawGraph (reduce f) (valid f hf)).monoFinset χ).card < f.clauses.length →
      ∃ assignment : List Bool, assignment.length = f.variables ∧
        (falseClauses f assignment).card ≤
          8 * ((rawGraph (reduce f) (valid f hf)).monoFinset χ).card
  bitFunction : List Bool → List Bool
  bitFunction_valid : ∀ f, f.Valid →
    bitFunction (EncodedCNF.encode f) = EncodedGraph.encode (reduce f)
  bitFunction_malformed : ∀ input, EncodedCNF.decode input = none → bitFunction input = []
  polytime : BitMachine.Polytime bitFunction

namespace BOTReduction

variable {k : ℕ} (B : BOTReduction k)

/-- The clause-loss input gives an absolute lower bound even when the
colouring has too many bad edges for the rounding lemma's small-loss regime. -/
theorem monochromatic_lower (f : Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k) {ρ : ℚ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hgap : FormulaGap f ρ) (χ : Fin (B.reduce f).vertices → Fin 3) :
    ρ * f.clauses.length ≤
      8 * (((rawGraph (B.reduce f) (B.valid f hf)).monoFinset χ).card : ℚ) := by
  by_cases hsmall : 8 * ((rawGraph (B.reduce f) (B.valid f hf)).monoFinset χ).card <
      f.clauses.length
  · obtain ⟨assignment, hlen, hbad⟩ := B.round f hf hk χ hsmall
    have h := hgap assignment hlen
    exact h.trans (by exact_mod_cast hbad)
  · have hlarge : (f.clauses.length : ℚ) ≤
        8 * (((rawGraph (B.reduce f) (B.valid f hf)).monoFinset χ).card : ℚ) := by
      exact_mod_cast (Nat.le_of_not_gt hsmall)
    exact (mul_le_of_le_one_left (by positivity) hρ1).trans hlarge

def gapFraction (variableRatio : ℕ) (ρ : ℚ) : ℚ :=
  ρ / (8 * variableRatio * B.sizeConstant)

theorem gapFraction_pos {V : ℕ} (hV : 0 < V) {ρ : ℚ} (hρ : 0 < ρ) :
    0 < B.gapFraction V ρ := by
  have hB : (0 : ℚ) < B.sizeConstant := by exact_mod_cast B.sizeConstant_pos
  have hVQ : (0 : ℚ) < V := by exact_mod_cast hV
  exact div_pos hρ (by positivity)

theorem graph_gap (f : Formula) (hf : f.Valid) (hk : BoundedOccurrence f k)
    {V : ℕ} (hV : 0 < V) (hused : f.variables ≤ V * f.clauses.length)
    {ρ : ℚ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hgap : FormulaGap f ρ) :
    (rawGraph (B.reduce f) (B.valid f hf)).Gap (B.gapFraction V ρ) := by
  intro χ
  have hM := B.monochromatic_lower f hf hk hρ hρ1 hgap χ
  have he : ((B.reduce f).edges.length : ℚ) ≤
      V * B.sizeConstant * f.clauses.length := by
    have h := le_trans (B.edges f hf hk) (Nat.mul_le_mul_left B.sizeConstant hused)
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_left_comm] using h)
  have hB : (0 : ℚ) < B.sizeConstant := by exact_mod_cast B.sizeConstant_pos
  have hVQ : (0 : ℚ) < V := by exact_mod_cast hV
  simp only [Fintype.card_fin]
  rw [gapFraction, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h₁ := mul_le_mul_of_nonneg_left he hρ
  have h₂ := mul_le_mul_of_nonneg_left hM (show (0 : ℚ) ≤ V * B.sizeConstant by positivity)
  nlinarith only [h₁, h₂]

theorem graph_not_colourable (f : Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k) (hm : 0 < f.clauses.length)
    {ρ : ℚ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hgap : FormulaGap f ρ) :
    ¬ (rawGraph (B.reduce f) (B.valid f hf)).Colourable := by
  rintro ⟨χ, hχ⟩
  have hzero : (rawGraph (B.reduce f) (B.valid f hf)).monoFinset χ = ∅ := by
    ext e
    simp [RawGraph.monoFinset, hχ e]
  have h := B.monochromatic_lower f hf hk hρ.le hρ1 hgap χ
  rw [hzero] at h
  have hmQ : (0 : ℚ) < f.clauses.length := by exact_mod_cast hm
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h
  exact (not_le_of_gt (mul_pos hρ hmQ)) h

def normalized (f : Formula) (hf : f.Valid) (n : ℕ) :=
  (rawGraph (B.reduce f) (B.valid f hf)).normalize n

def output (f : Formula) (hf : f.Valid) (n : ℕ) : EncodedGraph.Graph :=
  serializeGraph (B.normalized f hf n)

theorem output_valid (f : Formula) (hf : f.Valid) (n : ℕ) :
    (B.output f hf n).Valid := serializeGraph_valid _

theorem output_degree (f : Formula) (hf : f.Valid) (hk : BoundedOccurrence f k)
    (n : ℕ) (v : Fin (B.output f hf n).vertices) :
    1 ≤ (rawGraph (B.output f hf n) (B.output_valid f hf n)).degree v ∧
      (rawGraph (B.output f hf n) (B.output_valid f hf n)).degree v ≤ B.degreeBound := by
  change 1 ≤ (rawGraph (serializeGraph (B.normalized f hf n))
    (serializeGraph_valid (B.normalized f hf n))).degree v ∧
      (rawGraph (serializeGraph (B.normalized f hf n))
        (serializeGraph_valid (B.normalized f hf n))).degree v ≤ B.degreeBound
  rw [serialized_degree]
  exact ⟨RawGraph.normalized_no_isolates _ n _,
    RawGraph.normalized_degree_bound _ n B.degreeBound_pos (B.degree f hf hk) _⟩

theorem normalized_common (f : Formula) (hf : f.Valid) (hk : BoundedOccurrence f k)
    (n : ℕ) (γ : ℚ) : (B.normalized f hf n).SourceCommon γ B.degreeBound := by
  exact ⟨RawGraph.normalized_vertex_bound _ n, fun v =>
    ⟨RawGraph.normalized_no_isolates _ n v,
      RawGraph.normalized_degree_bound _ n B.degreeBound_pos (B.degree f hf hk) v⟩⟩

theorem normalized_yes (f : Formula) (hf : f.Valid) (hk : BoundedOccurrence f k)
    (n : ℕ) (hyes : Satisfiable f) : (B.normalized f hf n).SourceYES :=
  RawGraph.normalized_colourable _ n (B.complete f hf hk hyes)

theorem normalized_no (f : Formula) (hf : f.Valid) (hk : BoundedOccurrence f k)
    {V : ℕ} (hV : 0 < V) (hused : f.variables ≤ V * f.clauses.length)
    (hm : 0 < f.clauses.length)
    (n : ℕ) {ρ : ℚ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hgap : FormulaGap f ρ) :
    (B.normalized f hf n).SourceNO (B.gapFraction V ρ / 2) :=
  RawGraph.normalized_gap _ n (B.gapFraction_pos hV hρ).le
    (B.graph_not_colourable f hf hk hm hρ hρ1 hgap)
    (B.graph_gap f hf hk hV hused hρ.le hρ1 hgap)

theorem output_edge_bounds (f : Formula) (hf : f.Valid) (n : ℕ) :
    n ≤ (B.output f hf n).edges.length ∧
      (B.output f hf n).edges.length ≤ n + (B.reduce f).edges.length + 1 := by
  simpa [output, normalized] using
    (RawGraph.normalized_edge_bounds (rawGraph (B.reduce f) (B.valid f hf)) n)

theorem output_total_size (f : Formula) (hf : f.Valid) (n : ℕ) :
    (B.output f hf n).vertices + (B.output f hf n).edges.length ≤
      3 * (n + (B.reduce f).edges.length + 1) := by
  simpa [output, normalized] using
    (RawGraph.normalized_total_size (rawGraph (B.reduce f) (B.valid f hf)) n)

theorem output_code_length (f : Formula) (hf : f.Valid) (n : ℕ) :
    (EncodedGraph.encode (B.output f hf n)).length ≤
      50 * (n + (B.reduce f).edges.length + 1) ^ 2 := by
  have hs := B.output_total_size f hf n
  have he := EncodedGraph.encode_length_upper (B.output f hf n) (B.output_valid f hf n)
  have hn : 1 ≤ n + (B.reduce f).edges.length + 1 := by omega
  have hm := (B.output_edge_bounds f hf n).2
  have hv : (B.output f hf n).vertices ≤ 3 * (n + (B.reduce f).edges.length + 1) :=
    le_trans (Nat.le_add_right _ _) hs
  have hprod := Nat.mul_le_mul hm
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hv) 4)
  nlinarith

abbrev ValidGraph := {g : EncodedGraph.Graph // g.Valid}

/-- This is the literal ordered output list, not an existential collection
of graphs satisfying the source promise. -/
def graphList (n : ℕ) (fs : List ValidFormula) : List ValidGraph :=
  fs.map fun f : ValidFormula =>
    (⟨B.output f.val f.property n, B.output_valid f.val f.property n⟩ : ValidGraph)

def graphListBits (n : ℕ) (fs : List ValidFormula) : List Bool :=
  SourceListEncoding.encode ((B.graphList n fs).map fun g => EncodedGraph.encode g.val)

theorem graphList_count (n : ℕ) (fs : List ValidFormula) :
    (B.graphList n fs).length = fs.length := by simp [graphList]

theorem graphList_roundtrip (n : ℕ) (fs : List ValidFormula) :
    SourceListEncoding.decode (B.graphListBits n fs) =
      some ((B.graphList n fs).map fun g => EncodedGraph.encode g.val) :=
  SourceListEncoding.decode_encode _

theorem graphList_member_roundtrip (n : ℕ) (fs : List ValidFormula)
    (g : ValidGraph) (_hg : g ∈ B.graphList n fs) :
    EncodedGraph.decode (EncodedGraph.encode g.val) = some g.val :=
  EncodedGraph.decode_encode g.val g.property

theorem graphList_some_yes (n : ℕ) (fs : List ValidFormula)
    (hk : ∀ f ∈ fs, BoundedOccurrence f.val k)
    (h : ∃ f ∈ fs, Satisfiable f.val) :
    ∃ g ∈ B.graphList n fs, (rawGraph g.val g.property).Colourable := by
  obtain ⟨f, hf, hyes⟩ := h
  refine ⟨⟨B.output f.val f.property n, B.output_valid f.val f.property n⟩,
    List.mem_map.mpr ⟨f, hf, rfl⟩, ?_⟩
  exact (serialized_colourable_iff (B.normalized f.val f.property n)).mpr
    (B.normalized_yes f.val f.property (hk f hf) n hyes)

theorem graphList_every_no (n : ℕ) (fs : List ValidFormula) {V : ℕ} (hV : 0 < V) {ρ : ℚ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hk : ∀ f ∈ fs, BoundedOccurrence f.val k)
    (hused : ∀ f ∈ fs, f.val.variables ≤ V * f.val.clauses.length)
    (hm : ∀ f ∈ fs, 0 < f.val.clauses.length)
    (hgap : ∀ f ∈ fs, FormulaGap f.val ρ) :
    ∀ g ∈ B.graphList n fs, (rawGraph g.val g.property).Gap (B.gapFraction V ρ / 2) := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  exact serialized_gap (B.normalized f.val f.property n)
    (B.normalized_no f.val f.property (hk f hf) hV (hused f hf) (hm f hf) n hρ hρ1 (hgap f hf))

theorem graphListBits_length (n M : ℕ) (fs : List ValidFormula)
    (hM : ∀ f ∈ fs, (B.reduce f.val).edges.length ≤ M) :
    (B.graphListBits n fs).length ≤
      3 * fs.length * (50 * (n + M + 1) ^ 2 + 1) + 1 := by
  unfold graphListBits
  have h := SourceListEncoding.encode_map_length_le (B.graphList n fs)
    (fun g => EncodedGraph.encode g.val) (50 * (n + M + 1) ^ 2) ?_
  · simpa only [graphList_count] using h
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact (B.output_code_length f.val f.property n).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (by have := hM f hf; omega) 2))

end BOTReduction

/-- Constant factors in the normalization can be absorbed by a larger
polylogarithmic exponent. This is a finite scalar estimate; eventual growth
of the chosen logarithm and machine runtime are different obligations. -/
theorem constant_le_power (A : ℕ) : 3 * (A + 2) ≤ 2 ^ (A + 4) := by
  induction A with
  | zero => norm_num
  | succ A ih =>
      rw [show A + 1 + 4 = (A + 4) + 1 by omega, pow_succ]
      nlinarith

theorem normalized_size_absorb (n m A L c : ℕ) (hn : 1 ≤ n) (hL : 2 ≤ L)
    (hm : m ≤ A * n * L ^ c) :
    3 * (n + m + 1) ≤ n * L ^ (c + (A + 4)) := by
  have hpow : 1 ≤ L ^ c := Nat.one_le_pow _ _ (by omega)
  have hA := (constant_le_power A).trans (Nat.pow_le_pow_left hL (A + 4))
  have hmul := Nat.mul_le_mul_left (n * L ^ c) hA
  rw [pow_add]
  nlinarith [Nat.mul_le_mul_left n hpow]

end

end EthInapproximability.CurrentPaper.EncodedETHSource
