import CurrentV43.TimeTradeoff.Accuracy
import CurrentAdditive.V42ETHNumerics
import CurrentAdditive.V42SourceGeometry
import CurrentAdditive.V42AllRoundSampleAccess

/-! Size and eventual-domain discharges for the arbitrary schedule in v43
`thm:time-tradeoff`. Every bound concerns the actual v42 constructor output.
No fixed kOf/rounds schedule and no runtime assumption about a SAT algorithm
is used. Source: v43 main.tex 3269--3287, locked SHA256 recorded in Accuracy. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39GeneratedConstruction
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- Lifting the graph-size polynomial into the original-variable bound. -/
theorem graph_power_lift (N n e P K : ℕ) (hN : 1 ≤ N) (hn : n ≤ N^e) :
    (n+2)^(P*(K+1)) ≤ randomizedSize ((e+1)*P) N K := by
  have hpow : 1 ≤ (N+2)^e := Nat.one_le_pow _ _ (by omega)
  have hn' : n ≤ (N+2)^e := hn.trans (Nat.pow_le_pow_left (by omega) e)
  have hb : n+2 ≤ (N+2)^(e+1) := by rw [pow_succ]; nlinarith
  calc
    _ ≤ ((N+2)^(e+1))^(P*(K+1)) := Nat.pow_le_pow_left hb _
    _ = _ := by unfold randomizedSize; rw [←pow_mul]; congr 1; ring

/-- The sampled table grows with the source even for a constant positive gap. -/
theorem sampled_entries_ge_vertices (n K : ℕ) (hK : 1 ≤ K) :
    n ≤ V42PublicSchedule.sampleEntries (Nat.clog 2 n) K := by
  let L:=Nat.clog 2 n
  have hmul:V42PublicSchedule.fullOverhead L ≤ K*V42PublicSchedule.fullOverhead L :=
    Nat.le_mul_of_pos_left _ hK
  have hLH:L ≤ V42PublicSchedule.H L K := by
    unfold V42PublicSchedule.H V42PublicSchedule.B V42PublicSchedule.fullOverhead at *
    omega
  have hs:n ≤ V42PublicSchedule.sampleSide L K :=
    (Nat.le_pow_clog (by decide) n).trans
      ((Nat.pow_le_pow_right (by decide) hLH).trans (V42PublicSchedule.sampleSide_lower L K))
  exact hs.trans (Nat.le_self_pow (by decide : 2≠0) _)

/-- The eventual accuracy cutoff is met uniformly in every positive schedule. -/
theorem randomized_source_entries_large
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (Φ : ValidFormula) (T₀ K : ℕ) (hK : 1 ≤ K)
    (hN : Bsrc.degreeBound*T₀ ≤ Φ.val.variables) :
    T₀ ≤ V42PublicSchedule.sampleEntries
      (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K := by
  exact ((V39SourceGeometry.source_only Src Bsrc Φ).vertices_floor T₀ hN).trans
    (sampled_entries_ge_vertices _ K hK)

/-- The deterministic table is large on the same source, for every round. -/
theorem deterministic_source_entries_large
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (Φ : ValidFormula) (T₀ K : ℕ)
    (hN : Bsrc.degreeBound*T₀ ≤ Φ.val.variables) :
    T₀ ≤ V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K) := by
  let g:=t10Graph Src Bsrc Φ
  let p:=V42ActualSource.selected Src Bsrc Φ
  let R:=V42ActualSource.run Src Bsrc Φ K
  have hgeom:=V39CurrentSourceJoin.source_geometry Src Bsrc Φ
  have hn:T₀ ≤ g.vertices:=(V39SourceGeometry.source_only Src Bsrc Φ).vertices_floor T₀ hN
  have hnp:g.vertices ≤ 2^(4*p) := by
    simpa only [V42PublicSchedule.generatedN_exact] using
      (V42PublicCutoff.generatedExponent_spec g.vertices (V42ActualSource.k0 Src Bsrc)).2
  have hside:2^(4*p) ≤ SquarePadding.side R.rows R.cols :=
    V42ActualLower.public_side p (V42ActualSource.selected_two Src Bsrc Φ) hgeom.1
      (V42GraphRuntime.selected_width Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc) g
        hgeom.2.2 (V42ActualSource.k0_degree Src Bsrc))
      (LiteralEdgeEncoder.edge g (t10Graph_valid Src Bsrc Φ)) K
  exact (hn.trans (hnp.trans hside)).trans (Nat.le_self_pow (by decide : 2≠0) _)

/-- A single construction constant pays its table, random bits, and raw
printer time. Its value precedes the estimator and the chosen schedule. -/
def randomizedGraphExponent : ℕ := 2*V42ZeroAccess.packetExponentAll+544+80

theorem randomizedGraphExponent_pos : 1 ≤ randomizedGraphExponent := by
  unfold randomizedGraphExponent
  omega

/-- The actual randomized constructor's table size, clock and tape are all
bounded by the same original-variable S, uniformly over the round count. -/
theorem randomized_constructor_resources
    (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (N e K : ℕ) (hN : 1 ≤ N) (hgraph : g.vertices ≤ N^e)
    (cc δv ζ : ℚ)
    (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    V42PublicSchedule.sampleEntries (Nat.clog 2 g.vertices) K ≤
      randomizedSize ((e+1)*randomizedGraphExponent) N K ∧
    ∀ bits : V42PrintedCompression.Bits g K,
      V42WRaw.finiteMachine.OutputsWithin (V42WRaw.packedInput g K bits)
        (V42WRaw.outputWord g hg K cc δv ζ ht bits)
        (randomizedSize ((e+1)*randomizedGraphExponent) N K) ∧
      (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K) bits).length ≤
        randomizedSize ((e+1)*randomizedGraphExponent) N K := by
  have hlift:=graph_power_lift N g.vertices e randomizedGraphExponent K hN hgraph
  have hbase:1 ≤ g.vertices+2 := by omega
  have hpow (P:ℕ) (hP:P ≤ randomizedGraphExponent):
      (g.vertices+2)^(P*(K+1)) ≤ randomizedSize ((e+1)*randomizedGraphExponent) N K :=
    (Nat.pow_le_pow_right hbase (Nat.mul_le_mul_right (K+1) hP)).trans hlift
  have hn2:2 ≤ g.vertices := by
    have hL:=ht.1.2.2.1
    by_contra h
    have hz:g.vertices=0 ∨ g.vertices=1 := by omega
    rcases hz with hz|hz <;> norm_num [hz] at hL
  have hentries:=V42PublicSize.sampleEntries_polynomial_bound 0 g.vertices K hn2 ht.2
  have htable:V42PublicSchedule.sampleEntries (Nat.clog 2 g.vertices) K ≤
      (g.vertices+2)^(80*(K+1)) :=
    hentries.trans (Nat.pow_le_pow_left (by omega) _)
  refine ⟨htable.trans (hpow 80 (by unfold randomizedGraphExponent;omega)),?_⟩
  intro bits
  have h:=(V42ZeroAccess.sample_access_all g K cc δv ζ ht hg).1 bits
  exact ⟨BitMachine.outputsWithin_mono _ h.1 (hpow _ (by unfold randomizedGraphExponent;omega)),
    h.2.1.trans (hpow _ (by unfold randomizedGraphExponent;omega))⟩

/-- The deterministic bound uses the actual pipeline amplification, fixed
by the source reduction before the clause-density bound or estimator. -/
def deterministicSourceConstant (Src : DinurReduction)
    (Bsrc : BOTReduction (booleanOccurrence Src)) : ℕ :=
  (Src.sizeExponent+4)*V42ETHNumerics.sizeExponent Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc)

theorem deterministicSourceConstant_pos (Src : DinurReduction)
    (Bsrc : BOTReduction (booleanOccurrence Src)) : 1 ≤ deterministicSourceConstant Src Bsrc := by
  have h:=V42ETHNumerics.sizeExponent_ge Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc)
  unfold deterministicSourceConstant
  nlinarith

/-- Actual deterministic table size in the original variables, for arbitrary K. -/
theorem deterministic_source_size
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (cs : ℕ) (Φ : ValidFormula) (K : ℕ)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hcut : DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc cs ≤ Φ.val.variables)
    (hN : 16 ≤ Φ.val.variables)
    (hbase : 2^(4*V42ActualSource.k0 Src Bsrc) ≤ Φ.val.variables) :
    V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K) ≤
      deterministicSize (V42ETHPhysical.amplification Src Bsrc)
        (deterministicSourceConstant Src Bsrc) Φ.val.variables K := by
  let R:=V42ActualSource.run Src Bsrc Φ K
  let n:=Φ.val.variables
  let e:=Src.sizeExponent+3
  let g:=t10Graph Src Bsrc Φ
  have hgeom:=V39CurrentSourceJoin.source_geometry Src Bsrc Φ
  have hgraph:g.vertices ≤ n^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial Src Bsrc cs Φ hsp hcut
  have hpublic:V42RuntimePrefix.N (V42ActualSource.k0 Src Bsrc) g ≤ n^(e+1) :=
    V42ETHNumerics.selected_polynomial (V42ActualSource.k0 Src Bsrc) n e g
      hN (by unfold e;omega) hgraph hbase
  have hlen:R.squareWord.length ≤
      (V42RuntimePrefix.N (V42ActualSource.k0 Src Bsrc) g)^
        (V42ETHNumerics.sizeExponent Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc)*
          (V42ETHPhysical.amplification Src Bsrc)^K) :=
    V42ETHNumerics.actual_size Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc) g
      (t10Graph_valid Src Bsrc Φ) K (V42ActualSource.k0_two Src Bsrc) hgeom.1 hgeom.2.2
      (V42ActualSource.k0_degree Src Bsrc)
  have hentries:V42ActualLower.entryCount R ≤ R.squareWord.length :=
    V39ActualETHNumerics.entries_le_length R
  apply hentries.trans (hlen.trans ?_)
  calc
    _ ≤ (n^(e+1))^(V42ETHNumerics.sizeExponent Bsrc.degreeBound (V42ActualSource.k0 Src Bsrc)*
          (V42ETHPhysical.amplification Src Bsrc)^K) := Nat.pow_le_pow_left hpublic _
    _ = n^(deterministicSourceConstant Src Bsrc*(V42ETHPhysical.amplification Src Bsrc)^K) := by
      rw [←pow_mul]; congr 1; unfold deterministicSourceConstant e; ring
    _ ≤ _ := Nat.pow_le_pow_left (by omega) _

#print axioms sampled_entries_ge_vertices
#print axioms randomized_source_entries_large
#print axioms deterministic_source_entries_large
#print axioms randomized_constructor_resources
#print axioms deterministic_source_size
end
end CurrentV43.TimeTradeoff
