import CurrentV43.Parametric.Source
import CurrentV43.Parametric.Carrier
import CurrentV43.TimeTradeoff.SourceBounds
import Paper2.A4T10Size
import Paper2.A4T24RuntimeComposed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

namespace CurrentV43.ResourceFit
noncomputable section
open Paper2 EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff
attribute [local irreducible] randomizedGraphExponent V42ZeroAccess.packetExponentAll

def budget (E : ℕ) (S : Schedule) (Φ : ValidFormula) : ℕ :=
  ((EncodedCNF.encode Φ.val).length+2)^(E*(S.gap Φ.val.variables+1))

theorem budget_mono (E F : ℕ) (h : E ≤ F) (S : Schedule) (Φ : ValidFormula) :
    budget E S Φ ≤ budget F S Φ :=
  Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ h)

theorem budget_dominates (E : ℕ) (hE : 1 ≤ E) (S : Schedule) (Φ : ValidFormula) :
    Φ.val.variables+S.gap Φ.val.variables+2 ≤ budget E S Φ := by
  have hn := EncodedCNF.encode_length_lower Φ.val
  exact (by omega : Φ.val.variables+S.gap Φ.val.variables+2 ≤
    (EncodedCNF.encode Φ.val).length+S.gap Φ.val.variables+2).trans
    (randomizedSize_dominates E (EncodedCNF.encode Φ.val).length _ hE)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
local instance sourceNonzero (Φ : ValidFormula) : NeZero (t10Graph D B Φ).vertices :=
  ⟨(t10_vertices_pos D B Φ).ne'⟩
attribute [local irreducible] V42WRaw.packetCoefficient V42ZeroAccess.rawTableExponentAll

def graphWordExponent : ℕ := Unit4Shell.T10Size.sizeC D B+D.sizeExponent+1
attribute [local irreducible] graphWordExponent

theorem graph_word_power (Φ : ValidFormula) :
    (t10Graph D B Φ).vertices+2 ≤
      ((EncodedCNF.encode Φ.val).length+2)^(graphWordExponent D B) := by
  let w := (EncodedCNF.encode Φ.val).length
  have hc : Unit4Shell.T10Size.sizeC D B ≤ (w+2)^(Unit4Shell.T10Size.sizeC D B) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)
  calc
    _ ≤ Unit4Shell.T10Size.sizeC D B*(w+1)^(D.sizeExponent+1) :=
      Unit4Shell.T10Size.t10_size_poly D B Φ
    _ ≤ (w+2)^(Unit4Shell.T10Size.sizeC D B)*(w+2)^(D.sizeExponent+1) :=
      Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [←pow_add]; unfold graphWordExponent; rw [Nat.add_assoc]

def sourceExponent : ℕ := graphWordExponent D B*randomizedGraphExponent
attribute [local irreducible] sourceExponent

theorem sourceExponent_pos : 1 ≤ sourceExponent D B := by
  have hp := randomizedGraphExponent_pos
  unfold sourceExponent graphWordExponent
  nlinarith

theorem graph_resource_bound (S : Schedule) (Φ : ValidFormula) (P : ℕ)
    (hP : P ≤ randomizedGraphExponent) :
    ((t10Graph D B Φ).vertices+2)^(P*(S.gap Φ.val.variables+1)) ≤
      budget (sourceExponent D B) S Φ := by
  calc
    _ ≤ (((EncodedCNF.encode Φ.val).length+2)^(graphWordExponent D B))^
      (P*(S.gap Φ.val.variables+1)) := Nat.pow_le_pow_left (graph_word_power D B Φ) _
    _ ≤ (((EncodedCNF.encode Φ.val).length+2)^(graphWordExponent D B))^
      (randomizedGraphExponent*(S.gap Φ.val.variables+1)) :=
      Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (Nat.mul_le_mul_right _ hP)
    _ = _ := by unfold budget sourceExponent; rw [←pow_mul,Nat.mul_assoc]

omit D B in
theorem graph_source_resources (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (k : ℕ) (cc δv ζ : ℚ)
    (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ) :
    V42RawSamplerJoin.precision g.vertices k*V42RawSamplerJoin.reservation g.vertices k ≤
        (g.vertices+2)^(randomizedGraphExponent*(k+1)) ∧
    V42PublicSchedule.sampleEntries (Nat.clog 2 g.vertices) k ≤
      (g.vertices+2)^(randomizedGraphExponent*(k+1)) ∧
    V42WRaw.clock g k ≤ (g.vertices+2)^(randomizedGraphExponent*(k+1)) := by
  have hn : 1 ≤ g.vertices := by have h := NeZero.pos g.vertices; omega
  have hn2 : 2 ≤ g.vertices := by
    have hL : 16 ≤ Nat.clog 2 g.vertices := ht.1.2.2.1
    by_contra h
    have hz : g.vertices=0 ∨ g.vertices=1 := by omega
    rcases hz with hz|hz <;> norm_num [hz] at hL
  have hbits := V42RuntimeSchedule.reserved_bits_le g.vertices (Nat.clog 2 g.vertices) k
    (Nat.le_pow_clog (by decide) _) ht.2
  have hbits' := V42ZeroAccess.binary_resource_source_power 272 g.vertices k hn
  have hb : V42RawSamplerJoin.precision g.vertices k*V42RawSamplerJoin.reservation g.vertices k ≤
      (g.vertices+2)^(544*(k+1)) := by
    apply hbits.trans
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbits'
  have he := V42PublicSize.sampleEntries_polynomial_bound 0 g.vertices k hn2 ht.2
  have he' : V42PublicSchedule.sampleEntries (Nat.clog 2 g.vertices) k ≤
      (g.vertices+2)^(80*(k+1)) := he.trans (Nat.pow_le_pow_left (by omega) _)
  have hc := V42ZeroAccess.raw_table_pure_all g hg k cc δv ζ ht
  have hc' := V42ZeroAccess.binary_resource_source_power
    (V42ZeroAccess.rawTableExponentAll+440) g.vertices k hn
  have hclock : V42WRaw.clock g k ≤
      (g.vertices+2)^((2*(V42ZeroAccess.rawTableExponentAll+440))*(k+1)) := by
    apply hc.trans
    simpa only [V42FullTableClock.physical_clock_eq,V42FullTableClock.T,
      Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc'
  have hpow (P : ℕ) (hP : P ≤ randomizedGraphExponent) :
      (g.vertices+2)^(P*(k+1)) ≤ (g.vertices+2)^(randomizedGraphExponent*(k+1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hP)
  exact ⟨hb.trans (hpow _ (by unfold randomizedGraphExponent; omega)),
    he'.trans (hpow _ (by unfold randomizedGraphExponent; omega)),
    hclock.trans (hpow _ (by unfold randomizedGraphExponent V42ZeroAccess.packetExponentAll; omega))⟩

theorem actual_source_resources (S : Schedule) (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
      (t10Graph D B Φ).edges.length δv ζ) :
    V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables) ≤
        budget (sourceExponent D B) S Φ ∧
    V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices)
      (S.gap Φ.val.variables) ≤ budget (sourceExponent D B) S Φ ∧
    V42WRaw.clock (t10Graph D B Φ) (S.gap Φ.val.variables) ≤
      budget (sourceExponent D B) S Φ := by
  obtain ⟨hb,he,hc⟩ := graph_source_resources (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) cc δv ζ ht
  have h := graph_resource_bound D B S Φ randomizedGraphExponent le_rfl
  exact ⟨hb.trans h,he.trans h,hc.trans h⟩

theorem polynomial_tape_absorb (b P k c d : ℕ) (hb : 2 ≤ b) :
    c*(9*b^(P*(k+1))+4)^d ≤ b^((c+(P+4)*d)*(k+1)) := by
  let z := b^(P*(k+1))
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by omega)
  have h16 : 16 ≤ b^4 := (by norm_num : (16:ℕ)=2^4).le.trans (Nat.pow_le_pow_left hb 4)
  have hi : 9*z+4 ≤ b^((P+4)*(k+1)) := by
    calc
      _ ≤ 16*z := by omega
      _ ≤ b^4*b^(P*(k+1)) := Nat.mul_le_mul_right _ h16
      _ = b^(4+P*(k+1)) := by rw [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hc : c ≤ b^(c*(k+1)) := Nat.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left hb c).trans (Nat.pow_le_pow_right (by omega) (by nlinarith)))
  calc
    _ ≤ b^(c*(k+1))*(b^((P+4)*(k+1)))^d := Nat.mul_le_mul hc (Nat.pow_le_pow_left hi d)
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; ring

def resourceExponent (C : SelectedTape.Algorithm) : ℕ :=
  sourceExponent D B+C.cR+(sourceExponent D B+4)*C.dR+1

theorem resourceExponent_pos (C : SelectedTape.Algorithm) : 1 ≤ resourceExponent D B C := by
  unfold resourceExponent; omega

theorem actual_tapes_fit (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula)
    (cc δv ζ : ℚ)
    (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
      (t10Graph D B Φ).edges.length δv ζ) :
    V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables) ≤
        budget (resourceExponent D B C) S Φ ∧
    ∀ bits : RoundedDraw.BitBlocks
      (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables))
      (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)),
      C.tapeLength (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
        (S.gap Φ.val.variables) cc δv ζ ht bits) ≤ budget (resourceExponent D B C) S Φ := by
  have hb := budget_mono (sourceExponent D B) (resourceExponent D B C)
    (by unfold resourceExponent; omega) S Φ
  obtain ⟨hbits,hentries,_⟩ := actual_source_resources D B S Φ cc δv ζ ht
  refine ⟨hbits.trans hb,?_⟩
  intro bits
  let f := V42RawRequestPacket.matrix (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) cc δv ζ ht bits
  have hrl := V40MidpointRequest.v42_request_length (Nat.clog 2 (t10Graph D B Φ).vertices)
    (S.gap Φ.val.variables) f
  have hreq : C.tapeLength (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (S.gap Φ.val.variables) cc δv ζ ht bits) ≤
      C.cR*(9*V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices)
        (S.gap Φ.val.variables)+4)^C.dR := by
    unfold SelectedTape.Algorithm.tapeLength
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (S.gap Φ.val.variables) cc δv ζ ht bits).length+1 ≤ _
    change (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (S.gap Φ.val.variables) cc δv ζ ht bits).length ≤
      9*V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices)
        (S.gap Φ.val.variables)+3 at hrl
    omega
  apply hreq.trans
  have hpoly := polynomial_tape_absorb ((EncodedCNF.encode Φ.val).length+2)
    (sourceExponent D B) (S.gap Φ.val.variables) C.cR C.dR (by omega)
  have hentry := Nat.mul_le_mul_left C.cR (Nat.pow_le_pow_left
    (show 9*V42PublicSchedule.sampleSide (Nat.clog 2 (t10Graph D B Φ).vertices)
      (S.gap Φ.val.variables)^2+4 ≤ 9*budget (sourceExponent D B) S Φ+4 by
        change 9*V42PublicSchedule.sampleEntries _ _+4 ≤ _
        omega) C.dR)
  exact hentry.trans (hpoly.trans (Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_right _ (by unfold resourceExponent; omega))))

theorem budget_manuscript_polynomial (E C0 cs : ℕ) (hC0 : 1 ≤ C0)
    (S : Schedule) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : 28*cs+9 ≤ Φ.val.variables) :
    budget E S Φ ≤ (randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables))^(3*E) := by
  have henc := Unit4Shell.T24RuntimeComposed.encode_length_cube cs Φ hsp hN
  have hb : (EncodedCNF.encode Φ.val).length+2 ≤ (Φ.val.variables+2)^3 := by omega
  calc
    _ ≤ ((Φ.val.variables+2)^3)^(E*(S.gap Φ.val.variables+1)) := Nat.pow_le_pow_left hb _
    _ ≤ ((Φ.val.variables+2)^3)^(C0*(E*(S.gap Φ.val.variables+1))) :=
      Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (Nat.le_mul_of_pos_left _ hC0)
    _ = _ := by unfold randomizedSize; rw [←pow_mul,←pow_mul]; congr 1; ring

#print axioms actual_source_resources
#print axioms actual_tapes_fit
#print axioms budget_manuscript_polynomial
end
end CurrentV43.ResourceFit
