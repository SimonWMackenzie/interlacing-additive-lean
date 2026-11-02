import CurrentV43.ResourceClock
import CurrentV43.ResourceFit
import CurrentV43.Parametric.Resource
import CurrentV43.Parametric.Timing
import CurrentV43.Parametric.Algorithm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

namespace CurrentV43.ResourceFit
noncomputable section
open Paper2 EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff Unit4Shell.Poly
variable {ι : Type*} {sz : ι → ℕ}

theorem bank2_clock_poly (A B : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (ha : PolyIn sz (fun i => A.clock (x i)))
    (hb : PolyIn sz (fun i => B.clock (x i))) :
    PolyIn sz (fun i => (bank2 A B).clock (x i)) :=
  append_clock_poly _ _ x hx (compose_local_clock_poly A PhysicalProducer.field x hx ha)
    (compose_local_clock_poly B PhysicalProducer.field x hx hb)

theorem resource_input_clock_poly (S : Schedule) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hs : PolyIn sz (fun i => S.producer.clock (x i))) :
    PolyIn sz (fun i => (resourceInput S).clock (x i)) :=
  bank2_clock_poly _ _ x hx (local_clock_poly DynamicGetterPrimitives.literalLength x hx)
    (compose_local_clock_poly S.producer DynamicGetterPrimitives.literalLength x hx hs)

theorem resource_producer_clock_poly (E : ℕ) (S : Schedule) (φ : ι → ValidFormula)
    (hx : PolyIn sz (fun i => (EncodedCNF.encode (φ i).val).length))
    (hs : PolyIn sz (fun i => S.producer.clock (EncodedCNF.encode (φ i).val)))
    (hb : PolyIn sz (fun i => budget E S (φ i))) :
    PolyIn sz (fun i => (resourceProducer S E).clock (EncodedCNF.encode (φ i).val)) := by
  let x := fun i => EncodedCNF.encode (φ i).val
  have hi := resource_input_clock_poly S x hx hs
  have hil := producer_length_poly (resourceInput S) x hx hi
  have hsl := producer_length_poly S.producer x hx hs
  have hp : PolyIn sz (fun i => (x i).length+(S.producer.result (x i)).length+E+
      ((x i).length+2)^(E*((S.producer.result (x i)).length+1))+1) := by
    have hb' : PolyIn sz (fun i => ((x i).length+2)^(E*((S.producer.result (x i)).length+1))) := by
      simpa only [x,S.correct,List.length_replicate,budget] using hb
    exact add (add (add (add hx hsl) (const E)) hb') (const 1)
  have hpower : PolyIn sz (fun i => PowerMachine.resourceClock E (x i).length
      (S.producer.result (x i)).length) :=
    mono (fun i => PowerMachine.resourceClock_le E (x i).length (S.producer.result (x i)).length)
      (mul (const 512) (pow hp 3))
  exact add (add (add hi (mul (const 2) hil)) (const 2)) hpower

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
attribute [local irreducible] sourceExponent graphWordExponent randomizedGraphExponent
  V42ZeroAccess.packetExponentAll V42ZeroAccess.rawTableExponentAll V42WRaw.packetCoefficient
local instance totalSourceNonzero (Φ : ValidFormula) : NeZero (t10Graph D B Φ).vertices :=
  ⟨(t10_vertices_pos D B Φ).ne'⟩

theorem concrete_tapes_fit (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula)
    (cc δv ζ : ℚ)
    (ht : V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
      (t10Graph D B Φ).edges.length δv ζ) :
    V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables) ≤
        blockLength (resourceProducer S (resourceExponent D B C)) (EncodedCNF.encode Φ.val) ∧
    ∀ tape : List Bool, C.tapeLength (request D B S Φ cc δv ζ ht tape) ≤
      blockLength (resourceProducer S (resourceExponent D B C)) (EncodedCNF.encode Φ.val) := by
  have hb : budget (resourceExponent D B C) S Φ ≤
      blockLength (resourceProducer S (resourceExponent D B C)) (EncodedCNF.encode Φ.val) := by
    have h := resource_le_block (resourceProducer S (resourceExponent D B C)) (EncodedCNF.encode Φ.val)
    rw [resource_length] at h
    exact h
  obtain ⟨hfirst,hclass⟩ := actual_tapes_fit D B C S Φ cc δv ζ ht
  exact ⟨hfirst.trans hb,fun tape => (hclass (sampledBits D B S Φ tape)).trans hb⟩

/-- Indexing type contains source and sparsity premises, never a runtime conclusion. -/
structure SparseContext (S : Schedule) (cs : ℕ) where
  formula : ValidFormula
  sparse : formula.val.clauses.length ≤ cs*formula.val.variables
  cc : ℚ
  deltaV : ℚ
  zeta : ℚ
  tests : V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B formula).vertices)
    (t10Graph D B formula).edges.length deltaV zeta

/-- Literal total charge of the parametric machine and physically printed carrier.
It includes carrier production, all fair bits, initial framing and uniform execution. -/
def totalClock (C : SelectedTape.Algorithm) (S : Schedule) (E : ℕ) (Φ : ValidFormula) : ℕ :=
  let R := resourceProducer S E
  let w := EncodedCNF.encode Φ.val
  (carrierProducer R).clock w+carrierLength R w+4*(w.length+carrierLength R w+1)+
    uniformClock D B C S R Φ

theorem total_clock_resource_polynomial (C : SelectedTape.Algorithm) (S : Schedule)
    (cs E : ℕ) (hE : sourceExponent D B ≤ E) (hE1 : 1 ≤ E) :
    ∃ a d : ℕ, ∀ (Φ : ValidFormula),
      Φ.val.clauses.length ≤ cs*Φ.val.variables → ∀ cc δv ζ : ℚ,
      V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
        (t10Graph D B Φ).edges.length δv ζ →
      totalClock D B C S E Φ ≤ a*(budget E S Φ+1)^d := by
  let φ : SparseContext D B S cs → ValidFormula := fun i => i.formula
  let x := fun i => EncodedCNF.encode (φ i).val
  let sz := fun i => budget E S (φ i)
  have hword (i : SparseContext D B S cs) : (x i).length+S.gap (φ i).val.variables+2 ≤ sz i :=
    randomizedSize_dominates E (x i).length _ hE1
  have hdom (i : SparseContext D B S cs) : (φ i).val.variables+S.gap (φ i).val.variables+2 ≤ sz i :=
    budget_dominates E hE1 S (φ i)
  have hx : PolyIn sz (fun i => (x i).length) := mono (fun i => by have := hword i; omega) self
  have hk : PolyIn sz (fun i => S.gap (φ i).val.variables) := mono (fun i => by have := hword i; omega) self
  obtain ⟨csched,dsched,hpaid⟩ := S.paid cs
  have hs : PolyIn sz (fun i => S.producer.clock (x i)) := by
    refine ⟨csched,dsched,?_⟩
    intro i
    exact (hpaid (φ i) i.sparse).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (show (φ i).val.variables+S.gap (φ i).val.variables+1 ≤ sz i+1 by have := hdom i; omega) _))
  have hR := resource_producer_clock_poly E S φ hx hs (self (sz:=sz))
  have hcarrier := carrier_clock_poly (resourceProducer S E) x hx hR
  have hcarrierlen := carrier_length_poly (resourceProducer S E) x hx hR
  have hentries : PolyIn sz (fun i => V42PublicSchedule.sampleEntries
      (Nat.clog 2 (t10Graph D B (φ i)).vertices) (S.gap (φ i).val.variables)) := by
    apply mono (fun i => ?_) self
    exact (actual_source_resources D B S (φ i) i.cc i.deltaV i.zeta i.tests).2.1.trans
      (budget_mono _ _ hE S (φ i))
  have hraw : PolyIn sz (fun i => V42WRaw.clock (t10Graph D B (φ i)) (S.gap (φ i).val.variables)) := by
    apply mono (fun i => ?_) self
    exact (actual_source_resources D B S (φ i) i.cc i.deltaV i.zeta i.tests).2.2.trans
      (budget_mono _ _ hE S (φ i))
  have hrun : PolyIn sz (fun i => uniformClock D B C S (resourceProducer S E) (φ i)) :=
    random_clock_poly D B C S (resourceProducer S E) φ
      (fun i => List.replicate (carrierLength (resourceProducer S E) (x i)) false)
      hx hk hs hR hraw hentries
  have htotal : PolyIn sz (fun i => totalClock D B C S E (φ i)) :=
    add (add (add hcarrier hcarrierlen)
      (mul (const 4) (add (add hx hcarrierlen) (const 1)))) hrun
  obtain ⟨a,d,had⟩ := htotal
  exact ⟨a,d,fun Φ hsp cc δv ζ ht => had ⟨Φ,hsp,cc,δv,ζ,ht⟩⟩

/-- The manuscript construction constant stays independent of the classifier.
The selected resource exponent is absorbed only in the final polynomial degree. -/
theorem total_clock_manuscript_polynomial (C : SelectedTape.Algorithm) (S : Schedule)
    (cs C0 E : ℕ) (hC0 : 1 ≤ C0) (hE : sourceExponent D B ≤ E) (hE1 : 1 ≤ E) :
    ∃ a d : ℕ, ∀ (Φ : ValidFormula),
      Φ.val.clauses.length ≤ cs*Φ.val.variables → 28*cs+9 ≤ Φ.val.variables →
      ∀ cc δv ζ : ℚ,
      V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
        (t10Graph D B Φ).edges.length δv ζ →
      totalClock D B C S E Φ ≤ a*(randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables))^d := by
  obtain ⟨a,d,h⟩ := total_clock_resource_polynomial D B C S cs E hE hE1
  refine ⟨a*2^d,3*E*d,?_⟩
  intro Φ hsp hN cc δv ζ ht
  have hb := budget_manuscript_polynomial E C0 cs hC0 S Φ hsp hN
  have hS : 1 ≤ randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables) :=
    Nat.one_le_pow _ _ (by omega)
  have hP : 1 ≤ (randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables))^(3*E) :=
    Nat.one_le_pow _ _ hS
  apply (h Φ hsp cc δv ζ ht).trans
  calc
    _ ≤ a*(2*(randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables))^(3*E))^d :=
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) d)
    _ = _ := by rw [mul_pow,←pow_mul]; ring

theorem chosen_total_clock_resource_polynomial (C : SelectedTape.Algorithm)
    (S : Schedule) (cs : ℕ) :
    ∃ a d : ℕ, ∀ (Φ : ValidFormula),
      Φ.val.clauses.length ≤ cs*Φ.val.variables → ∀ cc δv ζ : ℚ,
      V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
        (t10Graph D B Φ).edges.length δv ζ →
      totalClock D B C S (resourceExponent D B C) Φ ≤
        a*(budget (resourceExponent D B C) S Φ+1)^d :=
  total_clock_resource_polynomial D B C S cs (resourceExponent D B C)
    (by unfold resourceExponent; omega) (resourceExponent_pos D B C)

theorem chosen_total_clock_manuscript_polynomial (C : SelectedTape.Algorithm)
    (S : Schedule) (cs C0 : ℕ) (hC0 : 1 ≤ C0) :
    ∃ a d : ℕ, ∀ (Φ : ValidFormula),
      Φ.val.clauses.length ≤ cs*Φ.val.variables → 28*cs+9 ≤ Φ.val.variables →
      ∀ cc δv ζ : ℚ,
      V42RuntimeSchedule.FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices)
        (t10Graph D B Φ).edges.length δv ζ →
      totalClock D B C S (resourceExponent D B C) Φ ≤
        a*(randomizedSize C0 Φ.val.variables (S.gap Φ.val.variables))^d :=
  total_clock_manuscript_polynomial D B C S cs C0 (resourceExponent D B C) hC0
    (by unfold resourceExponent; omega) (resourceExponent_pos D B C)

#print axioms resource_producer_clock_poly
#print axioms concrete_tapes_fit
#print axioms total_clock_resource_polynomial
#print axioms total_clock_manuscript_polynomial
#print axioms chosen_total_clock_resource_polynomial
#print axioms chosen_total_clock_manuscript_polynomial
end
end CurrentV43.ResourceFit
