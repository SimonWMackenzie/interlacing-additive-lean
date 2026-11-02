import CurrentV43.MixedCaller.Resource

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
set_option maxHeartbeats 2500000
set_option maxRecDepth 65536

theorem producer_output_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz (fun w=>(P.result w).length) := by
  apply Unit4Shell.Poly.mono (fun w=>BitMachine.output_length_bound P.machine (P.outputs w))
  exact Unit4Shell.Poly.add hi (Unit4Shell.Poly.mul ht (Unit4Shell.Poly.const _))

theorem compose_local_clock_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (Q : PhysicalProducer.Producer) (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz
      (ParametricSource.compose P (PhysicalProducer.localProducer Q)).clock := by
  have ho:=producer_output_poly sz P hi ht
  change Unit4Shell.Poly.PolyIn sz
    (fun w=>P.clock w+2*(P.result w).length+2+Q.coefficient*((P.result w).length+1)^Q.degree)
  repeat (first
    | exact ht
    | exact ho
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

theorem append_clock_poly (sz : List Bool→ℕ) (P Q : PhysicalConcat.Producer)
    (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (hp : Unit4Shell.Poly.PolyIn sz P.clock) (hq : Unit4Shell.Poly.PolyIn sz Q.clock) :
    Unit4Shell.Poly.PolyIn sz (ParametricSource.append P Q).clock := by
  have hop:=producer_output_poly sz P hi hp
  have hoq:=producer_output_poly sz Q hi hq
  change Unit4Shell.Poly.PolyIn sz
    (fun w=>2*w.length+2+1+P.clock w+1+Q.clock w+2*(Q.result w).length+2+
      2*(P.result w).length+2+1)
  repeat (first
    | exact hi
    | exact hp
    | exact hq
    | exact hop
    | exact hoq
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul)

/-- The physically printed random carrier and its entire printing clock
are polynomial in the paid constructor time and original input length. -/
theorem tapeProducer_clock_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (C : SelectedTape.Algorithm) (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz (tapeProducer P C).clock := by
  have hR:Unit4Shell.Poly.PolyIn sz (tapeResource P C).clock:=
    compose_local_clock_poly sz P (tapeUnary C).producer hi ht
  have hId:Unit4Shell.Poly.PolyIn sz ParametricSource.identity.clock:=by
    change Unit4Shell.Poly.PolyIn sz (fun w=>2*w.length+2)
    exact Unit4Shell.Poly.add
      (Unit4Shell.Poly.mul (Unit4Shell.Poly.const _) hi) (Unit4Shell.Poly.const _)
  have hField:=compose_local_clock_poly sz ParametricSource.identity PhysicalProducer.field hi hId
  have hInner:Unit4Shell.Poly.PolyIn sz (ParametricSource.inner (tapeResource P C)).clock:=
    append_clock_poly sz _ _ hi hField hR
  have hL:=compose_local_clock_poly sz (ParametricSource.inner (tapeResource P C))
    DynamicGetterPrimitives.literalLength hi hInner
  have hLast:Unit4Shell.Poly.PolyIn sz
      (PhysicalProducer.localProducer (CodeDFixedWordProducer.producer [true,true])).clock:=by
    exact Unit4Shell.Poly.const 1
  exact append_clock_poly sz _ _ hi (append_clock_poly sz _ _ hi hL hL) hLast

theorem tapeLength_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (C : SelectedTape.Algorithm) (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz (tapeLength P C) := by
  have h:=producer_output_poly sz (tapeProducer P C) hi (tapeProducer_clock_poly sz P C hi ht)
  simpa only [tapeProducer,ParametricSource.carrier_result,List.length_replicate,tapeLength] using h

/-- The clock of the actual randomized caller is a function of the source
word alone; every tape in its exact printed carrier receives this same clock. -/
def finiteTime (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) (w : List Bool) :=
  finiteClock P C w (List.replicate (tapeLength P C w) true)

theorem finiteClock_eq (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w tape : List Bool) (ht : tape.length=tapeLength P C w) :
    finiteClock P C w tape=finiteTime P C w := by
  simp only [finiteClock,finiteTime,V40ClassifierTail.afterClock,EncodedComplexity.pair_length,
    List.length_replicate,ht]

theorem finiteTime_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (C : SelectedTape.Algorithm) (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz (finiteTime P C) := by
  have ho:=producer_output_poly sz P hi ht
  have hb:=tapeLength_poly sz P C hi ht
  have hs:=Unit4Shell.Poly.add (Unit4Shell.Poly.add (Unit4Shell.Poly.add hi ht) ho) hb
  obtain ⟨c,d,h⟩:=finiteClock_poly P C
  apply Unit4Shell.Poly.transfer hs
  refine ⟨c,d,fun w=>?_⟩
  simpa only [finiteTime,Prod.fst,Prod.snd,List.length_replicate] using
    h (w,List.replicate (tapeLength P C w) true)

/-- The carrier printer and caller are both paid by the same fixed polynomial.
This statement keeps literal execution separate from the subsequent resource
inequality; the constructor is never replaced by a completed-decider premise. -/
theorem full_cost_poly (sz : List Bool→ℕ) (P : PhysicalConcat.Producer)
    (C : SelectedTape.Algorithm) (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz P.clock) :
    Unit4Shell.Poly.PolyIn sz
      (fun w=>(tapeProducer P C).clock w+finiteTime P C w) :=
  Unit4Shell.Poly.add (tapeProducer_clock_poly sz P C hi ht) (finiteTime_poly sz P C hi ht)

theorem finite_outputs_fixed_clock (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) (tape : Fin (tapeLength P C w)→Bool) :
    (finiteMachine P C).OutputsWithin (EncodedComplexity.pair w (List.ofFn tape))
      (finiteOutput P C w (List.ofFn tape)) (finiteTime P C w) := by
  have h:=finite_outputs P C w tape
  rwa [finiteClock_eq P C w _ (by simp only [List.length_ofFn])] at h

#print axioms tapeProducer_clock_poly
#print axioms finiteTime_poly
#print axioms full_cost_poly
#print axioms finite_outputs_fixed_clock
end
end CurrentV43.MixedCaller
