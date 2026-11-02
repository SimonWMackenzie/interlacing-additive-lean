import CurrentV43.TimeTradeoff.SourceBounds
import CurrentV43.Parametric.Caller

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

namespace CurrentV43.ResourceFit
noncomputable section
open Paper2 EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff Unit4Shell.Poly

variable {ι : Type*} {sz : ι → ℕ}

theorem poly_apply {f : ℕ → ℕ} (hf : PolyIn id f) {a : ι → ℕ}
    (ha : PolyIn sz a) : PolyIn sz (fun i => f (a i)) := by
  obtain ⟨c,d,h⟩ := hf
  exact transfer ha ⟨c,d,fun i => h (a i)⟩

theorem producer_length_poly (A : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hA : PolyIn sz (fun i => A.clock (x i))) :
    PolyIn sz (fun i => (A.result (x i)).length) := by
  apply mono (fun i => BitMachine.output_length_bound A.machine (A.outputs (x i)))
  exact add hx (mul hA (const _))

theorem local_clock_poly (A : PhysicalProducer.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length)) :
    PolyIn sz (fun i => (PhysicalProducer.localProducer A).clock (x i)) := by
  exact mul (const _) (pow (add hx (const 1)) _)

theorem compose_local_clock_poly (A : PhysicalConcat.Producer) (B : PhysicalProducer.Producer)
    (x : ι → List Bool) (hx : PolyIn sz (fun i => (x i).length))
    (hA : PolyIn sz (fun i => A.clock (x i))) :
    PolyIn sz (fun i => (ParametricSource.compose A (PhysicalProducer.localProducer B)).clock (x i)) := by
  have hy := producer_length_poly A x hx hA
  have hb := local_clock_poly B (fun i => A.result (x i)) hy
  change PolyIn sz (fun i => A.clock (x i)+2*(A.result (x i)).length+2+
    (PhysicalProducer.localProducer B).clock (A.result (x i)))
  exact add (add (add hA (mul (const 2) hy)) (const 2)) hb

theorem append_clock_poly (A B : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hA : PolyIn sz (fun i => A.clock (x i)))
    (hB : PolyIn sz (fun i => B.clock (x i))) :
    PolyIn sz (fun i => (ParametricSource.append A B).clock (x i)) := by
  have ha := producer_length_poly A x hx hA
  have hb := producer_length_poly B x hx hB
  unfold ParametricSource.append PhysicalConcat.clock
  repeat (first | exact const _ | exact hx | exact hA | exact hB | exact ha | exact hb | apply add | apply mul | apply pow)

theorem identity_clock_poly (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length)) :
    PolyIn sz (fun i => ParametricSource.identity.clock (x i)) := by
  exact add (mul (const 2) hx) (const 2)

theorem inner_clock_poly (R : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hR : PolyIn sz (fun i => R.clock (x i))) :
    PolyIn sz (fun i => (inner R).clock (x i)) := by
  exact append_clock_poly _ _ x hx
    (compose_local_clock_poly ParametricSource.identity PhysicalProducer.field x hx (identity_clock_poly x hx)) hR

theorem carrier_clock_poly (R : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hR : PolyIn sz (fun i => R.clock (x i))) :
    PolyIn sz (fun i => (carrierProducer R).clock (x i)) := by
  have hI := inner_clock_poly R x hx hR
  have hL := compose_local_clock_poly (inner R) DynamicGetterPrimitives.literalLength x hx hI
  exact append_clock_poly _ _ x hx (append_clock_poly _ _ x hx hL hL)
    (local_clock_poly (CodeDFixedWordProducer.producer [true,true]) x hx)

theorem block_length_poly (R : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hR : PolyIn sz (fun i => R.clock (x i))) :
    PolyIn sz (fun i => blockLength R (x i)) := by
  exact add (producer_length_poly (inner R) x hx (inner_clock_poly R x hx hR)) (const 1)

theorem carrier_length_poly (R : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hR : PolyIn sz (fun i => R.clock (x i))) :
    PolyIn sz (fun i => carrierLength R (x i)) :=
  mul (const 2) (block_length_poly R x hx hR)

theorem cut_time_poly (c d pb : ℕ) (m t : ι → ℕ)
    (hm : PolyIn sz m) (ht : PolyIn sz t) :
    PolyIn sz (fun i => AEth2.Cut.cutTimeG c d pb (m i) (t i)) := by
  unfold AEth2.Cut.cutTimeG
  repeat (first | exact const _ | exact hm | exact ht | apply add | apply mul | apply pow)

theorem retain_time_poly (c d cf df pb : ℕ) (m : ι → ℕ)
    (hm : PolyIn sz m) :
    PolyIn sz (fun i => SelectedTape.Bind.Retain.timeBound c d cf df pb (m i)) := by
  unfold SelectedTape.Bind.Retain.timeBound
  repeat (first | exact const _ | exact hm | apply add | apply mul | apply pow)

theorem split_clock_poly (R : PhysicalConcat.Producer) (x : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (hR : PolyIn sz (fun i => R.clock (x i))) :
    PolyIn sz (fun i => splitClock R (x i)) := by
  have hi := inner_clock_poly R x hx hR
  have hil := producer_length_poly (inner R) x hx hi
  have hl := block_length_poly R x hx hR
  have hc := carrier_length_poly R x hx hR
  have hmid : PolyIn sz (fun i => 2*((inner R).result (x i)).length+1+carrierLength R (x i)) :=
    add (add (mul (const 2) hil) (const 1)) hc
  have hcut := cut_time_poly 2 1 (inner R).machine.pushBound
    (fun i => (x i).length) (fun i => (inner R).clock (x i)) hx hi
  have hret := retain_time_poly 1 1 SelectedTape.Bind.idC SelectedTape.Bind.idD
    SelectedTape.Bind.idMachine.pushBound _ hmid
  have hcutclock : PolyIn sz (fun i => cutClock R (x i)) :=
    add (add (add hcut (mul (const 2) hmid)) (const 2)) hret
  unfold splitClock
  exact add (add (add hcutclock
    (mul (const 2) (add (add (mul (const 2)
      (add (add (mul (const 2) hil) (const 1)) hl)) (const 1)) (mul (const 2) hl)))) (const 2))
    (add (add (add
      (mul (const 2) (add (add (mul (const 2) hil) (const 1)) hl))
      (add (add (add (mul (const 2) hil)
        (add (mul (const 2) hx) (const 3))) (mul (const 2) hx)) (const 6)))
      (mul (const 2) (add (add (mul (const 2) hx) (const 1)) hl))) (const 6))

theorem kfront_clock_poly (S : Schedule) (x tape : ι → List Bool)
    (hx : PolyIn sz (fun i => (x i).length))
    (ht : PolyIn sz (fun i => (tape i).length))
    (hs : PolyIn sz (fun i => S.producer.clock (x i))) :
    PolyIn sz (fun i => kFrontClock S (x i) (tape i)) := by
  have hy := producer_length_poly S.producer x hx hs
  unfold kFrontClock
  simp only [EncodedComplexity.pair_length]
  repeat (first | exact const _ | exact hx | exact ht | exact hs | exact hy | apply add | apply mul | apply pow)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem source_clock_poly (S : Schedule) (φ : ι → ValidFormula) (tape : ι → List Bool)
    (hx : PolyIn sz (fun i => (EncodedCNF.encode (φ i).val).length))
    (hk : PolyIn sz (fun i => S.gap (φ i).val.variables))
    (ht : PolyIn sz (fun i => (tape i).length))
    (hs : PolyIn sz (fun i => S.producer.clock (EncodedCNF.encode (φ i).val))) :
    PolyIn sz (fun i => sourceClock D B S (φ i) (tape i)) := by
  let mid := fun i => EncodedComplexity.pair (EncodedCNF.encode (φ i).val)
    (EncodedComplexity.pair (List.replicate (S.gap (φ i).val.variables) true) (tape i))
  have hm : PolyIn sz (fun i => (mid i).length) := by
    dsimp [mid]
    simp only [EncodedComplexity.pair_length,List.length_replicate]
    repeat (first | exact const _ | exact hx | exact hk | exact ht | apply add | apply mul)
  have hb : PolyIn sz (fun i => (BitMachineBankCodec.encode
      ![EncodedGraph.encode (t10Graph D B (φ i)),List.replicate (S.gap (φ i).val.variables) true,tape i]).length) := by
    apply mono (fun i => BitMachine.output_length_bound (uniformMachine D B)
      (uniform_outputs D B (S.gap (φ i).val.variables) (φ i) (tape i)))
    change PolyIn sz (fun i => (mid i).length+
      (uniformCoefficient D B*((mid i).length+1)^uniformDegree D B)*(uniformMachine D B).pushBound)
    repeat (first | exact const _ | exact hm | apply add | apply mul | apply pow)
  have hf := kfront_clock_poly S (fun i => EncodedCNF.encode (φ i).val) tape hx ht hs
  unfold ParametricSource.sourceClock
  repeat (first | exact const _ | exact hf | exact hm | exact hb | apply add | apply mul | apply pow)

theorem source_word_poly (S : Schedule) (φ : ι → ValidFormula) (tape : ι → List Bool)
    (hx : PolyIn sz (fun i => (EncodedCNF.encode (φ i).val).length))
    (hk : PolyIn sz (fun i => S.gap (φ i).val.variables))
    (ht : PolyIn sz (fun i => (tape i).length))
    (hs : PolyIn sz (fun i => S.producer.clock (EncodedCNF.encode (φ i).val))) :
    PolyIn sz (fun i => (sourceWord D B S (φ i) (tape i)).length) := by
  apply mono (fun i => BitMachine.output_length_bound (sourceMachine D B S)
    (source_outputs D B S (φ i) (tape i)))
  simp only [EncodedComplexity.pair_length]
  exact add (add (add (mul (const 2) hx) (const 1)) ht)
    (mul (source_clock_poly D B S φ tape hx hk ht hs) (const _))

theorem caller_clock_poly (C : SelectedTape.Algorithm) (S : Schedule)
    (φ : ι → ValidFormula) (tape classifierTape : ι → List Bool)
    (hx : PolyIn sz (fun i => (EncodedCNF.encode (φ i).val).length))
    (hk : PolyIn sz (fun i => S.gap (φ i).val.variables))
    (ht : PolyIn sz (fun i => (tape i).length))
    (hct : PolyIn sz (fun i => (classifierTape i).length))
    (hs : PolyIn sz (fun i => S.producer.clock (EncodedCNF.encode (φ i).val)))
    (hraw : PolyIn sz (fun i => V42WRaw.clock (t10Graph D B (φ i)) (S.gap (φ i).val.variables)))
    (hentries : PolyIn sz (fun i => V42PublicSchedule.sampleEntries
      (Nat.clog 2 (t10Graph D B (φ i)).vertices) (S.gap (φ i).val.variables))) :
    PolyIn sz (fun i => ParametricSource.clock D B C S (φ i) (tape i) (classifierTape i)) := by
  have hsource := source_clock_poly D B S φ tape hx hk ht hs
  have hword := source_word_poly D B S φ tape hx hk ht hs
  have hfront : PolyIn sz (fun i => frontClock D B S (φ i) (tape i)) := by
    unfold frontClock
    simp only [EncodedComplexity.pair_length]
    repeat (first | exact const _ | exact hx | exact ht | exact hsource | exact hword | apply add | apply mul)
  have hfw : PolyIn sz (fun i => (frontWord D B S (φ i) (tape i) (classifierTape i)).length) := by
    unfold frontWord
    simp only [EncodedComplexity.pair_length]
    exact add (add (mul (const 2) hword) (const 1)) hct
  have hsize : PolyIn sz (fun i => ParametricSource.size D B S (φ i) (tape i) (classifierTape i)) := by
    change PolyIn sz (fun i => (sourceWord D B S (φ i) (tape i)).length+
      V42WRaw.clock (t10Graph D B (φ i)) (S.gap (φ i).val.variables)+
      V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B (φ i)).vertices)
        (S.gap (φ i).val.variables)+(classifierTape i).length+1)
    exact add (add (add (add hword hraw) hentries) hct) (const 1)
  exact add (add (add hfront (mul (const 2) hfw)) (const 2))
    (poly_apply (V42RawClassifierClock.cap_poly C) hsize)

theorem random_clock_poly (C : SelectedTape.Algorithm) (S : Schedule)
    (R : PhysicalConcat.Producer) (φ : ι → ValidFormula) (tape : ι → List Bool)
    (hx : PolyIn sz (fun i => (EncodedCNF.encode (φ i).val).length))
    (hk : PolyIn sz (fun i => S.gap (φ i).val.variables))
    (hs : PolyIn sz (fun i => S.producer.clock (EncodedCNF.encode (φ i).val)))
    (hR : PolyIn sz (fun i => R.clock (EncodedCNF.encode (φ i).val)))
    (hraw : PolyIn sz (fun i => V42WRaw.clock (t10Graph D B (φ i)) (S.gap (φ i).val.variables)))
    (hentries : PolyIn sz (fun i => V42PublicSchedule.sampleEntries
      (Nat.clog 2 (t10Graph D B (φ i)).vertices) (S.gap (φ i).val.variables))) :
    PolyIn sz (fun i => randomClock D B C S R (φ i) (tape i)) := by
  let x := fun i => EncodedCNF.encode (φ i).val
  let first := fun i => (tape i).take (blockLength R (x i))
  let second := fun i => ((tape i).take (carrierLength R (x i))).drop (blockLength R (x i))
  have hl := block_length_poly R x hx hR
  have hc := carrier_length_poly R x hx hR
  have hf : PolyIn sz (fun i => (first i).length) :=
    mono (fun i => List.length_take_le _ _) hl
  have hsnd : PolyIn sz (fun i => (second i).length) := by
    apply mono (fun i => ?_) hc
    dsimp [second]
    rw [List.length_drop]
    exact (Nat.sub_le _ _).trans (List.length_take_le _ _)
  have hsplit : PolyIn sz (fun i => (splitWord R (x i) (tape i)).length) := by
    change PolyIn sz (fun i => (EncodedComplexity.pair (EncodedComplexity.pair (x i) (first i)) (second i)).length)
    simp only [EncodedComplexity.pair_length]
    repeat (first | exact const _ | exact hx | exact hf | exact hsnd | apply add | apply mul)
  exact add (add (add (split_clock_poly R x hx hR) (mul (const 2) hsplit)) (const 2))
    (caller_clock_poly D B C S φ first second hx hk hf hsnd hs hraw hentries)

#print axioms split_clock_poly
#print axioms source_clock_poly
#print axioms caller_clock_poly
#print axioms random_clock_poly
end
end CurrentV43.ResourceFit
