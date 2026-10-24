import CurrentAdditive.GaussPostloopSerialized

namespace CurrentAdditive.GaussPostloopMachine
noncomputable section

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open GaussPostloopSerialized GaussFirstFreeCandidate GaussCertificateVectorABI

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

private abbrev ProgramControl {K L V : Type} (_ : L → TM2.Stmt (fun _ : K => Bool) L V) := V
abbrev Control := ProgramControl GaussPostloopSerialized.program

instance : Fintype GaussPostloopSerialized.Label := by infer_instance
instance : Fintype Control := by infer_instance

def machine : BitMachine.Machine :=
  ofFinite inputCell outputCell start GaussPostloopSerialized.control GaussPostloopSerialized.program

theorem body_bank (S : GaussWideVectorInvoke.Bank → List Bool) :
    BitMachineStackEmbedding.bank bodySlots (fun _ => []) S=Sum.elim S (fun _ => []) := by
  funext z
  cases z with
  | inl b => exact BitMachineStackEmbedding.bank_at bodySlots (fun _ => []) S b
  | inr b =>
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨i,hi⟩
    cases hi

theorem actual_raw_run {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (fun i j => (A i j:ℚ)) k).pivots≠none) :
    let s := GaussControlTrace.after (fun i j => (A i j:ℚ)) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat),
      SequentialTotality.typedFree s.pivots=some f ∧
      t≤5*((packet (GaussControlTrace.statePacket s) k).length+1)+GaussAnyWidthVector.totalClock s f+1 ∧
      postloopPacket s.B s.pivots=some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
      (((advance GaussPostloopSerialized.program)^[t])
        (rawInit inputCell start GaussPostloopSerialized.control
          (packet (GaussControlTrace.statePacket s) k))).l=none ∧
      (((advance GaussPostloopSerialized.program)^[t])
        (rawInit inputCell start GaussPostloopSerialized.control
          (packet (GaussControlTrace.statePacket s) k))).stk outputCell=
        vectorPacket (Array.ofFn (directCandidate s.B f hf)) := by
  let s := GaussControlTrace.after (fun i j => (A i j:ℚ)) k
  let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
  obtain ⟨f,hf,b,T,hfree,hb,hbody⟩:=GaussAnyWidthVector.actual_vector_fused A h01 hdependent
  let out:=vectorPacket (Array.ofFn (directCandidate s.B f hf))
  let c : TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _ :=
    ⟨some GaussWideVectorInvoke.start,GaussWideVectorInvoke.control,GaussWideVectorInvoke.wide S⟩
  have hr : ((advance GaussWideVectorInvoke.program)^[b]) c=
      ⟨none,GaussWideVectorInvoke.control,
        Function.update (GaussWideVectorInvoke.wide T) GaussWideVectorInvoke.slots.target out⟩ := hbody
  obtain ⟨u,hu,hlift⟩:=BitMachineStackEmbedding.outputs bodySlots (fun _ => []) id id id
    (by intro; rfl) none GaussWideVectorInvoke.program bodyProgram (by intro; rfl)
    c b (by rw [hr])
  rw [hr] at hlift
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq,c,body_bank] at hlift
  obtain ⟨a,ha,hparse⟩:=parse_run (words (GaussControlTrace.statePacket s) k)
  rw [parsed_exact] at hparse
  have hbody' : ((advance bodyProgram)^[u])
      (⟨some GaussWideVectorInvoke.start,GaussWideVectorInvoke.control,
        installed (GaussControlTrace.statePacket s) k⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _)=
      ⟨none,GaussWideVectorInvoke.control,
        Sum.elim (Function.update (GaussWideVectorInvoke.wide T) GaussWideVectorInvoke.slots.target out)
          (fun _ => [])⟩ := hlift
  obtain ⟨t,ht,hfull⟩:=BitMachineRawSequence.runs parserProgram bodyProgram
    (.scan 0) GaussWideVectorInvoke.start (none:Option Bool) (some true)
    GaussWideVectorInvoke.control GaussWideVectorInvoke.control
    (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none:Option Bool)
      (packet (GaussControlTrace.statePacket s) k)).stk
    (installed (GaussControlTrace.statePacket s) k)
    (Sum.elim (Function.update (GaussWideVectorInvoke.wide T) GaussWideVectorInvoke.slots.target out)
      (fun _ => [])) a u hparse hbody'
  have hfull' : ((advance GaussPostloopSerialized.program)^[t])
      (rawInit inputCell start GaussPostloopSerialized.control
        (packet (GaussControlTrace.statePacket s) k))=
      ⟨none,((none:Option Bool),GaussWideVectorInvoke.control),
        Sum.elim (Function.update (GaussWideVectorInvoke.wide T) GaussWideVectorInvoke.slots.target out)
          (fun _ => [])⟩ := hfull
  refine ⟨f,hf,t,hfree,?_,?_,?_,?_⟩
  · dsimp only [packet,s] at ha hb ⊢
    omega
  · exact GaussAnyWidthCertificate.firstFree_vector_is_postloop
      (fun i j => (A i j:ℚ)) hdependent f hf hfree
  · rw [hfull']
  · rw [hfull']
    simp [outputCell,out,s]

theorem actual_outputs {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j=0 ∨ A i j=1)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (fun i j => (A i j:ℚ)) k).pivots≠none) :
    let s := GaussControlTrace.after (fun i j => (A i j:ℚ)) k
    ∃ (f : Fin k) (hf : f.val ≤ m),
      SequentialTotality.typedFree s.pivots=some f ∧
      postloopPacket s.B s.pivots=some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
      machine.OutputsWithin (packet (GaussControlTrace.statePacket s) k)
        (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
        (5*((packet (GaussControlTrace.statePacket s) k).length+1)+GaussAnyWidthVector.totalClock s f+1) := by
  obtain ⟨f,hf,t,hfree,ht,hcert,hhalt,hout⟩:=actual_raw_run A h01 hdependent
  refine ⟨f,hf,hfree,hcert,?_⟩
  exact outputsWithin_of_raw_run inputCell outputCell start GaussPostloopSerialized.control
    GaussPostloopSerialized.program _ _ t _ ht hhalt hout

#print axioms actual_raw_run
#print axioms actual_outputs

end
end CurrentAdditive.GaussPostloopMachine
