import CurrentAdditive.FeatureInnerReady96

/-! The actual outer-bank preparation followed by the entire alphabet scan.
All five data words are copied from live outer registers. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeaturePreparedAlphabet96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureBoundedLift96
open CurrentAdditive.FeatureInnerReady96

def program := BitMachineRawSequence.program
  FeatureInnerPrep96.program liftedProgram (.inr (.inr .check))
  FeatureInnerPrep96.control innerControl

private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def start := labelFor program
  (BitMachineRawSequence.leftLabel FeatureInnerPrep96.start)
def control := (FeatureInnerPrep96.control,innerControl)

def copyClock (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : Nat :=
  2*((SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length+
    body.length+j.bits.length+ys.length+(CylinderFeatureCodec.encodeFeature c).length)+14

def clock (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) := copyClock j c ys body+scanClock j c ys body+1

theorem run (S : Fin 96 → List Bool) (j : Nat)
    (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool)
    (h30 : S 30 = SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys))
    (h9 : S 9 = body) (h15 : S 15 = j.bits)
    (h31 : S 31 = List.replicate ys.length true)
    (h6 : S 6 = CylinderFeatureCodec.encodeFeature c) (h16 : S 16 = [])
    (hhigh : ∀ k : Fin 96, 32 ≤ k.val → S k = []) :
    ∃ t ≤ clock j c ys body,
      let z := ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _)
      z.l=none ∧ z.stk 41=body++SourceListEncoding.fields
        (ys.map (fun y => CylinderFeatureCodec.encodeFeature ((j,y)::c))) ∧
      (∀ k : Fin 96, k.val<32 → z.stk k=S k) := by
  classical
  have hs : ∀ i : Fin 5, S (![30,9,15,31,6] i)=values j c ys body i := by
    intro i
    fin_cases i <;> simp [values,h30,h9,h15,h31,h6]
  have ht : ∀ i : Fin 5, S (![40,41,44,45,47] i)=[] := by
    intro i
    fin_cases i <;> apply hhigh <;> decide
  obtain ⟨a,ha,hr⟩ := FeatureInnerPrep96.run S (values j c ys body) hs ht h16
  obtain ⟨b,hb,hh,ho,hp⟩ := lifted_alphabet_scan S j c ys body
  let z := ((advance liftedProgram)^[b]) (liftedStart S j c ys body)
  have hz : z=⟨none,z.var,z.stk⟩ := by
    have hhalt : z.l=none := hh
    cases h : z with
    | mk l v T => cases l with
      | none => rfl
      | some l => simp [h] at hhalt
  have h2 := hz
  change ((advance liftedProgram)^[b]) (liftedStart S j c ys body) =
    ⟨none,z.var,z.stk⟩ at h2
  rw [start_fixed S j c ys body hhigh] at h2
  obtain ⟨t,ht,hseq⟩ := BitMachineRawSequence.runs
    FeatureInnerPrep96.program liftedProgram
    FeatureInnerPrep96.start (.inr (.inr .check))
    FeatureInnerPrep96.control FeatureInnerPrep96.control innerControl z.var
    S (FeatureInnerPrep96.after S (values j c ys body)) z.stk a b hr h2
  refine ⟨t,by unfold clock copyClock; simp [values] at ha; omega,?_,?_,?_⟩
  · simpa only [program,start,control] using congrArg TM2.Cfg.l hseq
  · have he := congrArg (fun w => w.stk (41 : Fin 96)) hseq
    exact he.trans ho
  · intro k hk
    have he := congrArg (fun w => w.stk k) hseq
    exact he.trans (hp k hk)

#print axioms run
end CurrentAdditive.FeaturePreparedAlphabet96
