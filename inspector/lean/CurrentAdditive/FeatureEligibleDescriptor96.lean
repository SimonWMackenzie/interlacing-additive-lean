import CurrentAdditive.FeaturePreparedAlphabet96
import CurrentAdditive.FeatureCommit96

/-! One complete physical eligible-descriptor step. It reads the actual
retained alphabet, appends every extension in indexed order, updates the
unary descriptor count, and clears the whole inner scanner bank. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CurrentAdditive.FeatureEligibleDescriptor96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def p01 := BitMachineRawSequence.program
  FeaturePreparedAlphabet96.program FeatureOutputTransfer96.transferProgram
  (BitMachineRawSequence.leftLabel FeatureOutputTransfer96.ClearLabel.scan)
  FeaturePreparedAlphabet96.control ((((),none),none) : (Unit × Option Bool) × Option Bool)

def p01Start := labelFor p01
  (BitMachineRawSequence.leftLabel FeaturePreparedAlphabet96.start)
def p01Control := (FeaturePreparedAlphabet96.control,
  ((((),none),none) : (Unit × Option Bool) × Option Bool))

def beforeClear := BitMachineRawSequence.program p01 FeatureCountAppend96.program
  BitMachineCopy.Label.scan p01Control (none : Option Bool)

def prefixStart := labelFor beforeClear (BitMachineRawSequence.leftLabel p01Start)
def prefixControl := (p01Control,(none : Option Bool))

def program := BitMachineRawSequence.program beforeClear FeatureClearInner96.program
  (MachineInvokeClear.clearLabel 64 0) prefixControl (((),none) : Unit × Option Bool)

def start := labelFor program (BitMachineRawSequence.leftLabel prefixStart)
def control := (prefixControl,(((),none) : Unit × Option Bool))

def extensions (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) : List Bool :=
  SourceListEncoding.fields
    (ys.map (fun y => CylinderFeatureCodec.encodeFeature ((j,y)::c)))

def prefixClock (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : Nat :=
  FeaturePreparedAlphabet96.clock j c ys body+
    (body.length+2+2*(body++extensions j c ys).length+2+1)+
    (2*ys.length+2)+2

def clock (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : Nat :=
  prefixClock j c ys body+
    64*BitMachineStackGrowth.perStep beforeClear*prefixClock j c ys body+67

theorem clear_after_run {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (cfg : TM2.Cfg (fun _ : Fin 96 => Bool) L V)
    (T t : Nat) (ht : t≤T)
    (hblank : ∀ i : Fin 64, cfg.stk (FeatureClearInner96.high i)=[]) :
    FeatureClearInner96.time (((advance P)^[t]) cfg).stk ≤
      64*BitMachineStackGrowth.perStep P*T+66 := by
  classical
  have hlen (i : Fin 64) :
      ((((advance P)^[t]) cfg).stk (FeatureClearInner96.high i)).length ≤
        BitMachineStackGrowth.perStep P*T := by
    have hg := BitMachineStackGrowth.run_growth P cfg t (FeatureClearInner96.high i)
    rw [hblank i,List.length_nil,Nat.zero_add] at hg
    exact hg.trans (Nat.mul_le_mul_left _ ht)
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => hlen i)
  unfold FeatureClearInner96.time
  simpa only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.mul_assoc] using
    Nat.add_le_add_right hs 66

theorem run (S : Fin 96 → List Bool) (j : Nat)
    (c : List (Nat × Nat)) (ys : List Nat) (body count : List Bool)
    (h30 : S 30=SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys))
    (h9 : S 9=body) (h12 : S 12=count) (h15 : S 15=j.bits)
    (h31 : S 31=List.replicate ys.length true)
    (h6 : S 6=CylinderFeatureCodec.encodeFeature c) (h16 : S 16=[])
    (hhigh : ∀ k : Fin 96, 32≤k.val → S k=[]) :
    ∃ t ≤ clock j c ys body,
      let z := ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _)
      z.l=none ∧ z.stk 9=body++extensions j c ys ∧
      z.stk 12=List.replicate ys.length true++count ∧
      (∀ k : Fin 96, k.val<32 → k≠9 → k≠12 → z.stk k=S k) ∧
      (∀ k : Fin 96, 32≤k.val → z.stk k=[]) := by
  classical
  obtain ⟨a,ha,hh,ho,hp⟩ := FeaturePreparedAlphabet96.run S j c ys body
    h30 h9 h15 h31 h6 h16 hhigh
  let z := ((advance FeaturePreparedAlphabet96.program)^[a])
    (⟨some FeaturePreparedAlphabet96.start,FeaturePreparedAlphabet96.control,S⟩ :
      TM2.Cfg (fun _ : Fin 96 => Bool) _ _)
  have hz : z=⟨none,z.var,z.stk⟩ := by
    have hhalt : z.l=none := hh
    cases he : z with
    | mk l v T => cases l with
      | none => rfl
      | some l => simp [he] at hhalt
  let T := z.stk
  have hT41 : T 41=body++extensions j c ys := ho
  have hT16 : T 16=[] := (hp 16 (by decide)).trans h16
  obtain ⟨b,hb,hbRun⟩ := FeatureCommit96.transfer_exact T
    (body++extensions j c ys) hT41 hT16
  let U := Function.update T (9 : Fin 96) (body++extensions j c ys)
  have hU31 : U 31=List.replicate ys.length true := by
    simpa [U] using (hp 31 (by decide)).trans h31
  have hU12 : U 12=count := by simpa [U] using (hp 12 (by decide)).trans h12
  have hU16 : U 16=[] := by simpa [U] using hT16
  obtain ⟨d,hd,hdRun⟩ := FeatureCommit96.count_exact U
    (List.replicate ys.length true) count hU31 hU12 hU16
  let V := Function.update U (12 : Fin 96) (List.replicate ys.length true++count)
  obtain ⟨ab,hab,habRun⟩ := BitMachineRawSequence.runs
    FeaturePreparedAlphabet96.program FeatureOutputTransfer96.transferProgram
    FeaturePreparedAlphabet96.start
    (BitMachineRawSequence.leftLabel FeatureOutputTransfer96.ClearLabel.scan)
    FeaturePreparedAlphabet96.control z.var
    ((((),none),none) : (Unit × Option Bool) × Option Bool)
    ((((),none),none) : (Unit × Option Bool) × Option Bool)
    S T U a b hz hbRun
  obtain ⟨v,hv,hvRun⟩ := BitMachineRawSequence.runs
    p01 FeatureCountAppend96.program p01Start BitMachineCopy.Label.scan
    p01Control p01Control (none : Option Bool) (none : Option Bool)
    S U V ab d
    (by simpa only [p01,p01Start,labelFor,p01Control] using habRun)
    hdRun
  have hT9 : (T 9).length=body.length := congrArg List.length ((hp 9 (by decide)).trans h9)
  have hvBound : v≤prefixClock j c ys body := by
    unfold prefixClock
    simp only [List.length_replicate] at hd
    omega
  have hc := clear_after_run beforeClear
    (((advance beforeClear)^[0]) ⟨some prefixStart,prefixControl,S⟩)
    (prefixClock j c ys body) v hvBound
    (fun i => hhigh _ (by simp [FeatureClearInner96.high,FeatureBoundedLift96.slot]))
  change FeatureClearInner96.time (((advance beforeClear)^[v])
    ⟨some prefixStart,prefixControl,S⟩).stk ≤ _ at hc
  have hvRun' : ((advance beforeClear)^[v])
      ⟨some prefixStart,prefixControl,S⟩=⟨none,prefixControl,V⟩ := by
    simpa only [beforeClear,prefixStart,labelFor,prefixControl] using hvRun
  rw [hvRun'] at hc
  change FeatureClearInner96.time V≤_ at hc
  obtain ⟨t,ht,hfinal⟩ := BitMachineRawSequence.runs
    beforeClear FeatureClearInner96.program prefixStart
    (MachineInvokeClear.clearLabel 64 0)
    prefixControl prefixControl (((),none) : Unit × Option Bool)
    (((),none) : Unit × Option Bool)
    S V (FeatureClearInner96.cleaned V) v (FeatureClearInner96.time V)
    hvRun' (FeatureClearInner96.run V)
  refine ⟨t,by unfold clock; omega,?_,?_,?_,?_,?_⟩
  · simpa only [program,start,labelFor,control] using congrArg TM2.Cfg.l hfinal
  · have he := congrArg (fun w => w.stk (9 : Fin 96)) hfinal
    simpa [FeatureClearInner96.cleaned_low V 9 (by decide),V,U] using he
  · have he := congrArg (fun w => w.stk (12 : Fin 96)) hfinal
    simpa [FeatureClearInner96.cleaned_low V 12 (by decide),V] using he
  · intro k hk hk9 hk12
    have he := congrArg (fun w => w.stk k) hfinal
    have he' : FeatureClearInner96.cleaned V k=T k := by
      rw [FeatureClearInner96.cleaned_low V k hk]
      simp [V,U,hk9,hk12]
    exact (he.trans he').trans (hp k hk)
  · intro k hk
    have he := congrArg (fun w => w.stk k) hfinal
    exact he.trans (FeatureClearInner96.cleaned_high V k hk)

#print axioms run
end CurrentAdditive.FeatureEligibleDescriptor96
