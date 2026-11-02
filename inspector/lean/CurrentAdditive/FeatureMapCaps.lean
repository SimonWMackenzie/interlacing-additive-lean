import CurrentAdditive.FeatureMapSizeBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureMapCaps
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussListContext FeatureMapPairLoader FeatureMapInvoke FeatureMapSizeBounds
open CurrentAdditive.MinimumRatioContext EntryClockPoly

def invokeCap (M : BitMachine.Machine) (L T : Nat) :=
  (2*L+2)+T+(2*(L+T*M.pushBound)+2)+
    (M.stackCount*(L+T*M.pushBound)+M.stackCount+2)+3

theorem invoke_le (M : BitMachine.Machine) (bits : List Bool) (T L U : Nat)
    (hL : bits.length ≤ L) (hT : T ≤ U) :
    MachineInvokeFull.uniformBound M bits T ≤ invokeCap M L U := by
  unfold MachineInvokeFull.uniformBound invokeCap
  gcongr

theorem invoke_poly {ι : Type*} (U : ι → Nat) (M : BitMachine.Machine)
    (L T : ι → Nat) (hL : PolyIn U L) (hT : PolyIn U T) :
    PolyIn U (fun i => invokeCap M (L i) (T i)) := by
  unfold invokeCap
  exact (((((PolyIn.const 2).mul hL).add (PolyIn.const 2)).add hT).add
    (((PolyIn.const 2).mul (hL.add (hT.mul (PolyIn.const M.pushBound)))).add (PolyIn.const 2))).add
      ((((PolyIn.const M.stackCount).mul (hL.add (hT.mul (PolyIn.const M.pushBound)))).add
        (PolyIn.const M.stackCount)).add (PolyIn.const 2)) |>.add (PolyIn.const 3)

def pieceCap (n : Nat) := 3*n+1
def outputCap (n : Nat) := 2*n+1+n*(3*n+1)
def timeCap (n : Nat) := n+2*n+2+(UnaryBinaryEncoding.coefficient+7)*(n+1)^2
def countTimeCap (n : Nat) := 20*(n+1)
def headerTimeCap (n : Nat) := (UnaryBinaryEncoding.coefficient+7)*(n+1)^2+1

def loadedCap (M : BitMachine.Machine) (framed : Bool) (n : Nat) :=
  4*n+6+invokeCap (evaluator M framed) n (timeCap n)
def coreCap (M : BitMachine.Machine) (framed : Bool) (n : Nat) :=
  loadedCap M framed n+(4*outputCap n+2*pieceCap n+7)+1
def callbackCap (M : BitMachine.Machine) (framed : Bool) (n : Nat) :=
  n+1+coreCap M framed n
def cycleCap (M : BitMachine.Machine) (framed : Bool) (n : Nat) :=
  50*(n+1)^3+callbackCap M framed n+2*n+14
def initializeCap (framed : Bool) (n : Nat) :=
  5*(n+1)+invokeCap FeatureMapListCount.machine n (countTimeCap n)+1+
    invokeCap (FeatureMapHeaders.machine framed) n (headerTimeCap n)+1
def fullCap (M : BitMachine.Machine) (framed : Bool) (n : Nat) :=
  initializeCap framed n+(n+1)*(cycleCap M framed n+1)+1

theorem itemTime_le (framed : Bool) (answer : List Bool) (T n : Nat)
    (hQ : answer.length ≤ n) (hT : T ≤ n) :
    FeatureMapInvoke.itemTime framed answer T ≤ timeCap n := by
  cases framed
  · change T ≤ timeCap n
    unfold timeCap
    omega
  · change T+2*answer.length+2+(UnaryBinaryEncoding.coefficient+7)*(answer.length+1)^2 ≤ _
    unfold timeCap
    gcongr <;> omega

theorem callback_le (M : BitMachine.Machine) (framed : Bool)
    (context word output answer : List Bool) (T n : Nat)
    (hc : context.length ≤ n) (hw : word.length ≤ n)
    (hp : (packet context word).length ≤ n) (ho : output.length ≤ outputCap n)
    (ha : answer.length ≤ n) (hT : T ≤ n) :
    ContextMapClockModel.callbackCap M framed context word output answer T ≤ callbackCap M framed n := by
  have hb : FeatureMapInvoke.budget M framed (packet context word) answer T ≤
      invokeCap (evaluator M framed) n (timeCap n) :=
    invoke_le _ _ _ _ _ hp (itemTime_le framed answer T n ha hT)
  have hpiece : (FeatureMapInvoke.piece framed answer).length ≤ pieceCap n :=
    (piece_length framed answer).trans (by unfold pieceCap; omega)
  unfold ContextMapClockModel.callbackCap FeatureMapAppend.coreBudget FeatureMapInvoke.loadedBudget
    callbackCap coreCap loadedCap
  omega

theorem cycle_le (M : BitMachine.Machine) (framed : Bool) (context : List Bool)
    (xs pre : List (List Bool)) (w : List Bool) (suf : List (List Bool))
    (hs : pre++w::suf=xs) (f : List Bool → List Bool) (b : List Bool → Nat)
    (P Q n : Nat) (hP : ∀ w∈xs,b w ≤ P) (hQ : ∀ w∈xs,(f w).length ≤ Q)
    (hL : inputSize context xs ≤ n) (hPn : P ≤ n) (hQn : Q ≤ n) :
    ContextMapClockModel.cycleCap M framed context (FeatureMapHeaders.output framed xs.length)
      f b pre w suf ≤ cycleCap M framed n := by
  obtain ⟨hc,hsource,hcount⟩ := basic_bounds context xs
  obtain ⟨hp,hfields,hpacket,hword⟩ := cut_bounds context xs pre w suf hs
  have hw : w∈xs := by rw [←hs]; simp
  have hout := prefix_output framed context xs pre w suf hs f Q hQ
  have hout' : (FeatureMapHeaders.output framed xs.length++
      FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre).length ≤ outputCap n := by
    apply hout.trans
    unfold outputCap
    gcongr <;> omega
  have hcallback := callback_le M framed context w _ (f w) (b w) n
    (hc.trans hL) (hword.trans hL) (hpacket.trans hL) hout' ((hQ w hw).trans hQn) ((hP w hw).trans hPn)
  have hgetter := StatefulListScheduler.getterBudget_cubic pre w suf
  rw [hs] at hgetter
  have hgetter' : StatefulListScheduler.getterBudget pre w suf ≤ 50*(n+1)^3 := by
    apply hgetter.trans
    gcongr <;> omega
  unfold ContextMapClockModel.cycleCap cycleCap
  omega

theorem initialize_le (framed : Bool) (context : List Bool) (xs : List (List Bool))
    (n : Nat) (hL : inputSize context xs ≤ n) :
    FeatureMapInitialize.budget framed context xs ≤ initializeCap framed n := by
  obtain ⟨hc,hsource,hcount⟩ := basic_bounds context xs
  have hcountTime : FeatureMapListCount.bound xs.length (SourceListEncoding.encode xs) ≤ countTimeCap n :=
    FeatureMapListCount.bound_le _ _ _ (hcount.trans hL) (hsource.trans hL)
  have hheaderTime : FeatureMapHeaders.bound framed xs.length ≤ headerTimeCap n := by
    cases framed
    · change 1 ≤ headerTimeCap n
      unfold headerTimeCap
      omega
    · change (UnaryBinaryEncoding.coefficient+7)*(xs.length+1)^2 ≤ headerTimeCap n
      unfold headerTimeCap
      have h := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+7)
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hcount.trans hL) 1) 2)
      omega
  have h1 := invoke_le FeatureMapListCount.machine (SourceListEncoding.encode xs) _ n
    (countTimeCap n) (hsource.trans hL) hcountTime
  have h2 := invoke_le (FeatureMapHeaders.machine framed) (List.replicate xs.length true) _ n
    (headerTimeCap n) (by simpa using hcount.trans hL) hheaderTime
  unfold FeatureMapInitialize.budget initializeCap
  change (packet context (SourceListEncoding.encode xs)).length ≤ n at hL
  omega

#print axioms cycle_le
#print axioms initialize_le
end CurrentAdditive.FeatureMapCaps
