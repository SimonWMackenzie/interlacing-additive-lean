import CurrentAdditive.RawBankParser
import CurrentAdditive.RatioBranchPolynomial
import CurrentAdditive.GaussCertificateVectorABI

namespace CurrentAdditive.RatioBranchPacketMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxSize 16384
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open RatioBranchLayout RatioCanonicalRequests
open MinimumRatioCallbackLayout

abbrev Stack:=BigStack ⊕ Fin 3
def sourceSlot : BigStack:=core (low 8)
def coeffSlot : BigStack:=core (low 12)
def resultSlot : BigStack:=core (low 24)
theorem source_coeff_ne : sourceSlot≠coeffSlot := by
  intro h
  have h': (8:Fin 32)=12 := by
    apply Fin.ext
    have hv:=congrArg (fun x : BigStack => x.val) h
    exact hv
  cases h'

def parseMap : Fin 2 ⊕ Fin 3 → Stack
  | .inl i => if i=0 then .inl sourceSlot else .inl coeffSlot
  | .inr i => .inr i
def parseSlots : (Fin 2 ⊕ Fin 3) ↪ Stack:=⟨parseMap,by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [parseMap,source_coeff_ne,Ne.symm source_coeff_ne]
    | inr b => fin_cases a <;> simp [parseMap] at h
  | inr a => cases b with
    | inl b => fin_cases b <;> simp [parseMap] at h
    | inr b => simpa only [parseMap,Sum.inr.injEq] using h⟩
def bodySlots : BigStack ↪ Stack:=⟨Sum.inl,Sum.inl_injective⟩
def parserProgram:=RawBankParser.program parseSlots
def bodyProgram l:=BitMachineStackEmbedding.stackStmt bodySlots (RatioBranchLayout.program l)
abbrev Label:=BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2) RatioBranchLayout.Label
def program:=BitMachineRawSequence.program parserProgram bodyProgram RatioBranchLayout.start none RatioBranchLayout.control
def start : Label:=BitMachineRawSequence.leftLabel (.scan 0)
def control:=((none : Option Bool),RatioBranchLayout.control)
def inputCell : Stack:=.inr 0
def outputCell : Stack:=.inl resultSlot
def machine : BitMachine.Machine:=ofFinite inputCell outputCell start control program

def words {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) : Fin 2 → List Bool:=
  ![SourceListEncoding.encode (records source),SourceListEncoding.encode (coeffWords coeff)]

theorem words_source {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    words source coeff 0=CodeDCanonicalSourceV2.encodedSource source:=by
  simp [words,records,CodeDCanonicalSourceV2.encodedSource,CodeDCanonicalSourceV2.canonicalSource,
    CodeDSourceCodecV2.encodeSource,CodeDCodecV2.encodeItems,List.map_map,Function.comp_def]
theorem words_coeff {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    words source coeff 1=GaussCertificateVectorABI.vectorPacket coeff:=rfl

theorem initial_local {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    RatioBranchRun.initialBank source coeff=
      Function.update (Function.update (fun _ : MinimumRatioCallbackLayout.Stack => []) (low 8)
        (words source coeff 0)) (low 12) (words source coeff 1) := by
  funext j
  have mod_small (n : Nat) (hn : n < 32) : n % (32+extraCount)=n := Nat.mod_eq_of_lt (by omega)
  simp [RatioBranchRun.initialBank,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
    StatefulListScheduler.initialBank,RatioPhysicalFold.blank,Function.update_apply,low,
    Fin.ext_iff,Fin.ofNat,mod_small 8 (by omega),mod_small 9 (by omega),
    mod_small 10 (by omega),mod_small 12 (by omega),mod_small 13 (by omega),
    words]
  split_ifs <;> simp_all <;> omega

theorem parsed_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    RawBankParser.parsed parseSlots (words source coeff)=
      BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => [])
        (RatioBranchLayout.frame (RatioBranchRun.initialBank source coeff)) := by
  have hlocal : (BitMachineBankCodec.parserCfg (K:=2) none (some true)
      (words source coeff) [] [] []).stk=
      Function.update (Function.update (fun _ : Fin 2 ⊕ Fin 3 => []) (.inl 0)
        (words source coeff 0)) (.inl 1) (words source coeff 1) := by
    funext j
    cases j with
    | inl j => fin_cases j <;> simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr j => fin_cases j <;> simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hemptyP : BitMachineStackEmbedding.bank parseSlots (fun _ : Stack => []) (fun _ => [])=
      (fun _ : Stack => []) :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hemptyC : BitMachineStackEmbedding.bank core (fun _ : BigStack => []) (fun _ => [])=
      (fun _ : BigStack => []) :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hemptyB : BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => []) (fun _ => [])=
      (fun _ : Stack => []) :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  unfold RawBankParser.parsed
  rw [hlocal,BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update,hemptyP]
  rw [initial_local,RatioBranchLayout.frame_update,RatioBranchLayout.frame_update]
  unfold RatioBranchLayout.frame
  rw [hemptyC,BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update,hemptyB]
  rfl

def coefficient : Nat:=Classical.choose RatioBranchPolynomial.uniform_run
def exponent : Nat:=Classical.choose (Classical.choose_spec RatioBranchPolynomial.uniform_run)
def clock (n : Nat) : Nat:=5*(n+1)+coefficient*(n+1)^exponent+1

theorem inputSize_le {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    RatioBranchPolynomial.inputSize source coeff ≤ (BitMachineBankCodec.encode (words source coeff)).length := by
  rw [BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_two,words,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold RatioBranchPolynomial.inputSize RatioListClockBounds.inputLength
  simp only [List.length_nil]
  omega

theorem outputs {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
    (hsize : coeff.size=source.size)
    (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w))=true) :
    machine.OutputsWithin (BitMachineBankCodec.encode (words source coeff))
      (CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
        (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))
      (clock (BitMachineBankCodec.encode (words source coeff)).length) := by
  let w:=words source coeff
  obtain ⟨a,ha,hparse⟩:=RawBankParser.physical_parse parseSlots w
  obtain ⟨b,hb,hhalt,hout⟩:=Classical.choose_spec (Classical.choose_spec RatioBranchPolynomial.uniform_run)
    source coeff lambda hsize hmin hnonneg
  let initial : TM2.Cfg (fun _ : BigStack => Bool) _ _:=
    ⟨some RatioBranchLayout.start,RatioBranchLayout.control,frame (RatioBranchRun.initialBank source coeff)⟩
  let final:=((advance RatioBranchLayout.program)^[b]) initial
  have hf : final.l=none:=hhalt
  have ho : final.stk resultSlot=CodeDCanonicalSourceV2.encodedSource
      (CodeDCompactSequentialBridge.retainedSource source
        (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)):=hout
  have hbody:=BitMachineStackRun.run bodySlots (fun _ : Stack => []) RatioBranchLayout.program initial b
  change ((advance bodyProgram)^[b])
    ⟨some RatioBranchLayout.start,RatioBranchLayout.control,
      BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => [])
        (frame (RatioBranchRun.initialBank source coeff))⟩=
    ⟨final.l,final.var,BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => []) final.stk⟩ at hbody
  rw [hf,←parsed_exact] at hbody
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs parserProgram bodyProgram
    (.scan 0) RatioBranchLayout.start none (some true) RatioBranchLayout.control final.var
    (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none : Option Bool)
      (BitMachineBankCodec.encode w)).stk (RawBankParser.parsed parseSlots w)
    (BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => []) final.stk) a b hparse hbody
  have hfull : ((advance program)^[t]) (rawInit inputCell start control (BitMachineBankCodec.encode w))=
      ⟨none,(none,final.var),BitMachineStackEmbedding.bank bodySlots (fun _ : Stack => []) final.stk⟩:=he
  have hsize':=inputSize_le source coeff
  change b ≤ coefficient*(RatioBranchPolynomial.inputSize source coeff+1)^exponent at hb
  have hb' : b ≤ coefficient*((BitMachineBankCodec.encode w).length+1)^exponent := by
    apply hb.trans
    dsimp only [w]
    gcongr
  apply outputsWithin_of_raw_run inputCell outputCell start control program
    (BitMachineBankCodec.encode w) _ t _ (by unfold clock; dsimp only [w] at *; omega)
  · change (((advance program)^[t]) _).l=none
    exact congrArg TM2.Cfg.l hfull
  · change (((advance program)^[t]) _).stk outputCell=_
    exact (congrArg (fun c => c.stk outputCell) hfull).trans
      ((BitMachineStackEmbedding.bank_at bodySlots (fun _ : Stack => []) final.stk resultSlot).trans ho)

def polynomialClock (n : Nat) : Nat:=(coefficient+6)*(n+1)^(exponent+1)
theorem clock_le_polynomial (n : Nat) : clock n ≤ polynomialClock n := by
  have hlin : n+1 ≤ (n+1)^(exponent+1):=Nat.le_self_pow (by omega) (n+1)
  have hp : (n+1)^exponent ≤ (n+1)^(exponent+1):=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hterm:=Nat.mul_le_mul_left coefficient hp
  unfold clock polynomialClock
  nlinarith

theorem outputs_polynomial {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
    (hsize : coeff.size=source.size)
    (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w))=true) :
    machine.OutputsWithin (BitMachineBankCodec.encode ![CodeDCanonicalSourceV2.encodedSource source,
        GaussCertificateVectorABI.vectorPacket coeff])
      (CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
        (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))
      (polynomialClock (BitMachineBankCodec.encode ![CodeDCanonicalSourceV2.encodedSource source,
        GaussCertificateVectorABI.vectorPacket coeff]).length) := by
  have hw : words source coeff=![CodeDCanonicalSourceV2.encodedSource source,
      GaussCertificateVectorABI.vectorPacket coeff] := by
    funext j
    fin_cases j
    · exact words_source source coeff
    · exact words_coeff source coeff
  have hout:=BitMachine.outputsWithin_mono machine (outputs source coeff lambda hsize hmin hnonneg)
    (clock_le_polynomial (BitMachineBankCodec.encode (words source coeff)).length)
  simpa only [hw] using hout

#print axioms parsed_exact
#print axioms outputs
#print axioms outputs_polynomial
end
end CurrentAdditive.RatioBranchPacketMachine
