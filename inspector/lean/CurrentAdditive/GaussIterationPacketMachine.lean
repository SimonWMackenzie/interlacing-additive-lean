import CurrentAdditive.GaussWholeIteration
import EthInapproximability.CurrentPaper.BitMachineRawSequence

namespace CurrentAdditive.GaussIterationPacketMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
abbrev M:=GaussWholeStepProgram.machine
abbrev Stack:=BitMachineIteration.Stack M ⊕ Fin 3
def inputCell : Stack:=.inr 0
def outputCell : Stack:=.inl (.inl M.input)
def parseMap : Fin 2 ⊕ Fin 3 → Stack
  | .inl i => if i=0 then .inl (.inl M.input) else .inl (.inr 0)
  | .inr i => .inr i
def parseSlots : (Fin 2 ⊕ Fin 3) ↪ Stack:=⟨parseMap,by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [parseMap]
    | inr b => fin_cases a <;> simp [parseMap] at h
  | inr a => cases b with
    | inl b => fin_cases b <;> simp [parseMap] at h
    | inr b => simpa only [parseMap,Sum.inr.injEq] using h⟩
def parserProgram (l : BitMachineBankCodec.ParserLabel 2):=
  BitMachineStackEmbedding.stmt parseSlots id id id none (BitMachineBankCodec.parser 2 l)
def localFinal (w : Fin 2 → List Bool):=
  (BitMachineBankCodec.parserCfg (K:=2) none (some true) w [] [] []).stk
def parsed (w : Fin 2 → List Bool):=
  BitMachineStackEmbedding.bank parseSlots (fun _ : Stack => []) (localFinal w)
def loopSlots : BitMachineIteration.Stack M ↪ Stack:=⟨Sum.inl,Sum.inl_injective⟩
def loopProgram:=GaussCellCursorEmbedding.relocate loopSlots (BitMachineIteration.program M)
def loopStart : BitMachineIteration.Label M:=.inr .testFuel
def loopControl : BitMachineIteration.Control M:=(M.initial,none)
def program:=BitMachineRawSequence.program parserProgram loopProgram loopStart none loopControl
abbrev Label:=BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2) (BitMachineIteration.Label M)
abbrev Control:=BitMachineRawSequence.Control (Option Bool) (BitMachineIteration.Control M)
def start : Label:=BitMachineRawSequence.leftLabel (.scan 0)
def control : Control:=(none,loopControl)
def machine : BitMachine.Machine:=ofFinite inputCell outputCell start control program

theorem localFinal_eq (w : Fin 2 → List Bool) : localFinal w=
    Function.update (Function.update (fun _ : Fin 2 ⊕ Fin 3 => []) (.inl 0) (w 0)) (.inl 1) (w 1) := by
  funext j
  cases j with
  | inl j => fin_cases j <;> simp [localFinal,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  | inr j => fin_cases j <;> simp [localFinal,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]

theorem parsed_exact (w : Fin 2 → List Bool) : parsed w=
    BitMachineStackEmbedding.bank loopSlots (fun _ : Stack => [])
      (BitMachineIteration.ready M (w 0) (w 1)).stk := by
  have hempty : BitMachineStackEmbedding.bank parseSlots (fun _ : Stack => []) (fun _ => [])=
      (fun _ : Stack => []) := BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  unfold parsed
  rw [localFinal_eq,BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update,hempty]
  funext j
  cases j with
  | inl j =>
    change _=BitMachineStackEmbedding.bank loopSlots _ _ (loopSlots j)
    rw [BitMachineStackEmbedding.bank_at]
    cases j with
    | inl j =>
      by_cases hj : j=M.input <;>
        simp [parseSlots,parseMap,BitMachineIteration.ready,BitMachineIteration.adminCfg,
          BitMachine.Machine.init,BitMachineIteration.foreign,Function.update_apply,hj]
    | inr j => fin_cases j <;>
        simp [parseSlots,parseMap,BitMachineIteration.ready,BitMachineIteration.adminCfg,
          BitMachineIteration.foreign]
  | inr j =>
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ (by rintro ⟨z,h⟩; cases h)]
    simp [parseSlots,parseMap]

theorem parse_run (w : Fin 2 → List Bool) :
    ∃t ≤ 5*((BitMachineBankCodec.encode w).length+1),
      ((advance parserProgram)^[t])
        (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2)
          (none : Option Bool) (BitMachineBankCodec.encode w))=⟨none,some true,parsed w⟩ := by
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct 2 (BitMachineBankCodec.encode w) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  change BitMachineBankCodec.parserRun a
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) (BitMachineBankCodec.encode w) [] [])=
    BitMachineBankCodec.parserCfg none (some true) w [] [] [] at hparse
  let c:=BitMachineBankCodec.parserCfg (K:=2) (some (.scan 0)) none (fun _ => [])
    (BitMachineBankCodec.encode w) [] []
  have hc : c.stk=Function.update (fun _ : Fin 2 ⊕ Fin 3 => []) (.inr 0) (BitMachineBankCodec.encode w) := by
    funext z
    cases z with
    | inl z => simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr z => fin_cases z <;> simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hempty : BitMachineStackEmbedding.bank parseSlots (fun _ : Stack => []) (fun _ => [])=
      (fun _ : Stack => []) := BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hinit : BitMachineStackEmbedding.bank parseSlots (fun _ => []) c.stk=
      (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none : Option Bool)
        (BitMachineBankCodec.encode w)).stk := by
    rw [hc,BitMachineStackEmbedding.bank_update,hempty]
    funext z
    simp [parseSlots,parseMap,rawInit,inputCell,Function.update_apply]
  have hp : ((advance (BitMachineBankCodec.parser 2))^[a]) c=
      BitMachineBankCodec.parserCfg none (some true) w [] [] []:=hparse
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs parseSlots (fun _ => [])
    id id id (fun _ => rfl) none (BitMachineBankCodec.parser 2) parserProgram
    (fun _ => rfl) c a (by rw [hp]; rfl)
  rw [hp] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at he
  rw [hinit] at he
  exact ⟨t,ht.trans ha,he⟩

def words {m k : Nat} (B : Fin m → Fin k → ℚ) : Fin 2 → List Bool:=
  ![GaussControlTrace.statePacket (GaussControlTrace.initial B),List.replicate k true]

/-- A fixed machine parses its actual state/fuel packet and runs the entire
concrete Gauss loop. No prepared-bank or per-step execution premise remains. -/
theorem outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) :
    machine.OutputsWithin (BitMachineBankCodec.encode (words (fun i j => (A i j : ℚ))))
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) k))
      (5*((BitMachineBankCodec.encode (words (fun i j => (A i j : ℚ)))).length+1)+
        GaussWholeIteration.clock (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length+1) := by
  let w:=words (fun i j => (A i j : ℚ))
  obtain ⟨a,ha,hparse⟩:=parse_run w
  obtain ⟨b,hb,hhalt,hout⟩:=GaussWholeIteration.actual_run A h01 hm
  let c:=BitMachineIteration.run M b (BitMachineIteration.ready M (w 0) (w 1))
  have hc : c.l=none:=hhalt
  have ho : c.stk (.inl M.input)=GaussControlTrace.statePacket
      (GaussControlTrace.after (fun i j => (A i j : ℚ)) k):=hout
  obtain ⟨d,hd,hloop⟩:=BitMachineStackEmbedding.outputs loopSlots (fun _ : Stack => [])
    id id id (fun _ => rfl) none (BitMachineIteration.program M) loopProgram
    (fun _ => rfl) (BitMachineIteration.ready M (w 0) (w 1)) b hc
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at hloop
  have hhalt' : (((advance (BitMachineIteration.program M))^[b])
      (BitMachineIteration.ready M (w 0) (w 1))).l=none:=hc
  have hready : (BitMachineIteration.ready M (w 0) (w 1)).l=some loopStart:=rfl
  have hreadyVar : (BitMachineIteration.ready M (w 0) (w 1)).var=loopControl:=rfl
  rw [hhalt',hready,hreadyVar] at hloop
  change ((advance loopProgram)^[d])
    ⟨some loopStart,loopControl,BitMachineStackEmbedding.bank loopSlots (fun _ : Stack => [])
      (BitMachineIteration.ready M (w 0) (w 1)).stk⟩=
    ⟨none,c.var,BitMachineStackEmbedding.bank loopSlots (fun _ : Stack => []) c.stk⟩ at hloop
  rw [←parsed_exact] at hloop
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs parserProgram loopProgram
    (.scan 0) loopStart none (some true) loopControl c.var
    (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none : Option Bool)
      (BitMachineBankCodec.encode w)).stk (parsed w)
    (BitMachineStackEmbedding.bank loopSlots (fun _ : Stack => []) c.stk) a d hparse hloop
  have hfull : ((advance program)^[t])
      (rawInit inputCell start control (BitMachineBankCodec.encode w))=
      ⟨none,(none,c.var),BitMachineStackEmbedding.bank loopSlots (fun _ : Stack => []) c.stk⟩:=he
  apply outputsWithin_of_raw_run inputCell outputCell start control program
    (BitMachineBankCodec.encode w)
    (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) k)) t _
    (by dsimp only [w] at ha; omega)
  · change (((advance program)^[t]) _).l=none
    rw [hfull]
  · change (((advance program)^[t]) _).stk outputCell=_
    rw [hfull]
    exact (BitMachineStackEmbedding.bank_at loopSlots (fun _ : Stack => []) c.stk (.inl M.input)).trans ho

#print axioms parsed_exact
#print axioms parse_run
#print axioms outputs
end
end CurrentAdditive.GaussIterationPacketMachine
