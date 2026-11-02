import CurrentAdditive.RawBankParser
import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BitMachineRawSequence

namespace CurrentAdditive.OrdinaryIterationPacket
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
variable (M : BitMachine.Machine)
abbrev Stack := BitMachineIteration.Stack M ⊕ Fin 3
def inputCell : Stack M := .inr 0
def outputCell : Stack M := .inl (.inl M.input)
def parseMap : Fin 2 ⊕ Fin 3 → Stack M
  | .inl i => if i=0 then .inl (.inl M.input) else .inl (.inr 0)
  | .inr i => .inr i
def parseSlots : (Fin 2 ⊕ Fin 3) ↪ Stack M := ⟨parseMap M,by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [parseMap]
    | inr b => fin_cases a <;> simp [parseMap] at h
  | inr a => cases b with
    | inl b => fin_cases b <;> simp [parseMap] at h
    | inr b => simpa only [parseMap,Sum.inr.injEq] using h⟩
def parserProgram := RawBankParser.program (parseSlots M)
def parsed (w : Fin 2 → List Bool) := RawBankParser.parsed (parseSlots M) w
def loopSlots : BitMachineIteration.Stack M ↪ Stack M := ⟨Sum.inl,Sum.inl_injective⟩
def loopProgram (l : BitMachineIteration.Label M) :=
  BitMachineStackEmbedding.stmt (loopSlots M) id id id none (BitMachineIteration.program M l)
def loopStart : BitMachineIteration.Label M := .inr .testFuel
def loopControl : BitMachineIteration.Control M := (M.initial,none)
def program := BitMachineRawSequence.program (parserProgram M) (loopProgram M)
  (loopStart M) none (loopControl M)
abbrev Label := BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2) (BitMachineIteration.Label M)
abbrev Control := BitMachineRawSequence.Control (Option Bool) (BitMachineIteration.Control M)
def start : Label M := BitMachineRawSequence.leftLabel (.scan 0)
def control : Control M := (none,loopControl M)
def machine : BitMachine.Machine := ofFinite (inputCell M) (outputCell M) (start M) (control M) (program M)

theorem parsed_exact (w : Fin 2 → List Bool) : parsed M w=
    BitMachineStackEmbedding.bank (loopSlots M) (fun _ : Stack M => [])
      (BitMachineIteration.ready M (w 0) (w 1)).stk := by
  have hlocal : (BitMachineBankCodec.parserCfg (K:=2) none (some true) w [] [] []).stk=
      Function.update (Function.update (fun _ : Fin 2 ⊕ Fin 3 => []) (.inl 0) (w 0)) (.inl 1) (w 1) := by
    funext j
    cases j with
    | inl j => fin_cases j <;> simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr j => fin_cases j <;> simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hempty : BitMachineStackEmbedding.bank (parseSlots M) (fun _ : Stack M => []) (fun _ => [])=
      (fun _ : Stack M => []) := BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  unfold parsed RawBankParser.parsed
  rw [hlocal,BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update,hempty]
  funext j
  cases j with
  | inl j =>
    change _=BitMachineStackEmbedding.bank (loopSlots M) _ _ ((loopSlots M) j)
    rw [BitMachineStackEmbedding.bank_at]
    cases j with
    | inl j =>
      by_cases hj : j=M.input <;>
        simp [parseSlots,parseMap,BitMachineIteration.ready,BitMachineIteration.adminCfg,
          BitMachine.Machine.init,BitMachineIteration.foreign,Function.update_apply,hj]
    | inr j => fin_cases j <;>
        simp [parseSlots,parseMap,BitMachineIteration.ready,BitMachineIteration.adminCfg,BitMachineIteration.foreign]
  | inr j =>
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ (by rintro ⟨z,h⟩; cases h)]
    simp [parseSlots,parseMap]

/-- An ordinary two-field packet supplies the actual initial word and
literal fuel. Both fields are physically parsed, then every reset and data
transfer of the generic iteration program is executed. -/
theorem outputsWithin (states : Nat → List Bool) (fuel : List Bool) (L T : Nat)
    (hstep : ∀j<fuel.length,M.OutputsWithin (states j) (states (j+1)) T)
    (hlen : ∀j<fuel.length,(states j).length≤L) :
    (machine M).OutputsWithin (BitMachineBankCodec.encode ![states 0,fuel]) (states fuel.length)
      (5*((BitMachineBankCodec.encode ![states 0,fuel]).length+1)+
        fuel.length*BitMachineIteration.roundBound M L T+2) := by
  let w : Fin 2 → List Bool := ![states 0,fuel]
  obtain ⟨a,ha,hparse⟩:=RawBankParser.physical_parse (parseSlots M) w
  obtain ⟨b,hb,hhalt,hout⟩:=BitMachineIteration.iteration_output M states fuel L T hstep hlen
  let c:=BitMachineIteration.run M b (BitMachineIteration.ready M (w 0) (w 1))
  have hc : c.l=none := hhalt
  have ho : c.stk (.inl M.input)=states fuel.length := hout
  obtain ⟨d,hd,hloop⟩:=BitMachineStackEmbedding.outputs (loopSlots M) (fun _ : Stack M => [])
    id id id (fun _ => rfl) none (BitMachineIteration.program M) (loopProgram M)
    (fun _ => rfl) (BitMachineIteration.ready M (w 0) (w 1)) b hc
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at hloop
  have hhalt' : (((advance (BitMachineIteration.program M))^[b])
      (BitMachineIteration.ready M (w 0) (w 1))).l=none := hc
  have hready : (BitMachineIteration.ready M (w 0) (w 1)).l=some (loopStart M) := rfl
  have hreadyVar : (BitMachineIteration.ready M (w 0) (w 1)).var=loopControl M := rfl
  rw [hhalt',hready,hreadyVar] at hloop
  change ((advance (loopProgram M))^[d])
    ⟨some (loopStart M),loopControl M,BitMachineStackEmbedding.bank (loopSlots M) (fun _ : Stack M => [])
      (BitMachineIteration.ready M (w 0) (w 1)).stk⟩=
    ⟨none,c.var,BitMachineStackEmbedding.bank (loopSlots M) (fun _ : Stack M => []) c.stk⟩ at hloop
  rw [←parsed_exact] at hloop
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs (parserProgram M) (loopProgram M)
    (.scan 0) (loopStart M) none (some true) (loopControl M) c.var
    (rawInit (inputCell M) (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none : Option Bool)
      (BitMachineBankCodec.encode w)).stk (parsed M w)
    (BitMachineStackEmbedding.bank (loopSlots M) (fun _ : Stack M => []) c.stk) a d hparse hloop
  have hfull : ((advance (program M))^[t]) (rawInit (inputCell M) (start M) (control M) (BitMachineBankCodec.encode w))=
      ⟨none,(none,c.var),BitMachineStackEmbedding.bank (loopSlots M) (fun _ : Stack M => []) c.stk⟩ := he
  apply outputsWithin_of_raw_run (inputCell M) (outputCell M) (start M) (control M) (program M)
    (BitMachineBankCodec.encode w) (states fuel.length) t _ (by dsimp only [w] at ha; omega)
  · exact congrArg TM2.Cfg.l hfull
  · have h:=congrArg (fun z => z.stk (outputCell M)) hfull
    exact h.trans ((BitMachineStackEmbedding.bank_at (loopSlots M) (fun _ : Stack M => []) c.stk (.inl M.input)).trans ho)

#print axioms parsed_exact
#print axioms outputsWithin
end
end CurrentAdditive.OrdinaryIterationPacket
