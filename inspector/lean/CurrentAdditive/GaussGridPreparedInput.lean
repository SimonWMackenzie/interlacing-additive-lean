import CurrentAdditive.GaussInputDimensions
import CurrentAdditive.GaussConcreteGridClock
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Literal six-field parser and charged preparation of the concrete grid's
complete bank. The original four-field input gets these dimensions only
through GaussInputDimensions.machine, which counts the actual matrix. -/

namespace CurrentAdditive.GaussGridPreparedInput
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussConcreteCellEntry (N)
open GaussConcreteGrid (K)

abbrev Stack := GaussConcreteGrid.Stack
def base (i : Fin 32) : Stack := .inl (.inl ⟨i.val,by
  have hi:=i.isLt; dsimp only [K,N]; omega⟩)
def innerRows : Stack := .inl (.inl ⟨N+2,by dsimp only [K]; omega⟩)
def innerCols : Stack := .inl (.inl ⟨N+3,by dsimp only [K]; omega⟩)
def outerRows : Stack := .inr .rows
def outerCols : Stack := .inr .cols
def inputCell : Stack := .inr .buffer

def fieldSlot (i : Fin 6) : Stack :=
  ![base 8,base 9,base 10,base 20,innerRows,innerCols] i
def parseMap : Fin 6 ⊕ Fin 3 → Stack
  | .inl i => fieldSlot i
  | .inr i => ![inputCell,.inr .temp,.inr .output] i

theorem parseMap_injective : Function.Injective parseMap := by
  intro a b h
  have hN : 32 ≤ N := by dsimp only [N]; omega
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      fin_cases a <;> fin_cases b <;>
        simp [parseMap,fieldSlot,base,innerRows,innerCols,Fin.ext_iff] at h ⊢ <;> omega
    | inr b => fin_cases a <;> fin_cases b <;>
        simp [parseMap,fieldSlot,base,innerRows,innerCols,inputCell] at h
  | inr a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;>
        simp [parseMap,fieldSlot,base,innerRows,innerCols,inputCell] at h
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [parseMap,inputCell]

def parseSlots : (Fin 6 ⊕ Fin 3) ↪ Stack := ⟨parseMap,parseMap_injective⟩
def parserProgram (l : BitMachineBankCodec.ParserLabel 6) :=
  BitMachineStackEmbedding.stmt parseSlots id id id none (BitMachineBankCodec.parser 6 l)
def localFinal (w : Fin 6 → List Bool) :=
  (BitMachineBankCodec.parserCfg (K:=6) none (some true) w [] [] []).stk
def parsed (w : Fin 6 → List Bool) : Stack → List Bool :=
  BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)

theorem parsed_at (w : Fin 6 → List Bool) (i : Fin 6) :
    parsed w (fieldSlot i)=w i := by
  change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
    (parseSlots (.inl i))=w i
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem parsed_foreign (w : Fin 6 → List Bool) (e : GaussWordGridTraversal.Extra) :
    parsed w (.inr e)=[] := by
  cases e
  all_goals first
    | change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
        (parseSlots (.inr (0 : Fin 3)))=[]
      rw [BitMachineStackEmbedding.bank_at]; rfl
    | change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
        (parseSlots (.inr (1 : Fin 3)))=[]
      rw [BitMachineStackEmbedding.bank_at]; rfl
    | change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
        (parseSlots (.inr (2 : Fin 3)))=[]
      rw [BitMachineStackEmbedding.bank_at]; rfl
    | apply BitMachineStackEmbedding.bank_outside
      rintro ⟨z,hz⟩
      cases z with
      | inl z => fin_cases z <;> simp [parseSlots,parseMap,fieldSlot,base,innerRows,innerCols] at hz
      | inr z => fin_cases z <;> simp [parseSlots,parseMap,inputCell] at hz

theorem parsed_inner (w : Fin 6 → List Bool) (z : Fin K)
    (h8 : z.val≠8) (h9 : z.val≠9) (h10 : z.val≠10) (h20 : z.val≠20)
    (hm : z.val≠N+2) (hk : z.val≠N+3) :
    parsed w (.inl (.inl z))=[] := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨v,hv⟩
  cases v with
  | inl v =>
    fin_cases v <;> simp [parseSlots,parseMap,fieldSlot,base,innerRows,innerCols,Fin.ext_iff] at hv
    all_goals omega
  | inr v => fin_cases v <;> simp [parseSlots,parseMap,inputCell] at hv

theorem parsed_cursor (w : Fin 6 → List Bool) (z : Fin 3) :
    parsed w (.inl (.inr z))=[] := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨v,hv⟩
  cases v with
  | inl v => fin_cases v <;> simp [parseSlots,parseMap,fieldSlot,base,innerRows,innerCols] at hv
  | inr v => fin_cases v <;> simp [parseSlots,parseMap,inputCell] at hv

theorem parse_run (w : Fin 6 → List Bool) :
    ∃ t ≤ 13*((BitMachineBankCodec.encode w).length+1),
      ((advance parserProgram)^[t])
        (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 6)
          (none : Option Bool) (BitMachineBankCodec.encode w)) =
        ⟨none,some true,parsed w⟩ := by
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct 6 (BitMachineBankCodec.encode w) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  change BitMachineBankCodec.parserRun a
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
      (BitMachineBankCodec.encode w) [] []) =
    BitMachineBankCodec.parserCfg none (some true) w [] [] [] at hparse
  let c:=BitMachineBankCodec.parserCfg (K:=6) (some (.scan 0)) none (fun _ => [])
    (BitMachineBankCodec.encode w) [] []
  have hc : c.stk=Function.update (fun _ : Fin 6 ⊕ Fin 3 => [])
      (.inr 0) (BitMachineBankCodec.encode w) := by
    funext z
    cases z with
    | inl z => simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr z => fin_cases z <;> simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hempty : BitMachineStackEmbedding.bank parseSlots (fun _ => []) (fun _ => [])=
      (fun _ : Stack => []) := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro z; rfl
  have hinit : BitMachineStackEmbedding.bank parseSlots (fun _ => []) c.stk=
      (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 6) (none : Option Bool)
        (BitMachineBankCodec.encode w)).stk := by
    rw [hc,BitMachineStackEmbedding.bank_update,hempty]
    funext z
    simp [parseSlots,parseMap,rawInit,Function.update_apply]
  have hp : ((advance (BitMachineBankCodec.parser 6))^[a]) c=
      BitMachineBankCodec.parserCfg none (some true) w [] [] [] := hparse
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs parseSlots (fun _ => [])
    id id id (by intro z; rfl) none (BitMachineBankCodec.parser 6) parserProgram
    (by intro l; rfl) c a (by rw [hp]; rfl)
  rw [hp] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at he
  rw [hinit] at he
  exact ⟨t,ht.trans ha,he⟩

def copySlots : Fin 3 ↪ Stack := ⟨![innerRows,outerRows,.inr .temp],by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [innerRows,outerRows]⟩
def copyProgram := ExactParameterBranchInstall.copyProgram copySlots
def constantProgram (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  .push outerCols (fun _ => true) .halt
def finishProgram := BitMachineRawSequence.program copyProgram constantProgram () none none
abbrev FinishLabel := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev FinishControl := BitMachineRawSequence.Control (Option Bool) (Option Bool)
def finishStart : FinishLabel := BitMachineRawSequence.leftLabel .scan
def finishControl : FinishControl := (none,none)
def prepared (w : Fin 6 → List Bool) : Stack → List Bool :=
  Function.update (Function.update (parsed w) outerRows (w 4)) outerCols [true]

theorem finish_run (w : Fin 6 → List Bool) :
    ∃ t ≤ 2*(w 4).length+4,
      ((advance finishProgram)^[t])
        (⟨some finishStart,finishControl,parsed w⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,finishControl,prepared w⟩ := by
  have hm : parsed w (copySlots 0)=w 4 := by simpa [copySlots,fieldSlot] using parsed_at w 4
  have ht : parsed w (copySlots 1)=[] := parsed_foreign w .rows
  have hs : parsed w (copySlots 2)=[] := parsed_foreign w .temp
  obtain ⟨a,ha,hrun⟩:=ExactParameterBranchInstall.copy_run copySlots (parsed w) (w 4) hm ht hs
  let S:=Function.update (parsed w) outerRows (w 4)
  have hcols : S outerCols=[] := by
    simp [S,outerCols,outerRows,parsed_foreign]
  have hconstant : ((advance constantProgram)^[1])
      (⟨some (),none,S⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool))=
      ⟨none,none,prepared w⟩ := by
    simp [Function.iterate_one,advance,constantProgram,TM2.step,TM2.stepAux,
      S,prepared,hcols]
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs copyProgram constantProgram .scan ()
    none none none none (parsed w) S (prepared w) a 1 hrun hconstant
  exact ⟨t,by omega,he⟩

def program := BitMachineRawSequence.program parserProgram finishProgram finishStart none finishControl
abbrev Label := BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 6) FinishLabel
abbrev Control := BitMachineRawSequence.Control (Option Bool) FinishControl
def start : Label := BitMachineRawSequence.leftLabel (.scan 0)
def control : Control := (none,finishControl)
def preparationClock (w : Fin 6 → List Bool) : Nat :=
  13*((BitMachineBankCodec.encode w).length+1)+2*(w 4).length+5

theorem physical_prepare (w : Fin 6 → List Bool) :
    ∃ t ≤ preparationClock w, ((advance program)^[t])
      (rawInit inputCell start control (BitMachineBankCodec.encode w))=
      ⟨none,control,prepared w⟩ := by
  obtain ⟨a,ha,hparse⟩:=parse_run w
  obtain ⟨b,hb,hfinish⟩:=finish_run w
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs parserProgram finishProgram
    (.scan 0) finishStart none (some true) finishControl finishControl
    (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 6) (none : Option Bool)
      (BitMachineBankCodec.encode w)).stk (parsed w) (prepared w) a b hparse hfinish
  exact ⟨t,by unfold preparationClock; omega,he⟩

def rawWords {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Fin 4 → List Bool :=
  ![GaussPhysical.encodeTypedMatrix B,List.replicate r.val true,
    List.replicate pivot.val true,List.replicate c.val true]
def words {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Fin 6 → List Bool :=
  GaussInputDimensions.extended (rawWords B r pivot c) m k

theorem parsed_inner_value (w : Fin 6 → List Bool) (z : Fin K) :
    parsed w (.inl (.inl z))=
      if z.val=8 then w 0 else if z.val=9 then w 1 else
      if z.val=10 then w 2 else if z.val=20 then w 3 else
      if z.val=N+2 then w 4 else if z.val=N+3 then w 5 else [] := by
  have hN : 32 ≤ N := by dsimp only [N]; omega
  by_cases h8 : z.val=8
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 0 := by simp [fieldSlot,base,Fin.ext_iff,h8]
    rw [if_pos h8,hz,parsed_at]
  by_cases h9 : z.val=9
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 1 := by simp [fieldSlot,base,Fin.ext_iff,h9]
    rw [if_neg h8,if_pos h9,hz,parsed_at]
  by_cases h10 : z.val=10
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 2 := by simp [fieldSlot,base,Fin.ext_iff,h10]
    rw [if_neg h8,if_neg h9,if_pos h10,hz,parsed_at]
  by_cases h20 : z.val=20
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 3 := by simp [fieldSlot,base,Fin.ext_iff,h20]
    rw [if_neg h8,if_neg h9,if_neg h10,if_pos h20,hz,parsed_at]
  by_cases hm : z.val=N+2
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 4 := by simp [fieldSlot,innerRows,Fin.ext_iff,hm]
    rw [if_neg h8,if_neg h9,if_neg h10,if_neg h20,if_pos hm,hz,parsed_at]
  by_cases hk : z.val=N+3
  · have hz : (.inl (.inl z) : Stack)=fieldSlot 5 := by simp [fieldSlot,innerCols,Fin.ext_iff,hk]
    rw [if_neg h8,if_neg h9,if_neg h10,if_neg h20,if_neg hm,if_pos hk,hz,parsed_at]
  rw [if_neg h8,if_neg h9,if_neg h10,if_neg h20,if_neg hm,if_neg hk]
  exact parsed_inner w z h8 h9 h10 h20 hm hk

theorem prepared_exact {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    prepared (words B r pivot c)=(GaussConcreteGrid.initialData B r pivot c).contents := by
  have hN : 32 ≤ N := by dsimp only [N]; omega
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z =>
      have hout : (.inl (.inl z) : Stack)≠outerRows := by simp [outerRows]
      have hout' : (.inl (.inl z) : Stack)≠outerCols := by simp [outerCols]
      simp only [prepared,Function.update_of_ne hout,Function.update_of_ne hout',parsed_inner_value]
      by_cases hz : z.val<N
      · have hm : z.val≠N+2 := by omega
        have hk : z.val≠N+3 := by omega
        simp [words,GaussInputDimensions.extended,rawWords,GaussConcreteGrid.initialData,
          GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,
          GaussWordGridTraversal.Data.cell,GaussConcreteGrid.persistent,GaussConcreteCellEntry.persistent,
          hz,hm,hk]
      · have h8 : z.val≠8 := by omega
        have h9 : z.val≠9 := by omega
        have h10 : z.val≠10 := by omega
        have h20 : z.val≠20 := by omega
        simp [words,GaussInputDimensions.extended,rawWords,GaussConcreteGrid.initialData,
          GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,
          GaussWordGridTraversal.Data.cell,GaussConcreteGrid.persistent,GaussConcreteCellEntry.persistent,
          hz,h8,h9,h10,h20]
    | inr z =>
      fin_cases z <;> simp [prepared,outerRows,outerCols,parsed_cursor,GaussConcreteGrid.initialData,
        GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.cell]
  | inr z =>
    cases z <;>
      simp [prepared,outerRows,outerCols,parsed_foreign,words,GaussInputDimensions.extended,
        GaussConcreteGrid.initialData,GaussWordGridTraversal.ready,
        GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.foreign]

noncomputable instance : Fintype GaussFetchSave64.Control := by infer_instance
noncomputable instance : Fintype GaussFetchFromBackups64.Control := by infer_instance
noncomputable instance : Fintype GaussFourOperands64.Control := by
  letI : Fintype (BitMachineRawSequence.Control GaussFetchFromBackups64.Control
    GaussFetchFromBackups64.Control) := inferInstance
  letI : Fintype (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control GaussFetchFromBackups64.Control GaussFetchFromBackups64.Control)
    GaussFetchFromBackups64.Control) := inferInstance
  infer_instance
noncomputable instance : Fintype GaussFetchedAdaptedRequest.Control := by infer_instance
noncomputable instance : Fintype GaussFetchedArithmetic.Control := by infer_instance
noncomputable instance : Fintype GaussReusableRawCell.Control := by infer_instance
noncomputable instance : Fintype GaussFramedCell.Control := by infer_instance
noncomputable instance : Fintype GaussConcreteRow.RowLabel := by infer_instance
noncomputable instance : Fintype GaussConcreteRow.RowControl := by infer_instance
noncomputable instance : Fintype GaussConcreteRow.Label := by
  letI : Fintype (BitMachineRawSequence.Label GaussCountHeader.Label GaussConcreteRow.RowLabel) := inferInstance
  infer_instance
noncomputable instance : Fintype GaussConcreteRow.Control := by
  letI : Fintype (BitMachineRawSequence.Control GaussCountHeader.Control GaussConcreteRow.RowControl) := inferInstance
  infer_instance
noncomputable instance : Fintype GaussConcreteGrid.Label := by infer_instance
noncomputable instance : Fintype GaussConcreteGrid.Control := by infer_instance

def fullProgram := BitMachineRawSequence.program program GaussConcreteGrid.program
  GaussConcreteGrid.start control GaussConcreteGrid.control
abbrev FullLabel := BitMachineRawSequence.Label Label GaussConcreteGrid.Label
abbrev FullControl := BitMachineRawSequence.Control Control GaussConcreteGrid.Control
def fullStart : FullLabel := BitMachineRawSequence.leftLabel start
def fullControl : FullControl := (control,GaussConcreteGrid.control)
def outputCell : Stack := .inr .output
def sixFieldMachine : BitMachine.Machine :=
  ofFinite inputCell outputCell fullStart fullControl fullProgram
def finiteBitMachine : BitMachine.Machine :=
  BitMachineComposition.composition GaussInputDimensions.machine sixFieldMachine
def sixFieldClock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  preparationClock (words B r pivot c)+GaussConcreteGridClock.clock B r pivot c+1
def answer {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : List Bool :=
  GaussPhysical.encodeTypedMatrix
    (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c)

/-- The parser/copy/constant prefix reaches the exact prepared grid bank.
The physical grid then updates only its designated output stack. -/
theorem physical_grid_from_dimensions {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t ≤ sixFieldClock B r pivot c, ∃ v : GaussConcreteGrid.Control,
      ((advance fullProgram)^[t])
        (rawInit inputCell fullStart fullControl (BitMachineBankCodec.encode (words B r pivot c)))=
        ⟨none,(control,v),Function.update (GaussConcreteGrid.initialData B r pivot c).contents
          outputCell (answer B r pivot c)⟩ := by
  obtain ⟨a,ha,hprepare⟩:=physical_prepare (words B r pivot c)
  rw [prepared_exact] at hprepare
  obtain ⟨b,hb,v,hgrid⟩:=GaussConcreteGridClock.physical_grid_clock B r pivot c hn
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs program GaussConcreteGrid.program
    start GaussConcreteGrid.start control control GaussConcreteGrid.control v
    (rawInit inputCell start control (BitMachineBankCodec.encode (words B r pivot c))).stk
    (GaussConcreteGrid.initialData B r pivot c).contents
    (Function.update (GaussConcreteGrid.initialData B r pivot c).contents outputCell
      (answer B r pivot c)) a b hprepare hgrid
  exact ⟨t,by unfold sixFieldClock; omega,v,he⟩

theorem six_field_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    sixFieldMachine.OutputsWithin (BitMachineBankCodec.encode (words B r pivot c))
      (answer B r pivot c) (sixFieldClock B r pivot c) := by
  obtain ⟨t,ht,v,hrun⟩:=physical_grid_from_dimensions B r pivot c hn
  apply outputsWithin_of_raw_run inputCell outputCell fullStart fullControl fullProgram
    (BitMachineBankCodec.encode (words B r pivot c)) (answer B r pivot c) t _ ht
  · rw [hrun]
  · rw [hrun]; simp

def clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  GaussInputDimensions.clock (rawWords B r pivot c) m k+
    2*(BitMachineBankCodec.encode (words B r pivot c)).length+2+
    sixFieldClock B r pivot c

/-- One fixed finite machine accepts only the original four serialized words.
Both unary dimensions are obtained by real counting machines, and every
preparation/copy/transfer step is charged. This theorem concerns valid typed
matrices and nonzero pivots; it makes no totality claim on malformed packets. -/
theorem outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    finiteBitMachine.OutputsWithin
      (BitMachineBankCodec.encode (rawWords B r pivot c))
      (answer B r pivot c) (clock B r pivot c) := by
  have hm : 0 < m := by
    have hr := r.isLt
    omega
  have hdimensions:=GaussInputDimensions.outputs B hm (rawWords B r pivot c) rfl
  have hgrid:=six_field_outputs B r pivot c hn
  exact BitMachineComposition.composition_outputsWithin
    GaussInputDimensions.machine sixFieldMachine hdimensions hgrid

#print axioms physical_prepare
#print axioms prepared_exact
#print axioms physical_grid_from_dimensions
#print axioms outputs

end
end CurrentAdditive.GaussGridPreparedInput
