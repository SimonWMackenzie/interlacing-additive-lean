import CurrentAdditive.V39WMasterLayout

/-! A fixed physical preparation program for the complete table-writer bank.
It copies only literal graph/count/code/sample words supplied in source
cells, and performs one charged push to form s+1. A blank source supplies
every blank work cell. The fixed finite copy schedule depends on stack
positions only, never on the graph, sampled labels, or their matrix values. -/

namespace CurrentAdditive.V39WTablePrepare
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 16384
open Paper2 Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open V39WEntry

abbrev WriterStack := MatrixTableWriter.Stack Kw
abbrev Stack := Fin 14 ⊕ (WriterStack ⊕ Fin 1)

def writer : WriterStack ↪ Stack := ⟨fun j => .inr (.inl j),by intro a b h; cases h; rfl⟩
def scratch : Stack := .inr (.inr 0)
def masterCell (z : SrcX.JX) : WriterStack := .inl (ιW (.inl (.inl (V39RLoop.mX z))))
def plusCell : WriterStack := masterCell (V39WMasterLayout.dst 0)

def masterSource (z : SrcX.JX) : Fin 14 :=
  if z=V39WMasterLayout.dst 0 then 5 else
  if z=V39WMasterLayout.dst 1 then 5 else
  if z=V39WMasterLayout.dst 2 then 1 else
  if z=V39WMasterLayout.dst 3 then 2 else
  if z=V39WMasterLayout.dst 4 then 0 else
  if z=V39WMasterLayout.dst 5 then 4 else
  if z=V39WMasterLayout.dst 6 then 5 else
  if z=V39WMasterLayout.dst 7 then 7 else
  if z=V39WMasterLayout.dst 8 then 3 else
  if z=V39WMasterLayout.dst 9 then 6 else 13

def sourceIndex : WriterStack → Fin 14
  | .inl (.inl k) => match eqv.symm k with
    | .inl (.inr (.inl z)) => masterSource z
    | .inl _ => 13
    | .inr (.inl i) => (![13,13,11,10,8] : Fin 5 → Fin 14) i
    | .inr (.inr (.inl _)) => 13
    | .inr (.inr (.inr i)) => (![12,9] : Fin 2 → Fin 14) i
  | .inl (.inr _) => 13
  | .inr .rows => 9
  | .inr .cols => 9
  | .inr _ => 13

@[irreducible] def N : Nat := Fintype.card WriterStack
def enumerate : Fin N ≃ WriterStack := by unfold N; exact (Fintype.equivFin _).symm

def copySlots (i : Fin N) : Fin 3 ↪ Stack :=
  ⟨![.inl (sourceIndex (enumerate i)),writer (enumerate i),scratch],by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [writer,scratch]⟩

theorem copy_hsd : ∀ i j, copySlots i 0 ≠ copySlots j 1 := by
  intro i j; simp [copySlots,writer]
theorem copy_hzd : ∀ i j, copySlots i 2 ≠ copySlots j 1 := by
  intro i j; simp [copySlots,writer,scratch]
theorem copy_hdd : ∀ i j, copySlots i 1 = copySlots j 1 → i=j := by
  intro i j h
  apply enumerate.injective
  exact writer.injective h

def copyProgram := CopyAll.prog copySlots
def pushProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit :=
  fun _ => push (writer plusCell) (fun _ => true) halt
def program := BitMachineRawSequence.program copyProgram pushProgram ()
  (none:Option Bool) ()
def start : BitMachineRawSequence.Label (CopyAll.Lab N) Unit := BitMachineRawSequence.leftLabel (.inl (0:Fin (N+1)) : CopyAll.Lab N)
def control := ((none:Option Bool),())

variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

/-- Source slots: graph,r,edge count,p,q1,s,w,Q,K,m,row syntax,column
syntax,current row-first sample word,blank. -/
def sourceWords (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    Fin 14 → List Bool :=
  ![EncodedGraph.encode g,List.replicate r true,List.replicate g.edges.length true,
    List.replicate p true,List.replicate q₁ true,List.replicate s true,
    List.replicate w true,List.replicate Q true,List.replicate K true,
    List.replicate m true,
    GeneratorSerialization.encodeCode (GeneratorSource.seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1,
    GeneratorSerialization.encodeCode (GeneratorSource.seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2,
    (rowWords g K m xs).flatten ++ (colWords g K m ys).flatten,[]]

def target (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    WriterStack → List Bool :=
  (MatrixTableWriter.ready (bankW g r K m m xs ys) m m 0 0 0 0 [] []).contents

def initial (S : Fin 14 → List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => [])

def final (S : Fin 14 → List Bool) (T : WriterStack → List Bool) : Stack → List Bool :=
  Sum.elim S (Sum.elim T (fun _ => []))

theorem target_master (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) (z : SrcX.JX) :
    target g r K m xs ys (masterCell z) =
      V39RLoop.master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z := by
  simp [target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,
    MatrixTableWriter.Data.cell,masterCell,ιW,ιWf,bankW,auxBank,V39RLoop.restL,V39RLoop.mX]

theorem sourceIndex_exact (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) (j : WriterStack) :
    sourceWords g r K m xs ys (sourceIndex j) =
      Function.update (target g r K m xs ys) plusCell (List.replicate s true) j := by
  rcases j with (k | i) | e
  · let a := eqv.symm k
    have hk : eqv a=k := eqv.apply_symm_apply k
    rw [←hk]
    rcases a with jl | (i | (f | i))
    · rcases jl with jt | (z | i)
      · simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,V39RLoop.restL,Function.update_apply,
          plusCell,masterCell,ιW,ιWf,eqv.symm_apply_apply,V39RLoop.mX]
      · by_cases hz : ∃ i, V39WMasterLayout.dst i=z
        · obtain ⟨i,rfl⟩ := hz
          fin_cases i <;>
            simp [sourceIndex,masterSource,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,
              V39RLoop.restL,plusCell,masterCell,ιW,ιWf,V39RLoop.mX,
              V39WMasterLayout.dst,V39WMasterLayout.scan,V39WMasterLayout.graph,
              FetchIndexed.myC,OTBody.sC,V39RLoop.master,SrcX.WXb,SrcU.JJ0,
              SrcX.srcAX,SrcX.fwX,SrcU.srcA,TemplateStepX.ccX,TemplateStepX.rcX,V39RLoop.marksX,
              OTOps.u,ScanDecodeMachine.u,
              DefaultWordLoop.entry,DefaultWordLoop.bk,CanonicalDefaultWordScratch.RowMachine.B,
              DefaultColumnRound.B,OTBody.BB,FetchIndexed.FB,FetchLabel.fb,
              ScanDecodeMachine.D0,EndpointOperands.entry,GraphPrefixBind.initBank,
              PublicGraphEndpointMachine.initialBank,SourceNormalizationMachineDecode.start,RankRun.RB,
              Function.update_apply]
        · push_neg at hz
          have hz' : ∀ i, z ≠ V39WMasterLayout.dst i := fun i => Ne.symm (hz i)
          have hm := V39WMasterLayout.master_off (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂)
            (w:=w) (Q:=Q) g r z hz
          simp [sourceIndex,masterSource,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,V39RLoop.restL,
            plusCell,masterCell,ιW,ιWf,V39RLoop.mX,Function.update_apply,hz',hm]
      · fin_cases i <;>
          simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,V39RLoop.restL,
            plusCell,masterCell,ιW,ιWf,V39RLoop.mX,Function.update_apply]
    · fin_cases i <;>
        simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,plusCell,masterCell,
          ιW,ιWf,V39RLoop.mX,Function.update_apply]
    · simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,plusCell,masterCell,
        ιW,ιWf,V39RLoop.mX,Function.update_apply]
    · fin_cases i <;>
        simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,bankW,auxBank,plusCell,masterCell,
          ιW,ιWf,V39RLoop.mX,Function.update_apply]
  · fin_cases i <;> simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,plusCell,masterCell,ιW,ιWf,V39RLoop.mX,Function.update_apply]
  · cases e <;> simp [sourceIndex,sourceWords,target,MatrixTableWriter.ready,MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,MatrixTableWriter.Data.foreign,plusCell,masterCell,ιW,ιWf,V39RLoop.mX,Function.update_apply]

theorem copied_exact (S : Fin 14 → List Bool) :
    CopyAll.done copySlots N (initial S) = final S (fun j => S (sourceIndex j)) := by
  funext z
  rcases z with i | (j | i)
  · rw [CopyAll.done_off copySlots _ _ (by intro k; simp [copySlots,writer])]
    rfl
  · have h : (Sum.inr (Sum.inl j) : Stack)=copySlots (enumerate.symm j) 1 := by
      simp [copySlots,writer]
    rw [h,CopyAll.done_dst copySlots copy_hdd]
    simp [copySlots,initial,final,writer]
  · rw [CopyAll.done_off copySlots _ _ (by intro k; simp [copySlots,writer,scratch])]
    rfl

def inputLength (S : Fin 14 → List Bool) : Nat := ∑ i, (S i).length
def clock (S : Fin 14 → List Bool) : Nat := N*(2*inputLength S+3)+3

theorem physical_prepare (g : EncodedGraph.Graph) (r K m : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let S := sourceWords g r K m xs ys
    ∃ t ≤ clock S, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,initial S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,final S (target g r K m xs ys)⟩ := by
  intro S
  obtain ⟨a,ha,va,hcopy⟩ := CopyAll.all_run copySlots copy_hsd copy_hzd copy_hdd
    (initial S) (by intro i; rfl) (inputLength S) (by
      intro i
      change (S (sourceIndex (enumerate i))).length ≤ ∑ j, (S j).length
      exact Finset.single_le_sum (f := fun j : Fin 14 => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (sourceIndex (enumerate i))))
    (none:Option Bool)
  rw [copied_exact] at hcopy
  have hpush : ((advance pushProgram)^[1])
      (⟨some (),(),final S (fun j => S (sourceIndex j))⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,(),final S (target g r K m xs ys)⟩ := by
    have hbank : Function.update (final S (fun j => S (sourceIndex j))) (writer plusCell)
        (true :: S (sourceIndex plusCell)) = final S (target g r K m xs ys) := by
      funext z
      rcases z with i | (j | i)
      · simp [final,writer,Function.update_apply]
      · by_cases hj : j=plusCell
        · subst j
          rw [show (Sum.inr (Sum.inl plusCell) : Stack)=writer plusCell from rfl,Function.update_self]
          change true :: S (sourceIndex plusCell) = target g r K m xs ys plusCell
          change true :: sourceWords g r K m xs ys (sourceIndex plusCell) = target g r K m xs ys plusCell
          rw [sourceIndex_exact,Function.update_self]
          rw [show plusCell=masterCell (V39WMasterLayout.dst 0) from rfl,target_master]
          change true :: List.replicate s true =
            V39RLoop.master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r (V39WMasterLayout.dst 0)
          rw [V39WMasterLayout.master_at]
          rfl
        · rw [Function.update_of_ne (by simpa [writer] using hj)]
          change S (sourceIndex j)=target g r K m xs ys j
          change sourceWords g r K m xs ys (sourceIndex j) = target g r K m xs ys j
          rw [sourceIndex_exact,Function.update_of_ne hj]
      · simp [final,writer,scratch,Function.update_apply]
    change (⟨none,(),Function.update (final S (fun j => S (sourceIndex j)))
      (writer plusCell) (true :: S (sourceIndex plusCell))⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit Unit) = _
    rw [hbank]
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs copyProgram pushProgram
    (.inl (0:Fin (N+1))) () (none:Option Bool) va () () _ _ _ a 1 hcopy hpush
  exact ⟨t,by unfold clock; omega,((none:Option Bool),()),by
    simpa only [program,start,control] using he⟩

#print axioms sourceIndex_exact
#print axioms physical_prepare
end
end CurrentAdditive.V39WTablePrepare
