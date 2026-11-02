import CurrentAdditive.GaussUnaryEquality64
import CurrentAdditive.GaussSwapIndexSpec

set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussSwapAddresses64
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
abbrev Stack := Fin 64

def eqStart : GaussUnaryEquality64.Label :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)
def eqControl : GaussUnaryEquality64.Control :=
  ((((),none),((),none)),(none,none))

def eqPair := BitMachineRawSequence.program
  (GaussUnaryEquality64.program 7 9 28)
  (GaussUnaryEquality64.program 7 10 31)
  eqStart eqControl eqControl

def selected (er ep : Bool) : Stack := if er then 10 else if ep then 9 else 7
abbrev PickLabel := Unit ⊕ ((Bool × Bool) × GaussGetterCopy64.Label)
abbrev PickControl := (Option Bool × Option Bool) × GaussGetterCopy64.Control

def pickProgram : PickLabel → TM2.Stmt (fun _ : Stack => Bool) PickLabel PickControl
  | .inl _ => .peek 28 (fun v b => ((b,v.1.2),v.2))
      (.peek 31 (fun v b => ((v.1.1,b),v.2))
        (.load (fun v => ((v.1.1,v.1.2),((),none)))
          (.goto (fun v => .inr ((v.1.1.getD false,v.1.2.getD false),.scan)))))
  | .inr ((er,ep),l) => BitMachineInline.stmt
      (fun l => .inr ((er,ep),l))
      (fun v => ((some er,some ep),v)) Prod.snd none
      (GaussGetterCopy64.program (selected er ep) 17 l)

def pickControl : PickControl := ((none,none),((),none))

noncomputable def source (i r pivot : Nat) : Nat :=
  if i=r then pivot else if i=pivot then r else i

theorem pick_run (S : Stack → List Bool) (i r pivot : Nat)
    (h7 : S 7 = List.replicate i true)
    (h9 : S 9 = List.replicate r true)
    (h10 : S 10 = List.replicate pivot true)
    (h17 : S 17 = []) (h63 : S 63 = [])
    (h28 : S 28 = [decide (i=r)]) (h31 : S 31 = [decide (i=pivot)]) :
    ∃ t ≤ 2*source i r pivot+4, ∃ v,
      ((advance pickProgram)^[t])
        (⟨some (.inl ()),pickControl,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,Function.update S 17 (List.replicate (source i r pivot) true)⟩ := by
  let er := decide (i=r)
  let ep := decide (i=pivot)
  let A := selected er ep
  have hA : A ≠ 63 := by dsimp [A,selected]; split_ifs <;> decide
  have h17A : (17 : Stack) ≠ A := by dsimp [A,selected]; split_ifs <;> decide
  have hword : S A = List.replicate (source i r pivot) true := by
    by_cases hir : i=r
    · simp [A,selected,er,ep,source,hir,h10]
    · by_cases hip : i=pivot
      · subst pivot; simp [A,selected,er,ep,source,hir,h9]
      · simp [A,selected,er,ep,source,hir,hip,h7]
  have hcopy := (GaussGetterCopy64.copy_word A 17 hA h17A (by decide)
    (List.replicate (source i r pivot) true) S hword h63 h17).1
  rw [GaussUnaryEquality64.copy_result A 17 hA h17A (by decide)
    S _ hword h63 h17] at hcopy
  have hh : (GaussGetterCopy64.run A 17 (2*source i r pivot+3)
      ⟨some .scan,((),none),S⟩).l = none := by
    simpa only [List.length_replicate] using congrArg (fun c => c.l) hcopy
  obtain ⟨u,hu,hsub⟩ := BitMachineInline.outputs
    (fun l => .inr ((er,ep),l) : GaussGetterCopy64.Label → PickLabel)
    (fun v => ((some er,some ep),v)) Prod.snd (by intro v; rfl) none
    (GaussGetterCopy64.program A 17) pickProgram (by intro l; rfl)
    (⟨some .scan,((),none),S⟩ : GaussGetterCopy64.Config)
    (2*source i r pivot+3) hh
  have hcopy' : GaussGetterCopy64.run A 17 (2*source i r pivot+3)
      ⟨some .scan,((),none),S⟩ =
      ⟨none,((),none),Function.update S 17 (List.replicate (source i r pivot) true)⟩ := by
    simpa only [List.length_replicate] using hcopy
  rw [show ((advance (GaussGetterCopy64.program A 17))^[2*source i r pivot+3])
      (⟨some .scan,((),none),S⟩ : GaussGetterCopy64.Config) =
      ⟨none,((),none),Function.update S 17 (List.replicate (source i r pivot) true)⟩
      from hcopy'] at hsub
  have hdispatch : advance pickProgram
      (⟨some (.inl ()),pickControl,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some (.inr ((er,ep),.scan)),((some er,some ep),((),none)),S⟩ := by
    simp [advance,TM2.step,TM2.stepAux,pickProgram,pickControl,h28,h31,er,ep]
  refine ⟨u+1,by omega,((some er,some ep),((),none)),?_⟩
  rw [Function.iterate_succ_apply,hdispatch]
  exact hsub

def program := BitMachineRawSequence.program eqPair pickProgram
  (.inl ()) (eqControl,eqControl) pickControl

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label GaussUnaryEquality64.Label GaussUnaryEquality64.Label)
  PickLabel
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control GaussUnaryEquality64.Control GaussUnaryEquality64.Control)
  PickControl

def initial (S : Stack → List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel eqStart)),((eqControl,eqControl),pickControl),S⟩

theorem physical_sourceRow (S : Stack → List Bool) (i r pivot : Nat)
    (h7 : S 7 = List.replicate i true)
    (h9 : S 9 = List.replicate r true)
    (h10 : S 10 = List.replicate pivot true)
    (h15 : S 15 = []) (h16 : S 16 = []) (h17 : S 17 = [])
    (h28 : S 28 = []) (h31 : S 31 = []) (h63 : S 63 = []) :
    ∃ t ≤ (2*i+2*r+max i r+10)+(2*i+2*pivot+max i pivot+10)+
        2*source i r pivot+6, ∃ v,
      ((advance program)^[t]) (initial S) =
        ⟨none,v,Function.update
          (Function.update (Function.update S 28 [decide (i=r)]) 31 [decide (i=pivot)])
          17 (List.replicate (source i r pivot) true)⟩ := by
  obtain ⟨a,ha,va,hrunA⟩ := GaussUnaryEquality64.run_equal 7 9 28
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) S i r h7 h9 h15 h16 h63
  simp only [h28] at hrunA
  let S1 := Function.update S 28 [decide (i=r)]
  obtain ⟨b,hb,vb,hrunB⟩ := GaussUnaryEquality64.run_equal 7 10 31
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) S1 i pivot
    (by simp [S1,h7]) (by simp [S1,h10]) (by simp [S1,h15])
    (by simp [S1,h16]) (by simp [S1,h63])
  have hS131 : S1 31 = [] := by simp [S1,h31]
  simp only [hS131] at hrunB
  let S2 := Function.update S1 31 [decide (i=pivot)]
  obtain ⟨u,hu,hpair⟩ := BitMachineRawSequence.runs
    (GaussUnaryEquality64.program 7 9 28) (GaussUnaryEquality64.program 7 10 31)
    eqStart eqStart eqControl va eqControl vb S S1 S2 a b hrunA hrunB
  obtain ⟨c,hc,vc,hpick⟩ := pick_run S2 i r pivot
    (by simp [S2,S1,h7]) (by simp [S2,S1,h9]) (by simp [S2,S1,h10])
    (by simp [S2,S1,h17]) (by simp [S2,S1,h63])
    (by simp [S2,S1]) (by simp [S2])
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs eqPair pickProgram
    (BitMachineRawSequence.leftLabel eqStart) (.inl ())
    (eqControl,eqControl) (eqControl,vb) pickControl vc
    S S2 (Function.update S2 17 (List.replicate (source i r pivot) true))
    u c hpair hpick
  exact ⟨t,by omega,((eqControl,eqControl),vc),hfull⟩


def completeProgram := BitMachineRawSequence.program program
  (GaussGetterCopy64.program 10 18) .scan
  ((eqControl,eqControl),pickControl) ((),none)

abbrev CompleteLabel := BitMachineRawSequence.Label Label GaussGetterCopy64.Label
abbrev CompleteControl := BitMachineRawSequence.Control Control GaussGetterCopy64.Control

def completeStart : CompleteLabel := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel eqStart))
def completeControl : CompleteControl := (((eqControl,eqControl),pickControl),((),none))

theorem physical_addresses (S : Stack → List Bool) (i r pivot : Nat)
    (h7 : S 7 = List.replicate i true)
    (h9 : S 9 = List.replicate r true)
    (h10 : S 10 = List.replicate pivot true)
    (h15 : S 15 = []) (h16 : S 16 = []) (h17 : S 17 = [])
    (h18 : S 18 = []) (h28 : S 28 = []) (h31 : S 31 = []) (h63 : S 63 = []) :
    ∃ t ≤ (2*i+2*r+max i r+10)+(2*i+2*pivot+max i pivot+10)+
        2*source i r pivot+2*pivot+10, ∃ v,
      ((advance completeProgram)^[t])
        (⟨some completeStart,completeControl,S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) CompleteLabel CompleteControl) =
        ⟨none,v,Function.update
          (Function.update
            (Function.update (Function.update S 28 [decide (i=r)]) 31 [decide (i=pivot)])
            17 (List.replicate (source i r pivot) true))
          18 (List.replicate pivot true)⟩ := by
  obtain ⟨a,ha,v,hrow⟩ := physical_sourceRow S i r pivot
    h7 h9 h10 h15 h16 h17 h28 h31 h63
  let T := Function.update
    (Function.update (Function.update S 28 [decide (i=r)]) 31 [decide (i=pivot)])
    17 (List.replicate (source i r pivot) true)
  have hT10 : T 10=List.replicate pivot true := by simp [T,h10]
  have hT18 : T 18=[] := by simp [T,h18]
  have hT63 : T 63=[] := by simp [T,h63]
  have hcopy := (GaussGetterCopy64.copy_word 10 18 (by decide) (by decide)
    (by decide) (List.replicate pivot true) T hT10 hT63 hT18).1
  rw [GaussUnaryEquality64.copy_result 10 18 (by decide) (by decide) (by decide)
    T _ hT10 hT63 hT18] at hcopy
  have hcopy' : GaussGetterCopy64.run 10 18 (2*pivot+3)
      ⟨some .scan,((),none),T⟩ =
      ⟨none,((),none),Function.update T 18 (List.replicate pivot true)⟩ := by
    simpa only [List.length_replicate] using hcopy
  obtain ⟨t,ht,hall⟩ := BitMachineRawSequence.runs program
    (GaussGetterCopy64.program 10 18)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel eqStart)) .scan
    ((eqControl,eqControl),pickControl) v ((),none) ((),none)
    S T (Function.update T 18 (List.replicate pivot true)) a (2*pivot+3) hrow hcopy'
  exact ⟨t,by omega,(((eqControl,eqControl),pickControl),((),none)),hall⟩

theorem source_eq_swap {m : Nat} (i r pivot : Fin m) :
    source i.val r.val pivot.val =
      (GaussCellSourceBridge.sourceRow r pivot i).val := by
  rw [GaussSwapIndexSpec.sourceRow_target]
  by_cases hir : i=r
  · subst i; simp [source]
  · have hvir : i.val≠r.val := by intro h; exact hir (Fin.ext h)
    by_cases hip : i=pivot
    · subst i; simp [source,hvir,hir]
    · have hvip : i.val≠pivot.val := by intro h; exact hip (Fin.ext h)
      simp [source,hir,hip,hvir,hvip]

#print axioms physical_addresses
#print axioms source_eq_swap
#print axioms pick_run
#print axioms physical_sourceRow
end CurrentAdditive.GaussSwapAddresses64
