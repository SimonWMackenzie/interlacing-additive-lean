import CurrentAdditive.FeaturePacketJoin96

/-! Physical finalization after one coordinate: count-header conversion,
old-packet deletion, exact header/body writing, and header scratch deletion.
Every other bank, including the retained body and unary count, is preserved. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace CurrentAdditive.FeaturePacketFinalize96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

def clearProgram (k : Fin 96) : Bool →
    TM2.Stmt (fun _ : Fin 96 => Bool) Bool (Unit × Option Bool)
  | false => BitMachineClearBank.clearStep k false true
  | true => .halt

theorem clear_run (k : Fin 96) (S : Fin 96 → List Bool) :
    ((advance (clearProgram k))^[(S k).length+2])
      (⟨some false,((),none),S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,((),none),Function.update S k []⟩ := by
  have h := BitMachineClearBank.clear_one_run (clearProgram k) k false true rfl () S
  rw [show (S k).length+2=((S k).length+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def p01 := BitMachineRawSequence.program FeatureCountHeader96.program
  (clearProgram 8) false FeatureCountHeader96.control (((),none) : Unit × Option Bool)
def start01 := labelFor p01 (BitMachineRawSequence.leftLabel FeatureCountHeader96.start)
def control01 := (FeatureCountHeader96.control,(((),none) : Unit × Option Bool))

def p012 := BitMachineRawSequence.program p01 FeaturePacketJoin96.program
  FeaturePacketJoin96.start control01 FeaturePacketJoin96.control
def start012 := labelFor p012 (BitMachineRawSequence.leftLabel start01)
def control012 := (control01,FeaturePacketJoin96.control)

def program := BitMachineRawSequence.program p012 (clearProgram 16)
  false control012 (((),none) : Unit × Option Bool)
def start := labelFor program (BitMachineRawSequence.leftLabel start012)
def control := (control012,(((),none) : Unit × Option Bool))

def clock (S : Fin 96 → List Bool) (count body : List Bool) :=
  FeatureCountHeader96.clock count+(S 8).length+2+
    FeaturePacketJoin96.clock (EncodedCommunication.natField count.length) body+
    (EncodedCommunication.natField count.length).length+2+3

theorem run (S : Fin 96 → List Bool) (count body : List Bool)
    (h12 : S 12=count) (h9 : S 9=body) (h16 : S 16=[])
    (h19 : S 19=[]) (h20 : S 20=[])
    (hhigh : ∀ k : Fin 96, 32≤k.val → S k=[]) :
    ∃ t≤clock S count body,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,Function.update S 8
        (EncodedCommunication.natField count.length++body)⟩ := by
  let header := EncodedCommunication.natField count.length
  let U := Function.update S (16 : Fin 96) header
  let V := Function.update U (8 : Fin 96) []
  let W := Function.update U (8 : Fin 96) (header++body)
  let X := Function.update W (16 : Fin 96) []
  obtain ⟨a,ha,haRun⟩ := FeatureCountHeader96.run S count h12 h16 h19 hhigh
  have hbRun := clear_run 8 U
  have hbTime : (U 8).length+2=(S 8).length+2 := by simp [U]
  rw [hbTime] at hbRun
  obtain ⟨c,hc,hcRun⟩ := FeaturePacketJoin96.run V header body
    (by simp [V,U]) (by simpa [V,U] using h9) (by simpa [V,U] using h19) (by simp [V])
  have hcRun' : ((advance FeaturePacketJoin96.program)^[c])
      ⟨some FeaturePacketJoin96.start,FeaturePacketJoin96.control,V⟩=
        ⟨none,FeaturePacketJoin96.control,W⟩ := by
    simpa [V,W] using hcRun
  have hdRun := clear_run 16 W
  have hdTime : (W 16).length+2=header.length+2 := by simp [W,U]
  rw [hdTime] at hdRun
  obtain ⟨ab,hab,habRun⟩ := BitMachineRawSequence.runs
    FeatureCountHeader96.program (clearProgram 8) FeatureCountHeader96.start false
    FeatureCountHeader96.control FeatureCountHeader96.control
    (((),none) : Unit × Option Bool) (((),none) : Unit × Option Bool)
    S U V a ((S 8).length+2) haRun hbRun
  obtain ⟨abc,habc,habcRun⟩ := BitMachineRawSequence.runs
    p01 FeaturePacketJoin96.program start01 FeaturePacketJoin96.start
    control01 control01 FeaturePacketJoin96.control FeaturePacketJoin96.control
    S V W ab c
    (by simpa only [p01,start01,labelFor,control01] using habRun) hcRun'
  obtain ⟨t,ht,htRun⟩ := BitMachineRawSequence.runs
    p012 (clearProgram 16) start012 false
    control012 control012 (((),none) : Unit × Option Bool) (((),none) : Unit × Option Bool)
    S W X abc (header.length+2)
    (by simpa only [p012,start012,labelFor,control012] using habcRun) hdRun
  have hX : X=Function.update S 8 (header++body) := by
    funext k
    by_cases h8 : k=8
    · subst k; simp [X,W,U]
    by_cases h16k : k=16
    · subst k; simp [X,W,U,h16]
    simp [X,W,U,h8,h16k]
  rw [hX] at htRun
  refine ⟨t,?_,by simpa only [program,start,labelFor,control,header] using htRun⟩
  change t≤FeatureCountHeader96.clock count+(S 8).length+2+
    FeaturePacketJoin96.clock header body+header.length+2+3
  omega

#print axioms run
end CurrentAdditive.FeaturePacketFinalize96
