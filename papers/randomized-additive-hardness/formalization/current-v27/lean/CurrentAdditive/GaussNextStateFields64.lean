import CurrentAdditive.GaussNextFieldsPrepare64
import CurrentAdditive.GaussCellCursorEmbedding
import CurrentAdditive.GaussPivotQuadraticClock32
import CurrentAdditive.GaussStepInactivePacket32
import CurrentAdditive.GaussPivotPrepHigh64

namespace CurrentAdditive.GaussNextStateFields64
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussNextFieldsPrepare64 (Bank)

def fieldStart : GaussStepFields32.Label := .parse false (.inl (.scan 0))
def fieldControl : GaussStepFields32.Control := GaussStepFields32.eParse none
def fieldProgram := GaussCellCursorEmbedding.relocate GaussPivotPrepHigh64.low GaussStepFields32.program
def program := BitMachineRawSequence.program GaussNextFieldsPrepare64.program fieldProgram
  fieldStart GaussNextFieldsPrepare64.control fieldControl
abbrev Label := BitMachineRawSequence.Label GaussNextFieldsPrepare64.Label GaussStepFields32.Label
abbrev Control := BitMachineRawSequence.Control GaussNextFieldsPrepare64.Control GaussStepFields32.Control
def start : Label := BitMachineRawSequence.leftLabel GaussNextFieldsPrepare64.start
def control : Control := (GaussNextFieldsPrepare64.control,fieldControl)

def initial (S : Bank → List Bool) : TM2.Cfg (fun _ : Bank => Bool) Label Control :=
  ⟨some start,control,S⟩

private theorem lift_field (S : Bank → List Bool) (t : Nat)
    (C : GaussStepFields32.Config)
    (he : ((advance GaussStepFields32.program)^[t])
      (⟨some fieldStart,fieldControl,fun z => S (GaussPivotPrepHigh64.low z)⟩ :
        GaussStepFields32.Config)=C) (hh : C.l=none) :
    ∃ u≤t,((advance fieldProgram)^[u])
      (⟨some fieldStart,fieldControl,S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
      ⟨none,C.var,BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low S C.stk⟩ := by
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs GaussPivotPrepHigh64.low S id id id
    (fun _ => rfl) none GaussStepFields32.program fieldProgram (fun _ => rfl)
    (⟨some fieldStart,fieldControl,fun z => S (GaussPivotPrepHigh64.low z)⟩ : GaussStepFields32.Config)
    t (by rw [he,hh])
  rw [he] at hr
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq,hh,Option.map_none,
    BitMachineStackEmbedding.bank_restrict] at hr
  exact ⟨u,hu,hr⟩

def pivotClock {m k : Nat} (s : GaussControlTrace.State m k) (S : Bank → List Bool)
    (hr : s.r < m) (hc : s.c < k) : Nat :=
  GaussNextFieldsPrepare64.clock S+
    GaussPivotQuadraticClock32.totalCoefficient*
      (GaussPivotByteSize32.byteCharge s
        (GaussNextFieldsPrepare64.foreign [true]
          (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc+1)^2+2

/-- Dirty search workspace is physically cleared, the saved original state
is copied back, and the fixed field controller writes the exact successor
including its ordered pivot list. Only the already computed matrix and search
tag are supplied at their physical banks; no prepared field-bank premise or
field-controller run is supplied. -/
theorem physical_pivot {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=some pivot)
    (hcount : s.r=s.pivots.length) (S : Bank → List Bool)
    (h56 : S 56=GaussControlTrace.statePacket s) (h20 : S 20=[true])
    (h22 : S 22=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)
    (h63 : S 63=[]) :
    ∃ t≤pivotClock s S hr hc,∃ v : Control,∃ T : Bank → List Bool,
      ((advance program)^[t]) (initial S)=⟨none,v,T⟩ ∧
      T 14=GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  let matrix := GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B
  let F := GaussNextFieldsPrepare64.foreign [true] matrix
  let R := GaussNextFieldsPrepare64.prepared S
  have hlow : (fun z => R (GaussPivotPrepHigh64.low z))=
      (GaussStepParseRun32.raw s F).stk :=
    GaussNextFieldsPrepare64.prepared_low s S [true] matrix h56 h20 h22
  obtain ⟨a,ha,hprep⟩ := GaussNextFieldsPrepare64.physical_prepare S h63
  obtain ⟨b,hb,hend,hout⟩ := GaussPivotQuadraticClock32.raw_pivot_quadratic_clock s hr hc pivot hp
    hcount F (by intro q; fin_cases q <;> simp [F,GaussNextFieldsPrepare64.foreign,GaussBranchFields32.dest])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,matrix,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by intro j; fin_cases j <;> simp [F,GaussNextFieldsPrepare64.foreign,GaussPivotFraming32.locate])
  let C0 : GaussStepFields32.Config := BitMachineInline.cfg (GaussStepFields32.Label.parse false)
    GaussStepFields32.eParse (some (.afterParse false)) (GaussStepParseRun32.raw s F)
  let C := GaussStepFields32.run (b+1) C0
  have hhalt : C.l=none := by
    unfold C
    rw [GaussStepFields32.run_add (show GaussStepFields32.run b C0=GaussStepFields32.run b C0 from rfl) 1]
    cases he : GaussStepFields32.run b C0 with
    | mk l v T =>
      have hl : l=some .done := by simpa only [C0,he] using hend
      subst l
      rfl
  have houtput : C.stk 14=GaussControlTrace.statePacket (GaussControlTrace.step s) := by
    unfold C
    rw [GaussStepFields32.run_add (show GaussStepFields32.run b C0=GaussStepFields32.run b C0 from rfl) 1]
    cases he : GaussStepFields32.run b C0 with
    | mk l v T =>
      have hl : l=some .done := by simpa only [C0,he] using hend
      have ht : T 14=GaussControlTrace.statePacket (GaussControlTrace.step s) := by
        simpa only [C0,he] using hout
      subst l
      exact ht
  have hstart : (⟨some fieldStart,fieldControl,fun z => R (GaussPivotPrepHigh64.low z)⟩ :
      GaussStepFields32.Config)=C0 := by
    rw [hlow]
    rfl
  have hlocal : ((advance GaussStepFields32.program)^[b+1])
      (⟨some fieldStart,fieldControl,fun z => R (GaussPivotPrepHigh64.low z)⟩ :
        GaussStepFields32.Config)=C := by rw [hstart]; rfl
  obtain ⟨u,hu,hfield⟩ := lift_field R (b+1) C hlocal hhalt
  let T := BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low R C.stk
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs GaussNextFieldsPrepare64.program fieldProgram
    GaussNextFieldsPrepare64.start fieldStart GaussNextFieldsPrepare64.control
    GaussNextFieldsPrepare64.control fieldControl C.var S R T a u hprep hfield
  refine ⟨t,?_,(GaussNextFieldsPrepare64.control,C.var),T,he,?_⟩
  · unfold pivotClock
    dsimp only [F,matrix] at hb
    omega
  · change T (GaussPivotPrepHigh64.low 14)=_
    dsimp only [T]
    rw [BitMachineStackEmbedding.bank_at]
    exact houtput

#print axioms physical_pivot

theorem physical_noPivot {m k : Nat} (s : GaussControlTrace.State m k)
    (S : Bank → List Bool) (matrix : List Bool)
    (h56 : S 56=GaussControlTrace.statePacket s) (h20 : S 20=[false])
    (h22 : S 22=matrix) (h63 : S 63=[]) :
    ∃ t : Nat,∃ v : Control,∃ T : Bank → List Bool,
      ((advance program)^[t]) (initial S)=⟨none,v,T⟩ ∧
      T 14=GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s) := by
  let F := GaussNextFieldsPrepare64.foreign [false] matrix
  let R := GaussNextFieldsPrepare64.prepared S
  have hlow : (fun z => R (GaussPivotPrepHigh64.low z))=
      (GaussStepParseRun32.raw s F).stk :=
    GaussNextFieldsPrepare64.prepared_low s S [false] matrix h56 h20 h22
  obtain ⟨a,ha,hprep⟩ := GaussNextFieldsPrepare64.physical_prepare S h63
  obtain ⟨b,hend,hout⟩ := GaussStepInactivePacket32.noPivot_packet s F
    (by intro q; fin_cases q <;> simp [F,GaussNextFieldsPrepare64.foreign,GaussBranchFields32.dest])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
    (by simp [F,GaussNextFieldsPrepare64.foreign])
  let C0 : GaussStepFields32.Config := BitMachineInline.cfg (GaussStepFields32.Label.parse false)
    GaussStepFields32.eParse (some (.afterParse false)) (GaussStepParseRun32.raw s F)
  let C := GaussStepFields32.run (b+1) C0
  have hhalt : C.l=none := by
    unfold C
    rw [GaussStepFields32.run_add (show GaussStepFields32.run b C0=GaussStepFields32.run b C0 from rfl) 1]
    cases he : GaussStepFields32.run b C0 with
    | mk l v T =>
      have hl : l=some .done := by simpa only [C0,he] using hend
      subst l
      rfl
  have houtput : C.stk 14=GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s) := by
    unfold C
    rw [GaussStepFields32.run_add (show GaussStepFields32.run b C0=GaussStepFields32.run b C0 from rfl) 1]
    cases he : GaussStepFields32.run b C0 with
    | mk l v T =>
      have hl : l=some .done := by simpa only [C0,he] using hend
      have ht : T 14=GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s) := by
        simpa only [C0,he] using hout
      subst l
      exact ht
  have hstart : (⟨some fieldStart,fieldControl,fun z => R (GaussPivotPrepHigh64.low z)⟩ :
      GaussStepFields32.Config)=C0 := by rw [hlow]; rfl
  obtain ⟨u,hu,hfield⟩ := lift_field R (b+1) C (by rw [hstart]; rfl) hhalt
  let T := BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low R C.stk
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs GaussNextFieldsPrepare64.program fieldProgram
    GaussNextFieldsPrepare64.start fieldStart GaussNextFieldsPrepare64.control
    GaussNextFieldsPrepare64.control fieldControl C.var S R T a u hprep hfield
  refine ⟨t,(GaussNextFieldsPrepare64.control,C.var),T,he,?_⟩
  change T (GaussPivotPrepHigh64.low 14)=_
  dsimp only [T]
  rw [BitMachineStackEmbedding.bank_at]
  exact houtput

#print axioms physical_noPivot
end
end CurrentAdditive.GaussNextStateFields64
