import EthInapproximability.CurrentPaper.WeightedLevelFieldsIdentity

/-! Lane owner:b-weighted-level-2, unit 2, segment 2 (partial, continued):
persistent writer field 15 (`nb = GraphVectors.auxiliaryCount s = 4*s*(s-3)`)
and the two count words that the admitted physical step's canonical-order
preparation reads at writer 8 (`s-3`) and writer 9 (`4*s`)
(`MatrixWeightedOrderPreparation.sourceBank … (Fintype.card VG) (s-3) (4*s)`).

ONE fixed controller: the checked `WeightedLevelFieldsIdentity.program`, then
a fixed tail: charged pop-until-empty clear of writer 15 (reached content not
assumed blank) → charged copy writer28 → writer8 → three pops on writer 8
(`s-3`, truncated subtraction as in `ℕ`) → constant `4` into writer 30 →
charged `multiply_run` writer30 × writer28 → writer9 (`4*s`) → charged
`multiply_run` writer9 × writer8 → writer15 (`4*s*(s-3)`) → pop clear of
writer 30. Only `s` (writer 28, produced by the frozen scalar controller) is
read. Scratch save 4..6 and writer 30 blank before and after. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelFields15

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevelColumnSave WeightedLevelFields1346

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-! ## Generic pop-until-empty and fixed-count pops -/

def popAllProgram (cell : Stack) : PopLabel →
    TM2.Stmt (fun _ : Stack => Bool) PopLabel (Unit × Option Bool)
  | .pop => BitMachineClearBank.clearStep cell PopLabel.pop PopLabel.stop
  | .stop => .halt

theorem popAll_run (cell : Stack) (S : Stack → List Bool) :
    ((advance (popAllProgram cell))^[(S cell).length + 2])
      (⟨some PopLabel.pop, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) PopLabel (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update S cell []⟩ := by
  have h := BitMachineClearBank.clear_one_run (popAllProgram cell) cell
    PopLabel.pop PopLabel.stop rfl () S
  rw [show (S cell).length + 2 = 1 + ((S cell).length + 1) by omega,
    Function.iterate_add_apply, h]
  rfl

def pop3Program (cell : Stack) :
    Fin 4 → TM2.Stmt (fun _ : Stack => Bool) (Fin 4) Unit :=
  fun i => if h : i.val < 3 then
      .pop cell (fun _ _ => ()) (.goto (fun _ => ⟨i.val + 1, by omega⟩))
    else .halt

theorem pop3_run (cell : Stack) (S : Stack → List Bool) :
    ((advance (pop3Program cell))^[4])
      (⟨some 0, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin 4) Unit) =
      ⟨none, (), Function.update S cell (S cell).tail.tail.tail⟩ := by
  show advance (pop3Program cell) (advance (pop3Program cell)
    (advance (pop3Program cell) (advance (pop3Program cell)
      (⟨some 0, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin 4) Unit)))) = _
  simp [advance, TM2.step, TM2.stepAux, pop3Program, Function.update_idem]

/-! ## Slots -/

def copy8 : Fin 3 ↪ Stack :=
  ⟨![wcell 28, wcell 8, save 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def mul9 : Fin 6 ↪ Stack :=
  ⟨![wcell 30, wcell 28, save 4, save 5, save 6, wcell 9], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def mul15 : Fin 6 ↪ Stack :=
  ⟨![wcell 9, wcell 8, save 4, save 5, save 6, wcell 15], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

/-! ## The fixed tail (right-nested raw sequence) -/

abbrev CC := Unit × Option Bool
abbrev CopyC := Option Bool

def seq6 := BitMachineRawSequence.program (multiplyProgram mul15)
  (popAllProgram (wcell 30)) PopLabel.pop false ((((), none)) : CC)
def init6 : Bool × CC := (false, ((), none))
def start6 := BitMachineRawSequence.leftLabel (LB := PopLabel)
  MatrixAddressMachine.Label.outer

def seq5 := BitMachineRawSequence.program (multiplyProgram mul9) seq6 start6
  false init6
def init5 := (false, init6)
def start5 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  MatrixAddressMachine.Label PopLabel) MatrixAddressMachine.Label.outer

def seq4 := BitMachineRawSequence.program (constProgram 4 (wcell 30)) seq5 start5
  () init5
def init4 := ((), init5)
def start4 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label PopLabel)) (0 : Fin 5)

def seq3 := BitMachineRawSequence.program (pop3Program (wcell 8)) seq4 start4
  () init4
def init3 := ((), init4)
def start3 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  (Fin 5) (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label PopLabel))) (0 : Fin 4)

def seq2 := BitMachineRawSequence.program (copyProgram copy8) seq3 start3
  (none : CopyC) init3
def init2 := ((none : CopyC), init3)
def start2 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  (Fin 4) (BitMachineRawSequence.Label
  (Fin 5) (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label PopLabel)))) BitMachineCopy.Label.scan

def tail2Program := BitMachineRawSequence.program (popAllProgram (wcell 15)) seq2
  start2 ((((), none)) : CC) init2
def tail2Initial := (((((), none)) : CC), init2)
def tail2Start := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label
  (Fin 4) (BitMachineRawSequence.Label
  (Fin 5) (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label PopLabel))))) PopLabel.pop

def counts15Bank (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update (Function.update (Function.update S
    (wcell 8) (List.replicate (s - 3) true))
    (wcell 9) (List.replicate (4 * s) true))
    (wcell 15) (List.replicate (4 * s * (s - 3)) true)

def tail2Cost (S : Stack → List Bool) (s : ℕ) : ℕ :=
  ((S (wcell 15)).length + 2) + (2 * s + 2) + 4 + (4 + 1) +
    MatrixAddressMachine.exactTime 4 s 0 +
    MatrixAddressMachine.exactTime (4 * s) (s - 3) 0 + (4 + 2) + 6

theorem tail2_run (S : Stack → List Bool) (s : ℕ)
    (h28 : S (wcell 28) = List.replicate s true)
    (h8 : S (wcell 8) = []) (h9 : S (wcell 9) = [])
    (hs4 : S (save 4) = []) (hs5 : S (save 5) = []) (hs6 : S (save 6) = [])
    (h30 : S (wcell 30) = []) :
    ∃ t ≤ tail2Cost S s,
      ((advance tail2Program)^[t])
        (⟨some tail2Start, tail2Initial, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, tail2Initial, counts15Bank S s⟩ := by
  let S1 := Function.update S (wcell 15) []
  let S2 := Function.update S1 (wcell 8) (List.replicate s true)
  let S3 := Function.update S1 (wcell 8) (List.replicate (s - 3) true)
  let S4 := Function.update S3 (wcell 30) (List.replicate 4 true)
  let S5 := Function.update S4 (wcell 9) (List.replicate (4 * s) true)
  let S6 := Function.update S5 (wcell 15) (List.replicate (4 * s * (s - 3)) true)
  let S7 := Function.update S6 (wcell 30) []
  have r1 := popAll_run (wcell 15) S
  -- copy s into writer 8
  have k2 := copy_run copy8 S1 (by
    show S1 (save 4) = []
    simp only [S1, Function.update_of_ne (save_ne_wcell 4 15)]
    exact hs4)
  have e28 : S1 (copy8 0) = List.replicate s true := by
    show S1 (wcell 28) = _
    simp only [S1, Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 15)]
    exact h28
  have e8 : S1 (copy8 1) = [] := by
    show S1 (wcell 8) = _
    simp only [S1, Function.update_of_ne (wcell_ne (by decide) : wcell 8 ≠ wcell 15)]
    exact h8
  rw [e28, e8, List.append_nil, List.length_replicate] at k2
  -- three pops: s - 3
  have r3 := pop3_run (wcell 8) S2
  have r3' : ((advance (pop3Program (wcell 8)))^[4])
      (⟨some 0, (), S2⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin 4) Unit) =
      ⟨none, (), S3⟩ := by
    rw [r3]
    have hw : (S2 (wcell 8)).tail.tail.tail = List.replicate (s - 3) true := by
      simp only [S2, Function.update_self, List.tail_replicate]
      congr 1
    rw [hw]
    simp only [S2, S3, Function.update_idem]
  -- constant 4 into writer 30
  have r4 := const_run 4 (wcell 30) S3 (by
    simp only [S3, S1,
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 8),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 15)]
    exact h30)
  -- 4 * s into writer 9
  have m5 := multiply_run mul9 S4 4 s
    (by show S4 (wcell 30) = _; simp only [S4, Function.update_self])
    (by
      show S4 (wcell 28) = _
      simp only [S4, S3, S1,
        Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 30),
        Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 8),
        Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 15)]
      exact h28)
    (by
      show S4 (save 4) = _
      simp only [S4, S3, S1, Function.update_of_ne (save_ne_wcell 4 30),
        Function.update_of_ne (save_ne_wcell 4 8),
        Function.update_of_ne (save_ne_wcell 4 15)]
      exact hs4)
    (by
      show S4 (save 5) = _
      simp only [S4, S3, S1, Function.update_of_ne (save_ne_wcell 5 30),
        Function.update_of_ne (save_ne_wcell 5 8),
        Function.update_of_ne (save_ne_wcell 5 15)]
      exact hs5)
    (by
      show S4 (save 6) = _
      simp only [S4, S3, S1, Function.update_of_ne (save_ne_wcell 6 30),
        Function.update_of_ne (save_ne_wcell 6 8),
        Function.update_of_ne (save_ne_wcell 6 15)]
      exact hs6)
  have e9 : S4 (mul9 5) = [] := by
    show S4 (wcell 9) = []
    simp only [S4, S3, S1,
      Function.update_of_ne (wcell_ne (by decide) : wcell 9 ≠ wcell 30),
      Function.update_of_ne (wcell_ne (by decide) : wcell 9 ≠ wcell 8),
      Function.update_of_ne (wcell_ne (by decide) : wcell 9 ≠ wcell 15)]
    exact h9
  rw [e9, List.append_nil] at m5
  -- 4 * s * (s - 3) into writer 15
  have m6 := multiply_run mul15 S5 (4 * s) (s - 3)
    (by show S5 (wcell 9) = _; simp only [S5, Function.update_self])
    (by
      show S5 (wcell 8) = _
      simp only [S5, S4, S3,
        Function.update_of_ne (wcell_ne (by decide) : wcell 8 ≠ wcell 9),
        Function.update_of_ne (wcell_ne (by decide) : wcell 8 ≠ wcell 30),
        Function.update_self])
    (by
      show S5 (save 4) = _
      simp only [S5, S4, S3, S1, Function.update_of_ne (save_ne_wcell 4 9),
        Function.update_of_ne (save_ne_wcell 4 30),
        Function.update_of_ne (save_ne_wcell 4 8),
        Function.update_of_ne (save_ne_wcell 4 15)]
      exact hs4)
    (by
      show S5 (save 5) = _
      simp only [S5, S4, S3, S1, Function.update_of_ne (save_ne_wcell 5 9),
        Function.update_of_ne (save_ne_wcell 5 30),
        Function.update_of_ne (save_ne_wcell 5 8),
        Function.update_of_ne (save_ne_wcell 5 15)]
      exact hs5)
    (by
      show S5 (save 6) = _
      simp only [S5, S4, S3, S1, Function.update_of_ne (save_ne_wcell 6 9),
        Function.update_of_ne (save_ne_wcell 6 30),
        Function.update_of_ne (save_ne_wcell 6 8),
        Function.update_of_ne (save_ne_wcell 6 15)]
      exact hs6)
  have e15 : S5 (mul15 5) = [] := by
    show S5 (wcell 15) = []
    simp only [S5, S4, S3, S1,
      Function.update_of_ne (wcell_ne (by decide) : wcell 15 ≠ wcell 9),
      Function.update_of_ne (wcell_ne (by decide) : wcell 15 ≠ wcell 30),
      Function.update_of_ne (wcell_ne (by decide) : wcell 15 ≠ wcell 8),
      Function.update_self]
  rw [e15, List.append_nil] at m6
  -- clear writer 30
  have r7 := popAll_run (wcell 30) S6
  have e30 : S6 (wcell 30) = List.replicate 4 true := by
    simp only [S6, S5, S4,
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 15),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 9),
      Function.update_self]
  rw [e30, List.length_replicate] at r7
  -- sequencing
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs
    (multiplyProgram mul15) (popAllProgram (wcell 30))
    MatrixAddressMachine.Label.outer PopLabel.pop false false
    ((((), none)) : CC) ((), none) S5 S6 S7
    (MatrixAddressMachine.exactTime (4 * s) (s - 3) 0) (4 + 2) m6 r7
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs
    (multiplyProgram mul9) seq6 MatrixAddressMachine.Label.outer start6
    false false init6 init6 S4 S5 S7
    (MatrixAddressMachine.exactTime 4 s 0) u6 m5 q6
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs
    (constProgram 4 (wcell 30)) seq5 0 start5 () () init5 init5 S3 S4 S7
    (4 + 1) u5 r4 q5
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs
    (pop3Program (wcell 8)) seq4 0 start4 () () init4 init4 S2 S3 S7
    4 u4 r3' q4
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs
    (copyProgram copy8) seq3 BitMachineCopy.Label.scan start3
    (none : CopyC) none init3 init3 S1 S2 S7 (2 * s + 2) u3 k2 q3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs
    (popAllProgram (wcell 15)) seq2 PopLabel.pop start2
    ((((), none)) : CC) ((), none) init2 init2 S S1 S7
    ((S (wcell 15)).length + 2) u2 r1 q2
  have hfin : S7 = counts15Bank S s := by
    funext k
    simp only [S7, S6, S5, S4, S3, S1, counts15Bank, Function.update_apply]
    by_cases k15 : k = wcell 15
    · subst k15; simp [wcell]
    by_cases k9 : k = wcell 9
    · subst k9; simp [wcell]
    by_cases k8 : k = wcell 8
    · subst k8; simp [wcell]
    by_cases k30 : k = wcell 30
    · subst k30; simp [wcell]; exact h30
    simp only [k15, k9, k8, k30, ↓reduceIte]
  refine ⟨u1, ?_, ?_⟩
  · unfold tail2Cost
    omega
  · rw [← hfin]
    exact q1

/-! ## Composition with the checked fields-1/3/4/6 controller, and identity -/

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

def program := BitMachineRawSequence.program WeightedLevelFieldsIdentity.program
  tail2Program tail2Start WeightedLevelFieldsIdentity.initialControl tail2Initial

def initialControl := (WeightedLevelFieldsIdentity.initialControl, tail2Initial)

/-- Fixed push constant of the checked fields-1/3/4/6 controller. -/
def fieldsPush : ℕ := BitMachineStackGrowth.perStep WeightedLevelFieldsIdentity.program

def publicBound15 (i : Parameters.Input) (g : EncodedGraph.Graph) (e : ℕ)
    (W : Fin 64 → List Bool) (a s q L B C S : ℕ) : ℕ :=
  let P := WeightedLevelFieldsIdentity.publicBound1346 i g e W a s q L B C S
  P + ((fieldsPush * P + 2) + (2 * S + 2) + 4 + (4 + 1) +
    MatrixAddressMachine.exactTime 4 S 0 +
    MatrixAddressMachine.exactTime (4 * S) (S - 3) 0 + (4 + 2) + 6) + 1

theorem bank15 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 15 =
      List.replicate d.nb true := by
  simp [MatrixWeightedEntryController.persistentBank]

/-- One level, same constructor, one public clock: twelve persistent writer
fields of `actualD` (1, 3, 4, 6, 15, 16, 17, 21, 26, 27, 28, 29) and the two
canonical-order count words `s-3` (writer 8) and `4*s` (writer 9) for the SAME
step, physically produced, plus the retained `a`, `q`, `L`, `s*L`. -/
theorem level_fields15_identity (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
    let g := EncodedETHSource.serializeGraph G
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    let L := PrimeSampler.size q (Parameters.balanceOrder i)
      (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
      let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
      let X := Function.update (exitBank T a s q L i.rows i.columns)
        (wcell 16) (List.replicate (s * L) true)
      let Y := fieldsBank X d.binBase d.rawWidth d.s
      let Z := counts15Bank Y d.s
      ∃ u ≤ publicBound15 i g (Fintype.card EG) W a s q L
          d.binBase d.rawWidth d.s,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
            initialControl, WeightedLevelColumnSave.initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, initialControl, Z⟩ ∧
        Z (wcell 1) = MatrixWeightedEntryController.persistentBank d 1 ∧
        Z (wcell 3) = MatrixWeightedEntryController.persistentBank d 3 ∧
        Z (wcell 4) = MatrixWeightedEntryController.persistentBank d 4 ∧
        Z (wcell 6) = MatrixWeightedEntryController.persistentBank d 6 ∧
        Z (wcell 15) = MatrixWeightedEntryController.persistentBank d 15 ∧
        Z (wcell 16) = MatrixWeightedEntryController.persistentBank d 16 ∧
        Z (wcell 17) = MatrixWeightedEntryController.persistentBank d 17 ∧
        Z (wcell 27) = MatrixWeightedEntryController.persistentBank d 27 ∧
        Z (wcell 28) = MatrixWeightedEntryController.persistentBank d 28 ∧
        Z (wcell 21) = MatrixWeightedEntryController.persistentBank d 21 ∧
        Z (wcell 26) = MatrixWeightedEntryController.persistentBank d 26 ∧
        Z (wcell 29) = MatrixWeightedEntryController.persistentBank d 29 ∧
        Z (wcell 8) = List.replicate (Iteration.s G c b y lvl M - 3) true ∧
        Z (wcell 9) = List.replicate (4 * Iteration.s G c b y lvl M) true ∧
        Z (save 0) = List.replicate (Iteration.a G c b y lvl M) true ∧
        Z (save 1) = List.replicate (Iteration.q₂ G c b y lvl M) true ∧
        Z (save 2) = List.replicate (Iteration.labels G c b y lvl M) true ∧
        Z (save 3) = List.replicate d.stagePrefixRows true := by
  intro d i g s q a L W''
  obtain ⟨F, Q, P, hY⟩ := WeightedLevelFieldsIdentity.level_fields_identity
    G c b y lvl M W h17 h62 h27 h63 h28 h61 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T X Y Z
  obtain ⟨u, hu, hrun, p1, p3, p4, p6, p16, p17, p27, p28, p21, p26, p29,
    ps0, ps1, ps2, ps3⟩ := hY
  have hu' : u ≤ WeightedLevelFieldsIdentity.publicBound1346 i g (Fintype.card EG) W
      a s q L d.binBase d.rawWidth d.s := hu
  have y28 : Y (wcell 28) = List.replicate d.s true :=
    p28.trans (WeightedLevelIdentity.bank28 d)
  -- blank cells of Y: writer 8, 9, 30 and save 4..6
  have yx (k : Stack) (h1 : k ≠ wcell 1) (h3 : k ≠ wcell 3) (h4 : k ≠ wcell 4)
      (h6 : k ≠ wcell 6) : Y k = X k := by
    show fieldsBank X d.binBase d.rawWidth d.s k = X k
    simp only [fieldsBank, Function.update_of_ne h1, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h6]
  have xb (k : Fin 64) (j : Fin 40) (hj : 13 ≤ j.val)
      (hk : ColumnWriterJoin.slots j = k) (hk16 : k ≠ 16) : X (wcell k) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (wcell k) = []
    rw [Function.update_of_ne (wcell_ne hk16)]
    have hb := (WeightedColumnActualStage.exit_blank T a s q L i.rows i.columns).2.1 j hj
    rw [hk] at hb
    exact hb
  have xsv (j : Fin 7) (hj : j = 4 ∨ j = 5 ∨ j = 6) : X (save j) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (save j) = []
    rw [Function.update_of_ne (save_ne_wcell j 16)]
    rcases hj with rfl | rfl | rfl <;> rfl
  have y8 : Y (wcell 8) = [] := by
    rw [yx (wcell 8) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact xb 8 13 (by decide) (by decide) (by decide)
  have y9 : Y (wcell 9) = [] := by
    rw [yx (wcell 9) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact xb 9 14 (by decide) (by decide) (by decide)
  have y30 : Y (wcell 30) = [] := by
    rw [yx (wcell 30) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact xb 30 25 (by decide) (by decide) (by decide)
  have ys (j : Fin 7) (hj : j = 4 ∨ j = 5 ∨ j = 6) : Y (save j) = [] := by
    rw [yx (save j) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
      (save_ne_wcell _ _)]
    exact xsv j hj
  obtain ⟨t, ht, htail⟩ := tail2_run Y d.s y28 y8 y9
    (ys 4 (Or.inl rfl)) (ys 5 (Or.inr (Or.inl rfl))) (ys 6 (Or.inr (Or.inr rfl))) y30
  obtain ⟨v, hv, hr⟩ := BitMachineRawSequence.runs
    WeightedLevelFieldsIdentity.program tail2Program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    tail2Start
    WeightedLevelFieldsIdentity.initialControl WeightedLevelFieldsIdentity.initialControl
    tail2Initial tail2Initial
    (WeightedLevelColumnSave.initialBank i g W) Y Z u t hrun htail
  -- public majorant of the charged clear of writer 15 (initially blank by h15)
  have grow : (Y (wcell 15)).length ≤ fieldsPush *
      WeightedLevelFieldsIdentity.publicBound1346 i g (Fintype.card EG) W
        a s q L d.binBase d.rawWidth d.s := by
    have h := BitMachineStackGrowth.run_growth WeightedLevelFieldsIdentity.program
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
        WeightedLevelFieldsIdentity.initialControl,
        WeightedLevelColumnSave.initialBank i g W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) u (wcell 15)
    rw [hrun] at h
    have hi : WeightedLevelColumnSave.initialBank i g W (wcell 15) = [] :=
      (WeightedLevelPublicClock.initial_writer i g W 15).trans h15
    have hm : fieldsPush * u ≤ fieldsPush *
        WeightedLevelFieldsIdentity.publicBound1346 i g (Fintype.card EG) W
          a s q L d.binBase d.rawWidth d.s :=
      Nat.mul_le_mul_left _ hu'
    change (Y (wcell 15)).length ≤
      (WeightedLevelColumnSave.initialBank i g W (wcell 15)).length +
        BitMachineStackGrowth.perStep WeightedLevelFieldsIdentity.program * u at h
    rw [hi, List.length_nil, Nat.zero_add] at h
    unfold fieldsPush
    unfold fieldsPush at hm
    omega
  -- cell facts of the exit bank
  have zo (k : Stack) (h8 : k ≠ wcell 8) (h9 : k ≠ wcell 9) (h15 : k ≠ wcell 15) :
      Z k = Y k := by
    show counts15Bank Y d.s k = Y k
    simp only [counts15Bank, Function.update_of_ne h8, Function.update_of_ne h9,
      Function.update_of_ne h15]
  have hnb : d.nb = 4 * d.s * (d.s - 3) := rfl
  refine ⟨v, ?_, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold tail2Cost at ht
    unfold publicBound15
    dsimp only
    omega
  · rw [zo (wcell 1) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p1
  · rw [zo (wcell 3) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p3
  · rw [zo (wcell 4) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p4
  · rw [zo (wcell 6) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p6
  · show counts15Bank Y d.s (wcell 15) = _
    simp only [counts15Bank, Function.update_self]
    rw [bank15, hnb]
  · rw [zo (wcell 16) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p16
  · rw [zo (wcell 17) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p17
  · rw [zo (wcell 27) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p27
  · rw [zo (wcell 28) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p28
  · rw [zo (wcell 21) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p21
  · rw [zo (wcell 26) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p26
  · rw [zo (wcell 29) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))]
    exact p29
  · show counts15Bank Y d.s (wcell 8) = _
    simp only [counts15Bank,
      Function.update_of_ne (wcell_ne (by decide) : wcell 8 ≠ wcell 15),
      Function.update_of_ne (wcell_ne (by decide) : wcell 8 ≠ wcell 9),
      Function.update_self]
    rfl
  · show counts15Bank Y d.s (wcell 9) = _
    simp only [counts15Bank,
      Function.update_of_ne (wcell_ne (by decide) : wcell 9 ≠ wcell 15),
      Function.update_self]
    rfl
  · rw [zo (save 0) (wcell_ne_save _ _ ).symm (wcell_ne_save _ _).symm (wcell_ne_save _ _).symm]
    exact ps0
  · rw [zo (save 1) (wcell_ne_save _ _ ).symm (wcell_ne_save _ _).symm (wcell_ne_save _ _).symm]
    exact ps1
  · rw [zo (save 2) (wcell_ne_save _ _ ).symm (wcell_ne_save _ _).symm (wcell_ne_save _ _).symm]
    exact ps2
  · rw [zo (save 3) (wcell_ne_save _ _ ).symm (wcell_ne_save _ _).symm (wcell_ne_save _ _).symm]
    exact ps3

#print axioms popAll_run
#print axioms pop3_run
#print axioms tail2_run
#print axioms level_fields15_identity

end
end EthInapproximability.CurrentPaper.WeightedLevelFields15
