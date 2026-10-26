import EthInapproximability.CurrentPaper.MatrixStage4AlignmentFromOrdinal
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Source-preserving ordinal copy into the alignment decoder

A fixed three-stack copy preserves the original unary raw-column ordinal in
bank 19 and writes a copy into alignment input bank 15. The nineteen-stack
alignment decoder then consumes that copied ordinal. Bank 20 is copy scratch.
The output alignment bit remains in the finite control, and the original
ordinal remains available for the later graph-source phase.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4OrdinalCopyAlignment

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 21
abbrev Label := BitMachineCopy.Label ⊕
  (MatrixStage4AlignmentFromOrdinal.Label ⊕ Unit)
abbrev Control := Option Bool × MatrixStage4AlignmentFromOrdinal.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev CopyConfig := TM2.Cfg (fun _ : Fin 3 => Bool)
  BitMachineCopy.Label (Option Bool)

def copyStart : Label := .inl .scan
def alignStart : Label := .inr (.inl MatrixStage4AlignmentFromOrdinal.splitStart)
def done : Label := .inr (.inr ())

def copyPermutation : Stack ≃ Stack where
  toFun := ![19,15,20,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18]
  invFun := ![3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,1,18,19,20,0,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyStacks : Fin 3 ⊕ Fin 18 ≃ Stack :=
  finSumFinEquiv.trans copyPermutation
def alignStacks : Fin 19 ⊕ Fin 2 ≃ Stack := finSumFinEquiv

def alignLabels : MatrixStage4AlignmentFromOrdinal.Label ⊕
    (BitMachineCopy.Label ⊕ Unit) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inr u)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inr u)
  left_inv l := by rcases l with l | (l | u) <;> rfl
  right_inv l := by rcases l with l | (l | u) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt copyStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4AlignmentFromOrdinal.splitStart))
        (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt alignStacks alignLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr ()))
        (MatrixStage4AlignmentFromOrdinal.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def copyFrame (alignControl : MatrixStage4AlignmentFromOrdinal.Control)
    (foreign : Fin 18 → List Bool) (c : CopyConfig) : Config :=
  renameCfg copyStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4AlignmentFromOrdinal.splitStart))
      alignControl foreign c)

theorem copy_phase (alignControl : MatrixStage4AlignmentFromOrdinal.Control)
    (foreign : Fin 18 → List Bool) (c : CopyConfig)
    (bound : ℕ) (hhalt : (BitMachineCopy.run bound c).l = none) :
    ∃ t ≤ bound, run t (copyFrame alignControl foreign c) =
      copyFrame alignControl foreign (BitMachineCopy.run bound c) := by
  apply lift_outputs_renamed copyStacks (Equiv.refl _) (Equiv.refl _)
    BitMachineCopy.program program
    (some (.inl MatrixStage4AlignmentFromOrdinal.splitStart))
  · intro l
    rfl
  · exact hhalt

def alignmentFrame (copyControl : Option Bool) (foreign : Fin 2 → List Bool)
    (c : MatrixStage4AlignmentFromOrdinal.Config) : Config :=
  renameCfg alignStacks alignLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) copyControl foreign c)

theorem alignment_phase (copyControl : Option Bool)
    (foreign : Fin 2 → List Bool)
    (c : MatrixStage4AlignmentFromOrdinal.Config) (bound : ℕ)
    (hhalt : (MatrixStage4AlignmentFromOrdinal.run bound c).l = none) :
    ∃ t ≤ bound, run t (alignmentFrame copyControl foreign c) =
      alignmentFrame copyControl foreign
        (MatrixStage4AlignmentFromOrdinal.run bound c) := by
  apply lift_outputs_renamed alignStacks alignLabels (Equiv.prodComm _ _)
    MatrixStage4AlignmentFromOrdinal.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def copyForeign (target : MatrixStage4AlignmentFromOrdinal.Config) :
    Fin 18 → List Bool :=
  fun j => target.stk ⟨(copyStacks (.inr j)).val,by
    fin_cases j <;> decide⟩

def originalForeign (bits : List Bool) : Fin 2 → List Bool :=
  ![bits,[]]

theorem bridge (target : MatrixStage4AlignmentFromOrdinal.Config)
    (bits : List Bool)
    (hl : target.l = some MatrixStage4AlignmentFromOrdinal.splitStart)
    (hbits : target.stk 15 = bits) :
    copyFrame target.var (copyForeign target)
      (BitMachineCopy.cfg none none bits bits []) =
      alignmentFrame none (originalForeign bits) target := by
  cases target with
  | mk l v S =>
    cases l with
    | none => simp at hl
    | some l =>
      have he : l = MatrixStage4AlignmentFromOrdinal.splitStart :=
        Option.some.inj hl
      subst l
      unfold copyFrame copyForeign alignmentFrame originalForeign
        renameCfg liftCfg BitMachineCopy.cfg
      congr 1
      funext k
      fin_cases k <;> first | simpa only using hbits.symm | rfl

theorem finish (c : Config) (hc : c.l = some done) :
    run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp at hc
    | some l =>
      have hl : l = done := Option.some.inj hc
      subst l
      simp [run,advance,done,program,TM2.step,TM2.stepAux]

open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

def alignmentInput {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) : MatrixStage4AlignmentFromOrdinal.Config :=
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let outer := base^s
  MatrixStage4AlignmentFromOrdinal.splitFrame
    (List.replicate base true) (List.replicate wordSize true)
    (List.replicate (s-1) true)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate code.val true) (List.replicate outer true)
      [] [] [] [])

theorem copy_alignment_run {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let outer := base^s
    let n := code.val%outer
    let reference := selectorDigit code (firstBin s hs)
    let target := alignmentInput code
    let input := copyFrame target.var (copyForeign target)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate code.val true) [] [])
    ∃ t ≤ (2*code.val+2)+
      (MatrixUnaryDivision.totalTime code.val outer+
        MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
        MatrixStage4AlignmentStream.budget
          (MatrixStage4AlignmentCorrect.selectorWords code) reference+3)+1,
      (run t input).l = none ∧
      (run t input).stk 19 = List.replicate code.val true ∧
      ((run t input).var.2.2.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) ∧
      (run t input).stk 14 = List.replicate (code.val/outer) true := by
  dsimp
  let target := alignmentInput code
  let source := List.replicate code.val true
  let cin := BitMachineCopy.cfg (some .scan) none source [] []
  have hcopy : BitMachineCopy.run (2*code.val+2) cin =
      BitMachineCopy.cfg none none source source [] := by
    simpa only [cin,source,List.length_replicate,List.append_nil]
      using BitMachineCopy.run_correct none source []
  obtain ⟨t₁,ht₁,h₁⟩ := copy_phase target.var (copyForeign target)
    cin (2*code.val+2) (by rw [hcopy]; rfl)
  rw [hcopy] at h₁
  have hb : copyFrame target.var (copyForeign target)
      (BitMachineCopy.cfg none none source source []) =
      alignmentFrame none (originalForeign source) target := by
    apply bridge target source
    · rfl
    · have hmap : MatrixStage4AlignmentFromOrdinal.splitStacks.symm
          (15 : Fin 19) = Sum.inl (0 : Fin 6) := by decide
      simp only [target,source,alignmentInput,
        MatrixStage4AlignmentFromOrdinal.splitFrame,
        renameCfg,liftCfg,MatrixUnaryDivision.cfg,hmap,Sum.elim_inl]
      rfl
  obtain ⟨ta,hta,hal,hflag,hquo⟩ :=
    MatrixStage4AlignmentFromOrdinal.raw_ordinal_alignment_run hs code
  have hhalt : (MatrixStage4AlignmentFromOrdinal.run ta target).l = none := by
    simpa only [target,alignmentInput] using hal
  obtain ⟨t₂,ht₂,h₂⟩ := alignment_phase none
    (originalForeign source) target ta hhalt
  let terminal := alignmentFrame none (originalForeign source)
    (MatrixStage4AlignmentFromOrdinal.run ta target)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,alignmentFrame,renameCfg,liftCfg]
    rw [hhalt]
    rfl
  have hf := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hf] at h123
  refine ⟨t₁+t₂+1,?_,?_,?_,?_,?_⟩
  · omega
  · rw [h123]
  · rw [h123]
    rfl
  · rw [h123]
    simpa only [terminal,alignmentFrame,renameCfg,liftCfg,target,alignmentInput]
      using hflag
  · rw [h123]
    simpa only [terminal,alignmentFrame,renameCfg,liftCfg,target,alignmentInput]
      using hquo

end EthInapproximability.CurrentPaper.MatrixStage4OrdinalCopyAlignment
