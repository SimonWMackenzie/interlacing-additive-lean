import EthInapproximability.CurrentPaper.MatrixStage4Decode
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Fixed four-division raw Stage--4 column decoder

Source: frozen v8 `B-effectivity-details.tex`, `thm:paper-materialization`.
The four phase inputs are unary: the raw column ordinal, bin-tuple stride,
selected-bin stride, bin base, and first-word base. Power construction and
selection of the bin stride from the decoded row are distinct charged stages.
No quotient or read is performed by the finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 16
abbrev Label := MatrixUnaryDivision.Label ⊕
  (MatrixUnaryDivision.Label ⊕
    (MatrixUnaryDivision.Label ⊕ (MatrixUnaryDivision.Label ⊕ Unit)))
abbrev Control := Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (false,false)
def outerStart : Label := .inl .start
def strideStart : Label := .inr (.inl .start)
def digitStart : Label := .inr (.inr (.inl .start))
def wordStart : Label := .inr (.inr (.inr (.inl .start)))
def done : Label := .inr (.inr (.inr (.inr ())))

def outerPermutation : Stack ≃ Stack where
  toFun := ![0,1,5,6,10,11,2,3,4,7,8,9,12,13,14,15]
  invFun := ![0,1,6,7,8,2,3,9,10,11,4,5,12,13,14,15]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def stridePermutation : Stack ≃ Stack where
  toFun := ![6,2,5,7,8,11,0,1,3,4,9,10,12,13,14,15]
  invFun := ![6,7,1,8,9,2,0,3,4,10,11,5,12,13,14,15]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def digitPermutation : Stack ≃ Stack where
  toFun := ![8,3,5,12,13,11,0,1,2,4,6,7,9,10,14,15]
  invFun := ![6,7,8,1,9,2,10,11,0,12,13,5,3,4,14,15]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def wordPermutation : Stack ≃ Stack where
  toFun := ![12,4,5,14,15,11,0,1,2,3,6,7,8,9,10,13]
  invFun := ![6,7,8,9,1,2,10,11,12,13,14,5,0,15,3,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def outerStacks : Fin 6 ⊕ Fin 10 ≃ Stack :=
  finSumFinEquiv.trans outerPermutation
def strideStacks : Fin 6 ⊕ Fin 10 ≃ Stack :=
  finSumFinEquiv.trans stridePermutation
def digitStacks : Fin 6 ⊕ Fin 10 ≃ Stack :=
  finSumFinEquiv.trans digitPermutation
def wordStacks : Fin 6 ⊕ Fin 10 ≃ Stack :=
  finSumFinEquiv.trans wordPermutation

def strideLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryDivision.Label ⊕
      (MatrixUnaryDivision.Label ⊕ (MatrixUnaryDivision.Label ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  left_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl
  right_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl

def digitLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryDivision.Label ⊕
      (MatrixUnaryDivision.Label ⊕ (MatrixUnaryDivision.Label ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  left_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl
  right_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl

def wordLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryDivision.Label ⊕
      (MatrixUnaryDivision.Label ⊕ (MatrixUnaryDivision.Label ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inr (.inl l)))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inl l))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inl l))) => .inl l
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  left_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl
  right_inv l := by rcases l with l | (l | (l | (l | u))) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt outerStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start))
        (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt strideStacks strideLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inl MatrixUnaryDivision.Label.start)))
        (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) => renameStmt digitStacks digitLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inr (.inl MatrixUnaryDivision.Label.start))))
        (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr (.inl l))) => renameStmt wordStacks wordLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inr (.inr ()))))
        (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr (.inr ()))) => load (fun _ => initial) halt

def cfg (l : Option Label) (v : Control)
    (code outerDiv strideDiv binBase wordBase binCode strideRem strideQuot
      tailCode digit extra word alpha : List Bool) : Config :=
  ⟨l,v,![code,outerDiv,strideDiv,binBase,wordBase,[],binCode,strideRem,
    strideQuot,[],tailCode,[],digit,extra,word,alpha]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def outerFrame (strideDiv binBase wordBase strideRem strideQuot digit extra word alpha
    : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg outerStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) false
      (fun i => ![strideDiv,binBase,wordBase,strideRem,strideQuot,[],
        digit,extra,word,alpha] i) c)

theorem outer_run (n outerDiv : ℕ)
    (strideDiv binBase wordBase : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n outerDiv,
      run t (cfg (some outerStart) initial
        (List.replicate n true) (List.replicate outerDiv true)
        strideDiv binBase wordBase [] [] [] [] [] [] [] []) =
      cfg (some strideStart) initial [] (List.replicate outerDiv true)
        strideDiv binBase wordBase (List.replicate (n%outerDiv) true)
        [] [] (List.replicate (n/outerDiv) true) [] [] [] [] := by
  have he := MatrixUnaryDivision.division_total_run n outerDiv
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed outerStacks
    (Equiv.refl _) (Equiv.refl _) MatrixUnaryDivision.program program
    (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl) false
    (fun i => ![strideDiv,binBase,wordBase,[],[],[],[],[],[],[]] i)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate n true) (List.replicate outerDiv true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n outerDiv)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n outerDiv])
        _ = _ from he]
      rfl)
  change run t (outerFrame strideDiv binBase wordBase [] [] [] [] [] [] _) =
    outerFrame strideDiv binBase wordBase [] [] [] [] [] []
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : outerFrame strideDiv binBase wordBase [] [] [] [] [] []
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate n true) (List.replicate outerDiv true) [] [] [] []) =
      cfg (some outerStart) initial
        (List.replicate n true) (List.replicate outerDiv true)
        strideDiv binBase wordBase [] [] [] [] [] [] [] [] := by
    unfold outerFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : outerFrame strideDiv binBase wordBase [] [] [] [] [] []
      (MatrixUnaryDivision.cfg none false [] (List.replicate outerDiv true) []
        (List.replicate (n%outerDiv) true) (List.replicate (n/outerDiv) true) []) =
      cfg (some strideStart) initial [] (List.replicate outerDiv true)
        strideDiv binBase wordBase (List.replicate (n%outerDiv) true)
        [] [] (List.replicate (n/outerDiv) true) [] [] [] [] := by
    unfold outerFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def strideFrame (outerDiv binBase wordBase tailCode digit extra word alpha
    : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg strideStacks strideLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inl MatrixUnaryDivision.Label.start))) false
      (fun i => ![[],outerDiv,binBase,wordBase,[],tailCode,
        digit,extra,word,alpha] i) c)

theorem stride_run (n strideDiv : ℕ)
    (outerDiv binBase wordBase tailCode : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n strideDiv,
      run t (cfg (some strideStart) initial [] outerDiv
        (List.replicate strideDiv true) binBase wordBase
        (List.replicate n true) [] [] tailCode [] [] [] []) =
      cfg (some digitStart) initial [] outerDiv
        (List.replicate strideDiv true) binBase wordBase
        [] (List.replicate (n%strideDiv) true)
        (List.replicate (n/strideDiv) true) tailCode [] [] [] [] := by
  have he := MatrixUnaryDivision.division_total_run n strideDiv
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed strideStacks strideLabels
    (Equiv.refl _) MatrixUnaryDivision.program program
    (some (.inr (.inl MatrixUnaryDivision.Label.start)))
    (fun _ => rfl) false
    (fun i => ![[],outerDiv,binBase,wordBase,[],tailCode,[],[],[],[]] i)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate n true) (List.replicate strideDiv true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n strideDiv)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n strideDiv])
        _ = _ from he]
      rfl)
  change run t (strideFrame outerDiv binBase wordBase tailCode [] [] [] [] _) =
    strideFrame outerDiv binBase wordBase tailCode [] [] [] []
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : strideFrame outerDiv binBase wordBase tailCode [] [] [] []
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate n true) (List.replicate strideDiv true) [] [] [] []) =
      cfg (some strideStart) initial [] outerDiv
        (List.replicate strideDiv true) binBase wordBase
        (List.replicate n true) [] [] tailCode [] [] [] [] := by
    unfold strideFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : strideFrame outerDiv binBase wordBase tailCode [] [] [] []
      (MatrixUnaryDivision.cfg none false [] (List.replicate strideDiv true) []
        (List.replicate (n%strideDiv) true)
        (List.replicate (n/strideDiv) true) []) =
      cfg (some digitStart) initial [] outerDiv
        (List.replicate strideDiv true) binBase wordBase
        [] (List.replicate (n%strideDiv) true)
        (List.replicate (n/strideDiv) true) tailCode [] [] [] [] := by
    unfold strideFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def digitFrame (outerDiv strideDiv wordBase strideRem tailCode word alpha
    : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg digitStacks digitLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inr (.inl MatrixUnaryDivision.Label.start)))) false
      (fun i => ![[],outerDiv,strideDiv,wordBase,[],strideRem,
        [],tailCode,word,alpha] i) c)

theorem digit_run (n binBase : ℕ)
    (outerDiv strideDiv wordBase strideRem tailCode : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n binBase,
      run t (cfg (some digitStart) initial [] outerDiv strideDiv
        (List.replicate binBase true) wordBase [] strideRem
        (List.replicate n true) tailCode [] [] [] []) =
      cfg (some wordStart) initial [] outerDiv strideDiv
        (List.replicate binBase true) wordBase [] strideRem []
        tailCode (List.replicate (n%binBase) true)
        (List.replicate (n/binBase) true) [] [] := by
  have he := MatrixUnaryDivision.division_total_run n binBase
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed digitStacks digitLabels
    (Equiv.refl _) MatrixUnaryDivision.program program
    (some (.inr (.inr (.inl MatrixUnaryDivision.Label.start))))
    (fun _ => rfl) false
    (fun i => ![[],outerDiv,strideDiv,wordBase,[],strideRem,
      [],tailCode,[],[]] i)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate n true) (List.replicate binBase true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n binBase)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n binBase])
        _ = _ from he]
      rfl)
  change run t (digitFrame outerDiv strideDiv wordBase strideRem tailCode [] [] _) =
    digitFrame outerDiv strideDiv wordBase strideRem tailCode [] []
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : digitFrame outerDiv strideDiv wordBase strideRem tailCode [] []
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate n true) (List.replicate binBase true) [] [] [] []) =
      cfg (some digitStart) initial [] outerDiv strideDiv
        (List.replicate binBase true) wordBase [] strideRem
        (List.replicate n true) tailCode [] [] [] [] := by
    unfold digitFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : digitFrame outerDiv strideDiv wordBase strideRem tailCode [] []
      (MatrixUnaryDivision.cfg none false [] (List.replicate binBase true) []
        (List.replicate (n%binBase) true)
        (List.replicate (n/binBase) true) []) =
      cfg (some wordStart) initial [] outerDiv strideDiv
        (List.replicate binBase true) wordBase [] strideRem []
        tailCode (List.replicate (n%binBase) true)
        (List.replicate (n/binBase) true) [] [] := by
    unfold digitFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def wordFrame (outerDiv strideDiv binBase strideRem tailCode extra : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg wordStacks wordLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inr (.inr ())))) false
      (fun i => ![[],outerDiv,strideDiv,binBase,[],strideRem,
        [],[],tailCode,extra] i) c)

theorem word_run (n wordBase : ℕ)
    (outerDiv strideDiv binBase strideRem tailCode extra : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n wordBase,
      run t (cfg (some wordStart) initial [] outerDiv strideDiv
        binBase (List.replicate wordBase true) [] strideRem []
        tailCode (List.replicate n true) extra [] []) =
      cfg (some done) initial [] outerDiv strideDiv
        binBase (List.replicate wordBase true) [] strideRem []
        tailCode [] extra (List.replicate (n%wordBase) true)
        (List.replicate (n/wordBase) true) := by
  have he := MatrixUnaryDivision.division_total_run n wordBase
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed wordStacks wordLabels
    (Equiv.refl _) MatrixUnaryDivision.program program
    (some (.inr (.inr (.inr ()))))
    (fun _ => rfl) false
    (fun i => ![[],outerDiv,strideDiv,binBase,[],strideRem,
      [],[],tailCode,extra] i)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate n true) (List.replicate wordBase true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n wordBase)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n wordBase])
        _ = _ from he]
      rfl)
  change run t (wordFrame outerDiv strideDiv binBase strideRem tailCode extra _) =
    wordFrame outerDiv strideDiv binBase strideRem tailCode extra
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : wordFrame outerDiv strideDiv binBase strideRem tailCode extra
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate n true) (List.replicate wordBase true) [] [] [] []) =
      cfg (some wordStart) initial [] outerDiv strideDiv
        binBase (List.replicate wordBase true) [] strideRem []
        tailCode (List.replicate n true) extra [] [] := by
    unfold wordFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : wordFrame outerDiv strideDiv binBase strideRem tailCode extra
      (MatrixUnaryDivision.cfg none false [] (List.replicate wordBase true) []
        (List.replicate (n%wordBase) true)
        (List.replicate (n/wordBase) true) []) =
      cfg (some done) initial [] outerDiv strideDiv
        binBase (List.replicate wordBase true) [] strideRem []
        tailCode [] extra (List.replicate (n%wordBase) true)
        (List.replicate (n/wordBase) true) := by
    unfold wordFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem done_run (outerDiv strideDiv binBase wordBase strideRem tailCode extra word alpha
    : List Bool) :
    run 1 (cfg (some done) initial [] outerDiv strideDiv binBase wordBase
      [] strideRem [] tailCode [] extra word alpha) =
    cfg none initial [] outerDiv strideDiv binBase wordBase
      [] strideRem [] tailCode [] extra word alpha := by
  simp [run,advance,cfg,done,program,TM2.step,TM2.stepAux]

theorem column_run (n outerDiv strideDiv binBase wordBase : ℕ) :
    let b := n%outerDiv
    let k := b/strideDiv
    let d := k%binBase
    let h := k/binBase
    ∃ t ≤ MatrixUnaryDivision.totalTime n outerDiv+
      MatrixUnaryDivision.totalTime b strideDiv+
      MatrixUnaryDivision.totalTime k binBase+
      MatrixUnaryDivision.totalTime d wordBase+1,
      run t (cfg (some outerStart) initial
        (List.replicate n true) (List.replicate outerDiv true)
        (List.replicate strideDiv true) (List.replicate binBase true)
        (List.replicate wordBase true) [] [] [] [] [] [] [] []) =
      cfg none initial [] (List.replicate outerDiv true)
        (List.replicate strideDiv true) (List.replicate binBase true)
        (List.replicate wordBase true) []
        (List.replicate (b%strideDiv) true) []
        (List.replicate (n/outerDiv) true) [] (List.replicate h true)
        (List.replicate (d%wordBase) true)
        (List.replicate (d/wordBase) true) := by
  dsimp
  obtain ⟨t₁,ht₁,h₁⟩ := outer_run n outerDiv
    (List.replicate strideDiv true) (List.replicate binBase true)
    (List.replicate wordBase true)
  obtain ⟨t₂,ht₂,h₂⟩ := stride_run (n%outerDiv) strideDiv
    (List.replicate outerDiv true) (List.replicate binBase true)
    (List.replicate wordBase true) (List.replicate (n/outerDiv) true)
  obtain ⟨t₃,ht₃,h₃⟩ := digit_run ((n%outerDiv)/strideDiv) binBase
    (List.replicate outerDiv true) (List.replicate strideDiv true)
    (List.replicate wordBase true)
    (List.replicate ((n%outerDiv)%strideDiv) true)
    (List.replicate (n/outerDiv) true)
  obtain ⟨t₄,ht₄,h₄⟩ := word_run (((n%outerDiv)/strideDiv)%binBase) wordBase
    (List.replicate outerDiv true) (List.replicate strideDiv true)
    (List.replicate binBase true)
    (List.replicate ((n%outerDiv)%strideDiv) true)
    (List.replicate (n/outerDiv) true)
    (List.replicate (((n%outerDiv)/strideDiv)/binBase) true)
  refine ⟨t₁+t₂+t₃+t₄+1, ?_, ?_⟩
  · omega
  · have hs₁ := run_add h₁ t₂
    rw [h₂] at hs₁
    have hs₂ := run_add hs₁ t₃
    rw [h₃] at hs₂
    have hs₃ := run_add hs₂ t₄
    rw [h₄] at hs₃
    have hs₄ := run_add hs₃ 1
    simpa only [done_run, ← Nat.add_assoc] using hs₄

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

theorem raw_column_run {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    let base := binBase a s q cy
    let stride := base^(s-1-p.val)
    let outer := base^s
    let wordSize := wordBase a s cy
    let b := code.val%outer
    let k := b/stride
    let d := k%base
    let r := ((rawColumnCode a s q cy).symm code).2 p
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val outer+
      MatrixUnaryDivision.totalTime b stride+
      MatrixUnaryDivision.totalTime k base+
      MatrixUnaryDivision.totalTime d wordSize+1,
      run t (cfg (some outerStart) initial
        (List.replicate code.val true) (List.replicate outer true)
        (List.replicate stride true) (List.replicate base true)
        (List.replicate wordSize true) [] [] [] [] [] [] [] []) =
      cfg none initial [] (List.replicate outer true)
        (List.replicate stride true) (List.replicate base true)
        (List.replicate wordSize true) []
        (List.replicate (b%stride) true) []
        (List.replicate
          ((tupleCode cy (s+1)) ((rawColumnCode a s q cy).symm code).1).val true)
        [] (List.replicate (k/base) true)
        (List.replicate (firstWordCode a s cy r.2).val true)
        (List.replicate r.1.val true) := by
  dsimp
  let base := binBase a s q cy
  let stride := base^(s-1-p.val)
  let outer := base^s
  let wordSize := wordBase a s cy
  let b := code.val%outer
  let k := b/stride
  let d := k%base
  let r := ((rawColumnCode a s q cy).symm code).2 p
  have htail :
      ((tupleCode cy (s+1)) ((rawColumnCode a s q cy).symm code).1).val =
      code.val/outer := column_tail_code code
  have hbin : (secondRowCode a s q cy r).val = d :=
    column_bin_code code p
  have hword : (firstWordCode a s cy r.2).val = d%wordSize := by
    rw [second_row_word]
    rw [hbin]
  have halpha : r.1.val = d/wordSize := by
    rw [second_row_alpha]
    rw [hbin]
  obtain ⟨t,ht,he⟩ := column_run code.val outer stride base wordSize
  refine ⟨t, ?_, ?_⟩
  · simpa only [b,k,d] using ht
  · simpa only [b,k,d,← htail,← hword,← halpha] using he

end EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine
