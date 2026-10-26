import CurrentAdditive.GenericParameterBranch
import EthInapproximability.CurrentPaper.MatrixUnaryDivision

/-! Preserving physical quotient installation: two literal copies, the
actual six-stack unary divider, and a literal output copy. -/
namespace V22ParameterDivide
noncomputable section
set_option maxRecDepth 8192
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
variable {Base : Type*} [DecidableEq Base]
abbrev Stack (Base : Type*) := Base ⊕ Fin 9

def leftSlots (source : Base) : Fin 3 ↪ Stack Base :=
  ⟨![.inl source,.inr 0,.inr 6],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def rightSlots (source : Base) : Fin 3 ↪ Stack Base :=
  ⟨![.inl source,.inr 1,.inr 7],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def divSlots : Fin 6 ↪ Stack Base :=
  ⟨fun j => .inr ⟨j.val,by omega⟩,by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Stack Base => Sum.elim (fun _ => 0) Fin.val x) h⟩
def outputSlots (target : Base) : Fin 3 ↪ Stack Base :=
  ⟨![.inr 4,.inl target,.inr 8],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def initial (B : Base → List Bool) : Stack Base → List Bool := Sum.elim B (fun _ => [])
def afterLeft (B : Base → List Bool) (n : ℕ) := Function.update (initial B) (.inr 0) (List.replicate n true)
def afterRight (B : Base → List Bool) (n m : ℕ) := Function.update (afterLeft B n) (.inr 1) (List.replicate m true)
def afterDivide (B : Base → List Bool) (n m : ℕ) : Stack Base → List Bool :=
  bank divSlots (afterRight B n m)
    (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
      (List.replicate (n%m) true) (List.replicate (n/m) true) []).stk
def terminal (B : Base → List Bool) (target : Base) (n m : ℕ) :=
  Function.update (afterDivide B n m) (.inl target) (List.replicate (n/m) true)
def leftProgram (source : Base) := CurrentAdditive.GenericParameterBranch.copyProgram (leftSlots source)
def rightProgram (source : Base) := CurrentAdditive.GenericParameterBranch.copyProgram (rightSlots source)
def divideProgram (l : MatrixUnaryDivision.Label) :
    TM2.Stmt (fun _ : Stack Base => Bool) MatrixUnaryDivision.Label Bool :=
  BitMachineStackEmbedding.stmt divSlots id id id none (MatrixUnaryDivision.program l)
def outputProgram (target : Base) := CurrentAdditive.GenericParameterBranch.copyProgram (outputSlots target)

theorem afterDivide_base (B : Base → List Bool) (n m : ℕ) (j : Base) :
    afterDivide B n m (.inl j)=B j := by
  rw [afterDivide,bank_outside]
  · rfl
  · rintro ⟨q,hq⟩; cases hq
theorem afterDivide_extra (B : Base → List Bool) (n m : ℕ) (j : Fin 9) (hj : 6 ≤ j.val) :
    afterDivide B n m (.inr j)=[] := by
  rw [afterDivide,bank_outside]
  · have h1 : j≠1 := by intro h; subst j; omega
    have h0 : j≠0 := by intro h; subst j; omega
    rw [afterRight,Function.update_of_ne (by exact fun h => h1 (Sum.inr.inj h))]
    rw [afterLeft,Function.update_of_ne (by exact fun h => h0 (Sum.inr.inj h))]
    rfl
  · rintro ⟨q,hq⟩
    have hv := congrArg Fin.val (Sum.inr.inj hq)
    change q.val=j.val at hv
    omega
theorem afterDivide_output (B : Base → List Bool) (n m : ℕ) :
    afterDivide B n m (.inr 4)=List.replicate (n/m) true := by
  change bank divSlots _ _ (divSlots 4)=_
  rw [bank_at]
  rfl

theorem run_left (B : Base → List Bool) (source : Base) (n : ℕ)
    (hs : B source=List.replicate n true) :
    ∃ t ≤ 2*n+2, ((advance (leftProgram source))^[t])
      (⟨some .scan,none,initial B⟩ : TM2.Cfg (fun _ : Stack Base => Bool) _ _) =
      ⟨none,none,afterLeft B n⟩ := by
  simpa only [leftProgram,leftSlots,List.length_replicate,afterLeft] using
    CurrentAdditive.GenericParameterBranch.copy_run (leftSlots source) (initial B) (List.replicate n true)
      hs (by rfl) (by rfl)
theorem run_right (B : Base → List Bool) (source : Base) (n m : ℕ)
    (hs : B source=List.replicate m true) :
    ∃ t ≤ 2*m+2, ((advance (rightProgram source))^[t])
      (⟨some .scan,none,afterLeft B n⟩ : TM2.Cfg (fun _ : Stack Base => Bool) _ _) =
      ⟨none,none,afterRight B n m⟩ := by
  simpa only [rightProgram,afterRight,List.length_replicate] using
    CurrentAdditive.GenericParameterBranch.copy_run (rightSlots source) (afterLeft B n) (List.replicate m true)
      hs (by rfl) (by rfl)
theorem run_divide (B : Base → List Bool) (n m : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n m, ((advance divideProgram)^[t])
      (⟨some .start,false,afterRight B n m⟩ : TM2.Cfg (fun _ : Stack Base => Bool) _ _) =
      ⟨none,false,afterDivide B n m⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate n true) (List.replicate m true) [] [] [] []
  have hbank : bank divSlots (afterRight B n m) c.stk=afterRight B n m := by
    apply bank_eq_self
    intro j
    fin_cases j <;> rfl
  have hlocal := MatrixUnaryDivision.division_total_run n m
  have hhalt : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) c).l=none := by
    rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) c =
      MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n%m) true) (List.replicate (n/m) true) [] from hlocal]
    rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs divSlots (afterRight B n m)
    id id id (by intro v; rfl) none MatrixUnaryDivision.program divideProgram (by intro l; rfl)
    c (MatrixUnaryDivision.totalTime n m) hhalt
  have hlocal' : ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) c =
      MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n%m) true) (List.replicate (n/m) true) [] := hlocal
  rw [hlocal'] at he
  change ((advance divideProgram)^[t])
    ⟨some .start,false,bank divSlots (afterRight B n m) c.stk⟩ =
    ⟨none,false,afterDivide B n m⟩ at he
  rw [hbank] at he
  exact ⟨t,ht,he⟩
theorem run_output (B : Base → List Bool) (target : Base) (n m : ℕ) (hb : B target=[]) :
    ∃ t ≤ 2*(n/m)+2, ((advance (outputProgram target))^[t])
      (⟨some .scan,none,afterDivide B n m⟩ : TM2.Cfg (fun _ : Stack Base => Bool) _ _) =
      ⟨none,none,terminal B target n m⟩ := by
  simpa only [List.length_replicate] using
    CurrentAdditive.GenericParameterBranch.copy_run (outputSlots target) (afterDivide B n m) (List.replicate (n/m) true)
      (afterDivide_output B n m) ((afterDivide_base B n m target).trans hb)
      (afterDivide_extra B n m 8 (by decide))

def lrProgram (left right : Base) := BitMachineRawSequence.program
  (leftProgram left) (rightProgram right) .scan (none : Option Bool) (none : Option Bool)
def lrdProgram (left right : Base) := BitMachineRawSequence.program
  (lrProgram left right) (divideProgram (Base:=Base)) .start
  ((none : Option Bool),(none : Option Bool)) false
def program (left right target : Base) := BitMachineRawSequence.program
  (lrdProgram left right) (outputProgram target) .scan
  (((none : Option Bool),(none : Option Bool)),false) (none : Option Bool)
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
    MatrixUnaryDivision.Label) BitMachineCopy.Label
def startLabel : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
def startControl := ((((none : Option Bool),(none : Option Bool)),false),(none : Option Bool))
def clock (n m : ℕ) := (2*n+2)+(2*m+2)+MatrixUnaryDivision.totalTime n m+(2*(n/m)+2)+3

theorem run_install (B : Base → List Bool) (left right target : Base) (n m : ℕ)
    (hl : B left=List.replicate n true) (hr : B right=List.replicate m true) (ht : B target=[]) :
    ∃ t ≤ clock n m, ((advance (program left right target))^[t])
      (⟨some startLabel,startControl,initial B⟩ : TM2.Cfg (fun _ : Stack Base => Bool) _ _) =
      ⟨none,startControl,terminal B target n m⟩ := by
  obtain ⟨a,ha,ea⟩ := run_left B left n hl
  obtain ⟨b,hb,eb⟩ := run_right B right n m hr
  obtain ⟨u,hu,eu⟩ := BitMachineRawSequence.runs (leftProgram left) (rightProgram right)
    .scan .scan (none : Option Bool) none (none : Option Bool) none
    (initial B) (afterLeft B n) (afterRight B n m) a b ea eb
  obtain ⟨c,hc,ec⟩ := run_divide B n m
  obtain ⟨v,hv,ev⟩ := BitMachineRawSequence.runs (lrProgram left right) divideProgram
    (.inl .scan) .start ((none : Option Bool),(none : Option Bool)) (none,none) false false
    (initial B) (afterRight B n m) (afterDivide B n m) u c eu ec
  obtain ⟨d,hd,ed⟩ := run_output B target n m ht
  obtain ⟨t,ht,et⟩ := BitMachineRawSequence.runs (lrdProgram left right) (outputProgram target)
    (.inl (.inl .scan)) .scan (((none : Option Bool),(none : Option Bool)),false)
    ((none,none),false) (none : Option Bool) none
    (initial B) (afterDivide B n m) (terminal B target n m) v d ev ed
  exact ⟨t,by unfold clock; omega,et⟩

theorem terminal_target (B : Base → List Bool) (target : Base) (n m : ℕ) :
    terminal B target n m (.inl target)=List.replicate (n/m) true := by simp [terminal]
theorem terminal_base_other (B : Base → List Bool) (target j : Base) (hj : j≠target) (n m : ℕ) :
    terminal B target n m (.inl j)=B j := by
  rw [terminal,Function.update_of_ne (by exact fun h => hj (Sum.inl.inj h)),afterDivide_base]
theorem clock_linear (n m : ℕ) : clock n m ≤ 12*n+5*m+13 := by
  have h := MatrixUnaryDivision.totalTime_bound n m
  have hd := Nat.div_le_self n m
  unfold clock
  omega

end
end V22ParameterDivide
