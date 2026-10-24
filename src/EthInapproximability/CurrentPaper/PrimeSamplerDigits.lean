import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical base-p digit extraction

Source: frozen v8 `B-effectivity-details.tex`, the balanced-family accessor.
The input label is repeatedly divided by the actual modulus. A unary
restriction-depth stack counts the digits. Each remainder is physically
prepended, so the final digit stream is most-significant first, suitable
for iterative Horner evaluation. This module exposes raw unary banks.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerDigits

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

inductive Admin where
  | loop | returned | emit | quotient
  deriving DecidableEq, Fintype

abbrev Stack := Fin 8
abbrev Label := MatrixUnaryDivision.Label ⊕ Admin
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

structure Data where
  dividend : List Bool := []
  divisor : List Bool := []
  count : List Bool := []
  remainder : List Bool := []
  quotient : List Bool := []
  saved : List Bool := []
  fuel : List Bool := []
  digits : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.dividend,d.divisor,d.count,d.remainder,d.quotient,d.saved,d.fuel,d.digits]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt (finSumFinEquiv : Fin 6 ⊕ Fin 2 ≃ Stack) (Equiv.refl _)
      (Equiv.refl _) (liftStmt (some Admin.returned) (MatrixUnaryDivision.program l))
  | .inr .loop => pop 6 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => (false,none)) (goto (fun _ => .inl .start)))
        (load (fun _ => (false,none)) halt))
  | .inr .returned => push 7 (fun _ => false) (goto (fun _ => .inr .emit))
  | .inr .emit => pop 3 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 7 (fun _ => true) (goto (fun _ => .inr .emit)))
        (load (fun _ => (false,none)) (goto (fun _ => .inr .quotient))))
  | .inr .quotient => pop 4 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 0 (fun _ => true) (goto (fun _ => .inr .quotient)))
        (load (fun _ => (false,none)) (goto (fun _ => .inr .loop))))

def cfg (l : Option Label) (v : Control) (d : Data) : Config := ⟨l,v,d.stacks⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c=run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_step {c d : Config} (h : advance program c=d) (t : ℕ) :
    run (t+1) c=run t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem emit_run (n : ℕ) (d : Data) (v : Control) :
    run (n+1) (cfg (some (.inr .emit)) v {d with remainder:=List.replicate n true}) =
      cfg (some (.inr .quotient)) (false,none)
        {d with remainder:=[],digits:=List.replicate n true++d.digits} := by
  induction n generalizing d v with
  | zero =>
      simp only [Nat.zero_add, List.replicate_zero, List.nil_append, run, Function.iterate_one]
      simp [advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
  | succ n ih =>
      have hs : advance program (cfg (some (.inr .emit)) v
          {d with remainder:=List.replicate (n+1) true}) =
          cfg (some (.inr .emit)) (v.1,some true)
            {d with remainder:=List.replicate n true,digits:=true::d.digits} := by
        simp [List.replicate_succ, advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
        funext k
        fin_cases k <;> rfl
      rw [run_step hs]
      simpa only [List.replicate_add, List.replicate_one, List.singleton_append,
        List.append_assoc] using ih {d with digits:=true::d.digits} (v.1,some true)

theorem quotient_run (n a : ℕ) (d : Data) (v : Control) :
    run (n+1) (cfg (some (.inr .quotient)) v
      {d with quotient:=List.replicate n true,dividend:=List.replicate a true}) =
      cfg (some (.inr .loop)) (false,none)
        {d with quotient:=[],dividend:=List.replicate (a+n) true} := by
  induction n generalizing a d v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run, Function.iterate_one]
      simp [advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
  | succ n ih =>
      have hs : advance program (cfg (some (.inr .quotient)) v
          {d with quotient:=List.replicate (n+1) true,dividend:=List.replicate a true}) =
          cfg (some (.inr .quotient)) (v.1,some true)
            {d with quotient:=List.replicate n true,dividend:=List.replicate (a+1) true} := by
        simp [List.replicate_succ, advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
        funext k
        fin_cases k <;> rfl
      rw [run_step hs]
      simpa only [show a+1+n=a+(n+1) by omega] using ih (a+1) d (v.1,some true)

def frame (fuel digits : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 6 ⊕ Fin 2 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some Admin.returned) none (fun i => ![fuel,digits] i) c)

theorem division_run (n p : ℕ) (fuel digits : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n p,
      run t (cfg (some (.inl .start)) (false,none)
        {dividend:=List.replicate n true,divisor:=List.replicate p true,fuel:=fuel,digits:=digits}) =
      cfg (some (.inr .returned)) (false,none)
        {divisor:=List.replicate p true,remainder:=List.replicate (n%p) true,
          quotient:=List.replicate (n/p) true,fuel:=fuel,digits:=digits} := by
  have he := MatrixUnaryDivision.division_total_run n p
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 6 ⊕ Fin 2 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program (some Admin.returned) (fun _ => rfl)
    none (fun i => ![fuel,digits] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate p true) [] [] [] []) (MatrixUnaryDivision.totalTime n p)
    (by rw [show ((advance MatrixUnaryDivision.program)^[_]) _ = _ from he]; rfl)
  change run t (frame _ _ _) = frame _ _ (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : frame fuel digits (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate n true) (List.replicate p true) [] [] [] []) =
      cfg (some (.inl .start)) (false,none)
        {dividend:=List.replicate n true,divisor:=List.replicate p true,fuel:=fuel,digits:=digits} := by
    unfold frame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : frame fuel digits (MatrixUnaryDivision.cfg none false [] (List.replicate p true)
      [] (List.replicate (n%p) true) (List.replicate (n/p) true) []) =
      cfg (some (.inr .returned)) (false,none)
        {divisor:=List.replicate p true,remainder:=List.replicate (n%p) true,
          quotient:=List.replicate (n/p) true,fuel:=fuel,digits:=digits} := by
    unfold frame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def ready (n p : ℕ) (fuel digits : List Bool) : Config :=
  cfg (some (.inr .loop)) (false,none)
    {dividend:=List.replicate n true,divisor:=List.replicate p true,fuel:=fuel,digits:=digits}

theorem round_run (n p : ℕ) (bit : Bool) (fuel digits : List Bool) :
    ∃ t ≤ 10*n+3*p+10,
      run t (ready n p (bit::fuel) digits) =
      ready (n/p) p fuel (List.replicate (n%p) true++false::digits) := by
  have hstart : advance program (ready n p (bit::fuel) digits) =
      cfg (some (.inl .start)) (false,none)
        {dividend:=List.replicate n true,divisor:=List.replicate p true,fuel:=fuel,digits:=digits} := by
    simp [ready, advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
    funext k
    fin_cases k <;> rfl
  obtain ⟨t,ht,hd⟩ := division_run n p fuel digits
  have hreturn : advance program (cfg (some (.inr .returned)) (false,none)
      {divisor:=List.replicate p true,remainder:=List.replicate (n%p) true,
        quotient:=List.replicate (n/p) true,fuel:=fuel,digits:=digits}) =
      cfg (some (.inr .emit)) (false,none)
        {divisor:=List.replicate p true,remainder:=List.replicate (n%p) true,
          quotient:=List.replicate (n/p) true,fuel:=fuel,digits:=false::digits} := by
    simp [advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
    funext k
    fin_cases k <;> rfl
  have he := emit_run (n%p)
    {divisor:=List.replicate p true,quotient:=List.replicate (n/p) true,
      fuel:=fuel,digits:=false::digits} (false,none)
  have hq := quotient_run (n/p) 0
    {divisor:=List.replicate p true,fuel:=fuel,digits:=List.replicate (n%p) true++false::digits}
    (false,none)
  simp only [Nat.zero_add,List.replicate_zero] at hq
  refine ⟨(t+1)+((n/p+1)+(n%p+1)+1),?_,?_⟩
  · have hdiv := MatrixUnaryDivision.totalTime_bound n p
    have hmod := Nat.mod_le n p
    have hquot := Nat.div_le_self n p
    omega
  · rw [run_add ((run_step hstart t).trans hd)]
    rw [run_step hreturn, show (n/p+1)+(n%p+1)=(n%p+1)+(n/p+1) by omega,
      run_add he, hq]
    rfl

def digits (p : ℕ) : ℕ → ℕ → List Bool → List Bool
  | 0, _, old => old
  | t+1, n, old => digits p t (n/p) (List.replicate (n%p) true++false::old)

/-- Full literal extraction with every quotient/remainder call and digit write
charged. The final stream includes exactly the requested leading zero digits. -/
theorem extraction_run (n p : ℕ) (fuel old : List Bool) :
    ∃ t ≤ fuel.length*(10*n+3*p+10)+1,
      let c := run t (ready n p fuel old)
      c.l=none ∧ c.stk 7=digits p fuel.length n old := by
  induction fuel generalizing n old with
  | nil =>
      refine ⟨1,by simp,?_⟩
      dsimp only
      simp [run, ready, advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks, digits]
  | cons bit fuel ih =>
      obtain ⟨a,ha,hr⟩ := round_run n p bit fuel old
      obtain ⟨b,hb,hh,ho⟩ := ih (n/p) (List.replicate (n%p) true++false::old)
      refine ⟨a+b,?_,?_⟩
      · have hn := Nat.div_le_self n p
        have hm := Nat.mul_le_mul_left fuel.length (show 10*(n/p)+3*p+10 ≤ 10*n+3*p+10 by omega)
        simp only [List.length_cons]
        nlinarith
      · dsimp only at hh ho ⊢
        rw [run_add hr]
        exact ⟨hh,ho⟩

/-- The complete final bank, for physical composition with the Horner stage. -/
theorem extraction_exact (n p : ℕ) (fuel old : List Bool) :
    ∃ t ≤ fuel.length*(10*n+3*p+10)+1,
      run t (ready n p fuel old) =
      cfg none (false,none)
        {dividend:=List.replicate (n/p^fuel.length) true,divisor:=List.replicate p true,
          digits:=digits p fuel.length n old} := by
  induction fuel generalizing n old with
  | nil =>
      refine ⟨1,by simp,?_⟩
      simp [run,ready,advance,cfg,program,TM2.step,TM2.stepAux,Data.stacks,digits]
  | cons bit fuel ih =>
      obtain ⟨a,ha,hr⟩ := round_run n p bit fuel old
      obtain ⟨b,hb,hend⟩ := ih (n/p) (List.replicate (n%p) true++false::old)
      refine ⟨a+b,?_,?_⟩
      · have hn := Nat.div_le_self n p
        have hm := Nat.mul_le_mul_left fuel.length (show 10*(n/p)+3*p+10 ≤ 10*n+3*p+10 by omega)
        simp only [List.length_cons]
        nlinarith
      · rw [run_add hr,hend]
        simp only [List.length_cons,digits,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm p]

end EthInapproximability.CurrentPaper.PrimeSamplerDigits
