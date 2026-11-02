import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.MatrixReadAt

/-!
# Literal row-major lookup with restored coordinates

Source: frozen v8 `B-effectivity-details.tex`, `thm:paper-materialization`.
The controller physically forms `row * width + column`, reads the preserved
payload at that unary address, and clears the temporary address. Its input
coordinates, width, payload, and arbitrary old output suffix are retained.
This is a reusable concrete callback for complete matrix transformations.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableLookup

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev Stack := Fin 10
abbrev Label := MatrixAddressMachine.Label ⊕ (MatrixReadAt.Label ⊕ Unit)
abbrev Control := Bool × MatrixReadAt.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def readInitial : MatrixReadAt.Control := (none,none,(false,false),(false,false))
def initial : Control := (false,readInitial)
def start : Label := .inl .outer
def readStart : Label := .inr (.inl (.inl .scan))
def clear : Label := .inr (.inr ())

def readPermutation : Stack ≃ Stack where
  toFun i := ![5,3,4,6,8,7,9,0,1,2] i
  invFun i := ![7,8,9,1,2,0,3,5,4,6] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def readStacks : Fin 7 ⊕ Fin 3 ≃ Stack := finSumFinEquiv.trans readPermutation

def readLabels : MatrixReadAt.Label ⊕ (MatrixAddressMachine.Label ⊕ Unit) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt (finSumFinEquiv : Fin 6 ⊕ Fin 4 ≃ Stack) (Equiv.refl _)
      (Equiv.refl _) (liftStmt (some (.inl (.inl BitMachineCopy.Label.scan)))
        (MatrixAddressMachine.program l))
  | .inr (.inl l) => renameStmt readStacks readLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixReadAt.program l))
  | .inr (.inr ()) => pop 5 (fun v b => (b.isSome,v.2))
      (branch Prod.fst (goto (fun _ => clear)) (load (fun _ => initial) halt))

def cfg (l : Option Label) (v : Control)
    (row width column address source out : List Bool) : Config :=
  ⟨l,v,![row,width,column,[],[],address,source,out,[],[]]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c=run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def addressFrame (source out : List Bool) (c : MatrixAddressMachine.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 6 ⊕ Fin 4 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl (.inl BitMachineCopy.Label.scan))) readInitial
      (fun i => ![source,out,[],[]] i) c)

theorem address_run (row width col : ℕ) (source out : List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width col,
      run t (cfg (some start) initial (List.replicate row true)
        (List.replicate width true) (List.replicate col true) [] source out) =
      cfg (some readStart) initial (List.replicate row true)
        (List.replicate width true) (List.replicate col true)
        (List.replicate (row*width+col) true) source out := by
  have he := MatrixAddressMachine.address_run row width col false []
  simp only [List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 6 ⊕ Fin 4 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    MatrixAddressMachine.program program (some (.inl (.inl BitMachineCopy.Label.scan)))
    (fun _ => rfl) readInitial (fun i => ![source,out,[],[]] i)
    (MatrixAddressMachine.cfg (some .outer) false (List.replicate row true)
      (List.replicate width true) (List.replicate col true) [] [] [])
    (MatrixAddressMachine.exactTime row width col)
    (by rw [show ((advance MatrixAddressMachine.program)^[_]) _ = _ from he]; rfl)
  change run t (addressFrame source out _) = addressFrame source out (MatrixAddressMachine.run _ _) at hr
  rw [he] at hr
  have hi : addressFrame source out (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate row true) (List.replicate width true) (List.replicate col true) [] [] []) =
      cfg (some start) initial (List.replicate row true)
        (List.replicate width true) (List.replicate col true) [] source out := by
    unfold addressFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : addressFrame source out (MatrixAddressMachine.cfg none false
      (List.replicate row true) (List.replicate width true) (List.replicate col true)
      [] [] (List.replicate (row*width+col) true)) =
      cfg (some readStart) initial (List.replicate row true)
        (List.replicate width true) (List.replicate col true)
        (List.replicate (row*width+col) true) source out := by
    unfold addressFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def readFrame (row width col : List Bool) (c : MatrixReadAt.Config) : Config :=
  renameCfg readStacks readLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) false (fun i => ![row,width,col] i) c)

theorem read_run (row width col : List Bool) (i : ℕ) (source out : List Bool) :
    ∃ t ≤ 3*i+3*source.length+8,
      run t (cfg (some readStart) initial row width col (List.replicate i true) source out) =
      cfg (some clear) initial row width col (List.replicate i true)
        source (source[i]?.getD false::out) := by
  obtain ⟨a,ha,he⟩ := MatrixReadAt.readAt_run i source out
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    readStacks readLabels (Equiv.prodComm _ _) MatrixReadAt.program program
    (some (.inr ())) (fun _ => rfl) false (fun k => ![row,width,col] k)
    (MatrixReadAt.initial (List.replicate i true) source out) a
    (by rw [show ((advance MatrixReadAt.program)^[a]) _ = _ from he]; rfl)
  change run t (readFrame row width col _) = readFrame row width col (MatrixReadAt.run _ _) at hr
  rw [he] at hr
  have hi : readFrame row width col (MatrixReadAt.initial (List.replicate i true) source out) =
      cfg (some readStart) initial row width col (List.replicate i true) source out := by
    unfold readFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : readFrame row width col (MatrixReadAt.cfg none readInitial
      (List.replicate i true) [] source [] (source[i]?.getD false::out)) =
      cfg (some clear) initial row width col (List.replicate i true)
        source (source[i]?.getD false::out) := by
    unfold readFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [readInitial] at hf
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

theorem clear_run (row width col source out address : List Bool) (v : Control) :
    run (address.length+1) (cfg (some clear) v row width col address source out) =
      cfg none initial row width col [] source out := by
  induction address generalizing v with
  | nil => simp [run,advance,cfg,clear,program,TM2.step,TM2.stepAux]
  | cons b address ih =>
      have hs : advance program (cfg (some clear) v row width col (b::address) source out) =
          cfg (some clear) (true,v.2) row width col address source out := by
        simp [advance,cfg,clear,program,TM2.step,TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons,run,Function.iterate_succ_apply,hs]
      exact ih (true,v.2)

/-- Coordinates and every payload bit survive the lookup; the temporary
address is empty again, allowing the exact same callback to run repeatedly. -/
theorem lookup_run (row width col : ℕ) (source out : List Bool) :
    ∃ t ≤ 32*(row+width+col+source.length+1)^2,
      run t (cfg (some start) initial (List.replicate row true)
        (List.replicate width true) (List.replicate col true) [] source out) =
      cfg none initial (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] source (source[row*width+col]?.getD false::out) := by
  obtain ⟨a,ha,he⟩ := address_run row width col source out
  obtain ⟨b,hb,hr⟩ := read_run (List.replicate row true) (List.replicate width true)
    (List.replicate col true) (row*width+col) source out
  have hc := clear_run (List.replicate row true) (List.replicate width true)
    (List.replicate col true) source (source[row*width+col]?.getD false::out)
    (List.replicate (row*width+col) true) initial
  simp only [List.length_replicate] at hc
  refine ⟨a+(b+(row*width+col+1)),?_,?_⟩
  · have htime := MatrixAddressMachine.exactTime_bound row width col
    let S := row+width+col+source.length+1
    have hS : 1≤S := by dsimp [S]; omega
    have hrow : row≤S := by dsimp [S]; omega
    have hw : width≤S := by dsimp [S]; omega
    have hcol : col≤S := by dsimp [S]; omega
    have hlen : source.length≤S := by dsimp [S]; omega
    have hsmall : row+width+col+1≤S := by dsimp [S]; omega
    have hsq := Nat.pow_le_pow_left hsmall 2
    have hprod := Nat.mul_le_mul hrow hw
    change a+(b+(row*width+col+1))≤32*S^2
    nlinarith
  · rw [run_add he,run_add hr,hc]

end EthInapproximability.CurrentPaper.MatrixTableLookup
