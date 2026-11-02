import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical cardinal initialization for a classical interlace

Frozen v8 `def:paper-interlace`, `thm:paper-materialization`.
From unary `blocks`, `rows` and `cols`, this fixed Boolean-stack controller
writes unary `blocks*rows` and `cols^blocks`.  The multiplication used by the
power loop is the audited literal unary address machine; no natural-number
register or arithmetic transition is hidden in the control state.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceSize

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

inductive Admin where
  | initOne | loop | clearAccumulator | moveProduct
  deriving DecidableEq, Fintype

abbrev Label := MatrixAddressMachine.Label ⊕
  (BitMachineCopy.Label ⊕ (MatrixAddressMachine.Label ⊕ Admin))
abbrev Control := Bool × (Option Bool × Bool)
abbrev Stack := Fin 11
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (false,none,false)
def start : Label := .inl .outer
def copyStart : Label := .inr (.inl .scan)
def powerStart : Label := .inr (.inr (.inl .outer))
def loop : Label := .inr (.inr (.inr .loop))

private def rowPerm : Stack ≃ Stack where
  toFun := ![0,1,5,6,7,3,2,4,8,9,10]
  invFun := ![0,1,6,5,7,2,3,4,8,9,10]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def rowStacks : Fin 6 ⊕ Fin 5 ≃ Stack := finSumFinEquiv.trans rowPerm

private def copyPerm : Stack ≃ Stack where
  toFun := ![0,8,9,1,2,3,4,5,6,7,10]
  invFun := ![0,3,4,5,6,7,8,9,1,2,10]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def copyStacks : Fin 3 ⊕ Fin 8 ≃ Stack := finSumFinEquiv.trans copyPerm

private def powerPerm : Stack ≃ Stack where
  toFun := ![4,2,5,6,7,10,0,1,3,8,9]
  invFun := ![6,7,1,8,0,2,3,4,9,10,5]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def powerStacks : Fin 6 ⊕ Fin 5 ≃ Stack := finSumFinEquiv.trans powerPerm

def rowControl : Bool × (Option Bool × Bool) ≃ Control := Equiv.refl _
def copyControl : Option Bool × (Bool × Bool) ≃ Control where
  toFun s := (s.2.1,s.1,s.2.2)
  invFun s := (s.2.1,s.1,s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
def powerControl : Bool × (Bool × Option Bool) ≃ Control where
  toFun s := (s.2.1,s.2.2,s.1)
  invFun s := (s.2.2,s.1,s.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def copyLabels : BitMachineCopy.Label ⊕
    (MatrixAddressMachine.Label ⊕ (MatrixAddressMachine.Label ⊕ Admin)) ≃ Label where
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

def powerLabels : MatrixAddressMachine.Label ⊕
    (MatrixAddressMachine.Label ⊕ (BitMachineCopy.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt rowStacks (Equiv.refl _) rowControl
      (liftStmt (some (.inr (.inr Admin.initOne)))
        (MatrixAddressMachine.program l))
  | .inr (.inl l) => renameStmt copyStacks copyLabels copyControl
      (liftStmt (some (.inr (.inr Admin.loop)))
        (BitMachineCopy.program l))
  | .inr (.inr (.inl l)) => renameStmt powerStacks powerLabels powerControl
      (liftStmt (some (.inr (.inr Admin.clearAccumulator)))
        (MatrixAddressMachine.program l))
  | .inr (.inr (.inr .initOne)) =>
      push 4 (fun _ => true) (goto (fun _ => copyStart))
  | .inr (.inr (.inr .loop)) =>
      pop 8 (fun s b => (b.isSome,s.2))
        (branch Prod.fst (load (fun _ => initial) (goto (fun _ => powerStart)))
          (load (fun _ => initial) halt))
  | .inr (.inr (.inr .clearAccumulator)) =>
      pop 4 (fun s b => (b.isSome,s.2))
        (branch Prod.fst
          (load (fun _ => initial) (goto (fun _ => .inr (.inr (.inr .clearAccumulator)))))
          (load (fun _ => initial) (goto (fun _ => .inr (.inr (.inr .moveProduct))))))
  | .inr (.inr (.inr .moveProduct)) =>
      pop 10 (fun s b => (b.isSome,s.2))
        (branch Prod.fst
          (push 4 (fun _ => true)
            (load (fun _ => initial) (goto (fun _ => .inr (.inr (.inr .moveProduct))))))
          (load (fun _ => initial) (goto (fun _ => loop))))

def cfg (l : Option Label) (s : Control)
    (blocks rows cols rowCount columnCount fuel scratch product : List Bool) : Config :=
  ⟨l,s,![blocks,rows,cols,rowCount,columnCount,[],[],[],fuel,scratch,product]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) := Function.iterate_succ_apply _ _ _

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def rowFrame (cols : ℕ) (c : MatrixAddressMachine.Config) : Config :=
  renameCfg rowStacks (Equiv.refl _) rowControl
    (liftCfg (some (.inr (.inr Admin.initOne))) (none,false)
      (fun k => ![List.replicate cols true,[],[],[],[]] k) c)

theorem row_count_run (blocks rows cols : ℕ) :
    ∃ t ≤ MatrixAddressMachine.exactTime blocks rows 0,
      run t (cfg (some start) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true) [] [] [] [] []) =
      cfg (some (.inr (.inr (.inr .initOne)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) (List.replicate (blocks*rows) true)
        [] [] [] [] := by
  have he := MatrixAddressMachine.address_run blocks rows 0 false []
  simp only [List.replicate_zero, Nat.add_zero,
    List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed rowStacks (Equiv.refl _) rowControl
    MatrixAddressMachine.program program
    (some (.inr (.inr Admin.initOne))) (fun _ => rfl)
    (none,false) (fun k => ![List.replicate cols true,[],[],[],[]] k)
    (MatrixAddressMachine.cfg (some .outer) false (List.replicate blocks true)
      (List.replicate rows true) [] [] [] [])
    (MatrixAddressMachine.exactTime blocks rows 0)
    (by rw [show ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime blocks rows 0]) _ = _ from he]; rfl)
  change run t (rowFrame cols _) = rowFrame cols (MatrixAddressMachine.run _ _) at hr
  rw [he] at hr
  have hi : rowFrame cols
      (MatrixAddressMachine.cfg (some .outer) false (List.replicate blocks true)
        (List.replicate rows true) [] [] [] []) =
      cfg (some start) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true) [] [] [] [] [] := by
    unfold rowFrame renameCfg liftCfg rowControl cfg MatrixAddressMachine.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : rowFrame cols
      (MatrixAddressMachine.cfg none false (List.replicate blocks true)
        (List.replicate rows true) [] [] [] (List.replicate (blocks*rows) true)) =
      cfg (some (.inr (.inr (.inr .initOne)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) (List.replicate (blocks*rows) true)
        [] [] [] [] := by
    unfold rowFrame renameCfg liftCfg rowControl cfg MatrixAddressMachine.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem init_one_run (blocks rows cols : ℕ) :
    run 1
      (cfg (some (.inr (.inr (.inr .initOne)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) (List.replicate (blocks*rows) true)
        [] [] [] []) =
      cfg (some copyStart) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) (List.replicate (blocks*rows) true)
        [true] [] [] [] := by
  simp [run_succ, advance, TM2.step, TM2.stepAux, program, cfg]
  simp only [run, Function.iterate_zero, id_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

def copyFrame (rows cols : ℕ) (rowCount : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool)) : Config :=
  renameCfg copyStacks copyLabels copyControl
    (liftCfg (some (.inr (.inr Admin.loop)))
      (false,false)
      (fun k => ![List.replicate rows true,List.replicate cols true,
        rowCount,[true],[],[],[],[]] k) c)

theorem copy_blocks_run (blocks rows cols : ℕ) :
    ∃ t ≤ 2*blocks+2,
      run t (cfg (some copyStart) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        (List.replicate (blocks*rows) true) [true] [] [] []) =
      cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        (List.replicate (blocks*rows) true) [true]
        (List.replicate blocks true) [] [] := by
  have he := BitMachineCopy.run_correct none (List.replicate blocks true) []
  simp only [List.length_replicate, List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed copyStacks copyLabels copyControl
    BitMachineCopy.program program
    (some (.inr (.inr Admin.loop))) (fun _ => rfl)
    (false,false)
    (fun k => ![List.replicate rows true,List.replicate cols true,
      List.replicate (blocks*rows) true,[true],[],[],[],[]] k)
    (BitMachineCopy.cfg (some .scan) none (List.replicate blocks true) [] [])
    (2*blocks+2)
    (by rw [show ((advance BitMachineCopy.program)^[2*blocks+2]) _ = _ from he]; rfl)
  change run t (copyFrame rows cols (List.replicate (blocks*rows) true) _) =
    copyFrame rows cols (List.replicate (blocks*rows) true)
      (BitMachineCopy.run _ _) at hr
  rw [he] at hr
  have hi : copyFrame rows cols (List.replicate (blocks*rows) true)
      (BitMachineCopy.cfg (some .scan) none (List.replicate blocks true) [] []) =
      cfg (some copyStart) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        (List.replicate (blocks*rows) true) [true] [] [] [] := by
    unfold copyFrame renameCfg liftCfg copyControl cfg BitMachineCopy.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : copyFrame rows cols (List.replicate (blocks*rows) true)
      (BitMachineCopy.cfg none none (List.replicate blocks true)
        (List.replicate blocks true) []) =
      cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        (List.replicate (blocks*rows) true) [true]
        (List.replicate blocks true) [] [] := by
    unfold copyFrame renameCfg liftCfg copyControl cfg BitMachineCopy.cfg initial loop
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def powerFrame (blocks rows : ℕ) (rowCount fuel : List Bool)
    (c : MatrixAddressMachine.Config) : Config :=
  renameCfg powerStacks powerLabels powerControl
    (liftCfg (some (.inr (.inr Admin.clearAccumulator)))
      (false,none)
      (fun k => ![List.replicate blocks true,List.replicate rows true,
        rowCount,fuel,[]] k) c)

theorem power_count_run (blocks rows cols a : ℕ) (rowCount fuel : List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime a cols 0,
      run t (cfg (some powerStart) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate a true) fuel [] []) =
      cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) rowCount (List.replicate a true)
        fuel [] (List.replicate (a*cols) true) := by
  have he := MatrixAddressMachine.address_run a cols 0 false []
  simp only [List.replicate_zero, Nat.add_zero,
    List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed powerStacks powerLabels powerControl
    MatrixAddressMachine.program program
    (some (.inr (.inr Admin.clearAccumulator))) (fun _ => rfl)
    (false,none)
    (fun k => ![List.replicate blocks true,List.replicate rows true,
      rowCount,fuel,[]] k)
    (MatrixAddressMachine.cfg (some .outer) false (List.replicate a true)
      (List.replicate cols true) [] [] [] [])
    (MatrixAddressMachine.exactTime a cols 0)
    (by rw [show ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime a cols 0]) _ = _ from he]; rfl)
  change run t (powerFrame blocks rows rowCount fuel _) =
    powerFrame blocks rows rowCount fuel (MatrixAddressMachine.run _ _) at hr
  rw [he] at hr
  have hi : powerFrame blocks rows rowCount fuel
      (MatrixAddressMachine.cfg (some .outer) false (List.replicate a true)
        (List.replicate cols true) [] [] [] []) =
      cfg (some powerStart) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate a true) fuel [] [] := by
    unfold powerFrame renameCfg liftCfg powerControl cfg MatrixAddressMachine.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : powerFrame blocks rows rowCount fuel
      (MatrixAddressMachine.cfg none false (List.replicate a true)
        (List.replicate cols true) [] [] [] (List.replicate (a*cols) true)) =
      cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) rowCount (List.replicate a true)
        fuel [] (List.replicate (a*cols) true) := by
    unfold powerFrame renameCfg liftCfg powerControl cfg MatrixAddressMachine.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

private theorem loop_cons (blocks rows cols : ℕ) (rowCount accumulator fuel : List Bool) :
    run 1 (cfg (some loop) initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount accumulator (true::fuel) [] []) =
    cfg (some powerStart) initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount accumulator fuel [] [] := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial, loop]
  funext k
  fin_cases k <;> rfl

private theorem loop_nil (blocks rows cols : ℕ) (rowCount accumulator : List Bool) :
    run 1 (cfg (some loop) initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount accumulator [] [] []) =
    cfg none initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount accumulator [] [] [] := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial, loop]

private theorem clear_cons (blocks rows cols : ℕ) (rowCount accumulator fuel product : List Bool) :
    run 1 (cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount (true::accumulator) fuel [] product) =
    cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount accumulator fuel [] product := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial]
  funext k
  fin_cases k <;> rfl

private theorem clear_nil (blocks rows cols : ℕ) (rowCount fuel product : List Bool) :
    run 1 (cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount [] fuel [] product) =
    cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount [] fuel [] product := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial]

private theorem move_cons (blocks rows cols : ℕ) (rowCount accumulator fuel product : List Bool) :
    run 1 (cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount accumulator fuel [] (true::product)) =
    cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount (true::accumulator) fuel [] product := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial]
  funext k
  fin_cases k <;> rfl

private theorem move_nil (blocks rows cols : ℕ) (rowCount accumulator fuel : List Bool) :
    run 1 (cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount accumulator fuel [] []) =
    cfg (some loop) initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount accumulator fuel [] [] := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, initial, loop]

private theorem clear_run (blocks rows cols a : ℕ) (rowCount fuel product : List Bool) :
    run (a+1) (cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount (List.replicate a true) fuel [] product) =
    cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount [] fuel [] product := by
  induction a with
  | zero => simpa using clear_nil blocks rows cols rowCount fuel product
  | succ a ih =>
      have h := run_add (clear_cons blocks rows cols rowCount
        (List.replicate a true) fuel product) (a+1)
      simpa only [List.replicate_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.trans ih

private theorem move_run (blocks rows cols p : ℕ)
    (rowCount accumulator fuel : List Bool) :
    run (p+1) (cfg (some (.inr (.inr (.inr .moveProduct)))) initial
      (List.replicate blocks true) (List.replicate rows true)
      (List.replicate cols true) rowCount accumulator fuel [] (List.replicate p true)) =
    cfg (some loop) initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true)
      rowCount (List.replicate p true ++ accumulator) fuel [] [] := by
  induction p generalizing accumulator with
  | zero => simpa using move_nil blocks rows cols rowCount accumulator fuel
  | succ p ih =>
      have h := run_add (move_cons blocks rows cols rowCount accumulator fuel
        (List.replicate p true)) (p+1)
      have hlist : List.replicate p true ++ true :: accumulator =
          List.replicate (p+1) true ++ accumulator := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      have hz := h.trans (ih (true::accumulator))
      rw [hlist] at hz
      simpa only [List.replicate_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz

def stepBound (a cols : ℕ) : ℕ :=
  1 + MatrixAddressMachine.exactTime a cols 0 + (a+1) + (a*cols+1)

theorem power_step_run (blocks rows cols a : ℕ) (rowCount fuel : List Bool) :
    ∃ t ≤ stepBound a cols,
      run t (cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate a true) (true::fuel) [] []) =
      cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate (a*cols) true) fuel [] [] := by
  obtain ⟨t,ht,he⟩ := power_count_run blocks rows cols a rowCount fuel
  have h1 := run_add (loop_cons blocks rows cols rowCount
    (List.replicate a true) fuel) t
  have h2 : run (1+t)
      (cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate a true) (true::fuel) [] []) =
      cfg (some (.inr (.inr (.inr .clearAccumulator)))) initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) rowCount (List.replicate a true)
        fuel [] (List.replicate (a*cols) true) := h1.trans he
  have h3 := run_add h2 (a+1)
  rw [clear_run] at h3
  have h4 := run_add h3 (a*cols+1)
  rw [move_run] at h4
  refine ⟨(1+t)+(a+1)+(a*cols+1), ?_, ?_⟩
  · unfold stepBound
    omega
  · simpa only [List.append_nil] using h4

def powerTime (a cols : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => stepBound a cols + powerTime (a*cols) cols n

theorem power_loop_run (blocks rows cols a n : ℕ) (rowCount : List Bool) :
    ∃ t ≤ powerTime a cols n,
      run t (cfg (some loop) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate a true) (List.replicate n true) [] []) =
      cfg none initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        rowCount (List.replicate (a*cols^n) true) [] [] [] := by
  induction n generalizing a with
  | zero =>
      refine ⟨1, by simp [powerTime], ?_⟩
      simpa only [pow_zero, Nat.mul_one, List.replicate_zero] using
        loop_nil blocks rows cols rowCount (List.replicate a true)
  | succ n ih =>
      obtain ⟨t₁,ht₁,he₁⟩ := power_step_run blocks rows cols a rowCount
        (List.replicate n true)
      obtain ⟨t₂,ht₂,he₂⟩ := ih (a*cols)
      have h := run_add he₁ t₂
      rw [he₂] at h
      refine ⟨t₁+t₂, ?_, ?_⟩
      · simp only [powerTime]
        omega
      · simpa only [List.replicate_succ, pow_succ,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private theorem pow_le_output (cols j blocks : ℕ) (hj : j ≤ blocks) :
    cols^j ≤ 1+cols^blocks := by
  by_cases hc : 0 < cols
  · have h := Nat.pow_le_pow_right hc hj
    omega
  · have hc0 : cols = 0 := by omega
    subst cols
    cases j with
    | zero => simp
    | succ j => simp

private theorem stepBound_le_output (cols j blocks : ℕ) (hj : j+1 ≤ blocks) :
    stepBound (cols^j) cols ≤ 16*(2+cols^blocks) := by
  have h₁ := pow_le_output cols j blocks (by omega)
  have h₂ := pow_le_output cols (j+1) blocks hj
  rw [pow_succ] at h₂
  calc
    stepBound (cols^j) cols = 3*(cols^j*cols)+5*cols^j+7 := by
      unfold stepBound MatrixAddressMachine.exactTime
      ring
    _ ≤ 3*(1+cols^blocks)+5*(1+cols^blocks)+7 := by omega
    _ ≤ 16*(2+cols^blocks) := by omega

theorem powerTime_le_output (cols blocks j n : ℕ) (h : j+n = blocks) :
    powerTime (cols^j) cols n ≤ n*(16*(2+cols^blocks))+1 := by
  induction n generalizing j with
  | zero => simp [powerTime]
  | succ n ih =>
      have hs : j+1 ≤ blocks := by omega
      have hj : (j+1)+n = blocks := by omega
      have hr := ih (j+1) hj
      have hb := stepBound_le_output cols j blocks hs
      have hr' : powerTime (cols^j*cols) cols n ≤
          n*(16*(2+cols^blocks))+1 := by simpa only [pow_succ] using hr
      change stepBound (cols^j) cols + powerTime (cols^j*cols) cols n ≤
        (n+1)*(16*(2+cols^blocks))+1
      calc
        stepBound (cols^j) cols + powerTime (cols^j*cols) cols n ≤
            16*(2+cols^blocks) + (n*(16*(2+cols^blocks))+1) :=
          Nat.add_le_add hb hr'
        _ = (n+1)*(16*(2+cols^blocks))+1 := by ring

def sizeBound (blocks rows cols : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime blocks rows 0 + 1 +
    (2*blocks+2) + (blocks*(16*(2+cols^blocks))+1)

theorem size_run (blocks rows cols : ℕ) :
    ∃ t ≤ sizeBound blocks rows cols,
      run t (cfg (some start) initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        [] [] [] [] []) =
      cfg none initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true)
        (List.replicate (blocks*rows) true)
        (List.replicate (cols^blocks) true) [] [] [] := by
  obtain ⟨t₁,ht₁,he₁⟩ := row_count_run blocks rows cols
  obtain ⟨t₂,ht₂,he₂⟩ := copy_blocks_run blocks rows cols
  obtain ⟨t₃,ht₃,he₃⟩ := power_loop_run blocks rows cols 1 blocks
    (List.replicate (blocks*rows) true)
  have h₃bound : t₃ ≤ blocks*(16*(2+cols^blocks))+1 := by
    have h := powerTime_le_output cols blocks 0 blocks (by omega)
    simpa only [pow_zero] using ht₃.trans h
  have h₁ := run_add he₁ 1
  rw [init_one_run] at h₁
  have h₂ := run_add h₁ t₂
  rw [he₂] at h₂
  have h₃ := run_add h₂ t₃
  have he₃' := he₃
  simp only [List.replicate_one, Nat.one_mul] at he₃'
  rw [he₃'] at h₃
  refine ⟨((t₁+1)+t₂)+t₃, ?_, ?_⟩
  · unfold sizeBound
    omega
  · simpa only [Nat.one_mul] using h₃

theorem sizeBound_polynomial (blocks rows cols : ℕ) :
    sizeBound blocks rows cols ≤
      64*(blocks+rows+cols+blocks*rows+cols^blocks+1)^2 := by
  let s := blocks+rows+cols+blocks*rows+cols^blocks+1
  have h₁ : blocks ≤ s := by dsimp [s]; omega
  have h₂ : cols^blocks ≤ s := by dsimp [s]; omega
  have h₃ : blocks*rows ≤ s := by dsimp [s]; omega
  have h₄ : 1 ≤ s := by dsimp [s]; omega
  have h₅ : blocks*(cols^blocks) ≤ s*s := Nat.mul_le_mul h₁ h₂
  have h₆ : s ≤ s*s := by nlinarith
  unfold sizeBound MatrixAddressMachine.exactTime
  change 2*blocks*rows+4*blocks+4+1+(2*blocks+2)+
    (blocks*(16*(2+cols^blocks))+1) ≤ 64*s^2
  nlinarith

end EthInapproximability.CurrentPaper.MatrixTableInterlaceSize
