import EthInapproximability.CurrentPaper.MatrixStage4ActiveGather
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Fixed graph active-rank controller for arbitrary `s`

The controller gathers the strict predecessor column prefix from a literal
row-major vector table and then counts every true bit into a unary rank.
Unlike the exact-NP two-active-item controller, its finite control never
stores or saturates the rank.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ActiveRankMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 10
abbrev Label := MatrixStrideGather.Label ⊕ Unit
abbrev Control := MatrixStrideGather.Control × MatrixStage4ActiveCount.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := ((MatrixStrideGather.baseControl,false),none)
def gatherStart : Label := .inl (.inr .test)
def countStart : Label := .inr ()

def gatherStacks : (Fin 7 ⊕ Fin 3) ⊕ Fin 0 ≃ Stack :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 0))).trans finSumFinEquiv

def countPermutation : Stack ≃ Stack where
  toFun := ![5,7,0,1,2,3,4,6,8,9]
  invFun := ![2,3,4,5,6,0,7,1,8,9]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def countStacks : Fin 2 ⊕ Fin 8 ≃ Stack :=
  finSumFinEquiv.trans countPermutation

def countLabels : Unit ⊕ MatrixStrideGather.Label ≃ Label where
  toFun
    | .inl u => .inr u
    | .inr l => .inl l
  invFun
    | .inl l => .inr l
    | .inr u => .inl u
  left_inv l := by rcases l with u | l <;> rfl
  right_inv l := by rcases l with l | u <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt gatherStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some ()) (MatrixStrideGather.program l))
  | .inr () => renameStmt countStacks countLabels (Equiv.prodComm _ _)
      (liftStmt none (MatrixStage4ActiveCount.program ()))

def cfg (l : Option Label) (v : Control)
    (index source gathered counter stride work : List Bool) : Config :=
  ⟨l,v,![index,[],[],source,[],gathered,[],counter,stride,work]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def gatherFrame (c : MatrixStrideGather.Config) : Config :=
  renameCfg gatherStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some ()) none (fun i : Fin 0 => Fin.elim0 i) c)

theorem gather_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    ∃ t ≤ i.val *
        (3*(α.val+i.val*q)+3*(n*q)+2*q+12)+1,
      run t (cfg (some gatherStart) initial
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate i.val true) (List.replicate q true) []) =
      cfg (some countStart) initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse
        [] (List.replicate q true) [] := by
  obtain ⟨t,ht,he⟩ := MatrixStage4ActiveGather.gather_before_run vectors i α
  have hhalt : (MatrixStrideGather.run t
      (MatrixStrideGather.cfg (some (.inr .test)) false
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors) []
        (List.replicate i.val true) (List.replicate q true) [])).l = none := by
    rw [he]
    rfl
  obtain ⟨u,hu,hr⟩ := lift_outputs_renamed gatherStacks
    (Equiv.refl _) (Equiv.refl _) MatrixStrideGather.program program
    (some ()) (fun _ => rfl) none (fun i : Fin 0 => Fin.elim0 i)
    (MatrixStrideGather.cfg (some (.inr .test)) false
      (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors) []
      (List.replicate i.val true) (List.replicate q true) []) t hhalt
  change run u (gatherFrame _) = gatherFrame (MatrixStrideGather.run t _) at hr
  rw [he] at hr
  have hi : gatherFrame (MatrixStrideGather.cfg (some (.inr .test)) false
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors) []
        (List.replicate i.val true) (List.replicate q true) []) =
      cfg (some gatherStart) initial
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate i.val true) (List.replicate q true) [] := by
    unfold gatherFrame renameCfg liftCfg cfg MatrixStrideGather.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : gatherFrame (MatrixStrideGather.cfg none false
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse
        [] (List.replicate q true) []) =
      cfg (some countStart) initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse
        [] (List.replicate q true) [] := by
    unfold gatherFrame renameCfg liftCfg cfg MatrixStrideGather.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨u,hu.trans ht,by simpa only [hi,hf] using hr⟩

def countFrame (index source stride : List Bool)
    (c : MatrixStage4ActiveCount.Config) : Config :=
  renameCfg countStacks countLabels (Equiv.prodComm _ _)
    (liftCfg none (MatrixStrideGather.baseControl,false)
      (fun i => ![index,[],[],source,[],[],stride,[]] i) c)

theorem count_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    ∃ t ≤ i.val+1,
      run t (cfg (some countStart) initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse
        [] (List.replicate q true) []) =
      cfg none initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate (Construction.activeRank vectors α i) true)
        (List.replicate q true) [] := by
  have he := MatrixStage4ActiveCount.active_rank_run vectors i α
  have hhalt : (MatrixStage4ActiveCount.run (i.val+1)
      (MatrixStage4ActiveCount.cfg (some ())
        MatrixStage4ActiveCount.initial
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse [])).l = none := by
    rw [he]
    rfl
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed countStacks countLabels
    (Equiv.prodComm _ _) MatrixStage4ActiveCount.program program
    none (fun _ => rfl) (MatrixStrideGather.baseControl,false)
    (fun j => ![List.replicate (α.val+i.val*q) true,[],[],
      MatrixMaterialization.rowMajor vectors,[],[],
      List.replicate q true,[]] j)
    (MatrixStage4ActiveCount.cfg (some ())
      MatrixStage4ActiveCount.initial
      (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse [])
    (i.val+1) hhalt
  change run t (countFrame _ _ _ _) =
    countFrame _ _ _ (MatrixStage4ActiveCount.run _ _) at hr
  rw [he] at hr
  have hi : countFrame (List.replicate (α.val+i.val*q) true)
      (MatrixMaterialization.rowMajor vectors) (List.replicate q true)
      (MatrixStage4ActiveCount.cfg (some ())
        MatrixStage4ActiveCount.initial
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse []) =
      cfg (some countStart) initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse
        [] (List.replicate q true) [] := by
    unfold countFrame renameCfg liftCfg cfg MatrixStage4ActiveCount.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : countFrame (List.replicate (α.val+i.val*q) true)
      (MatrixMaterialization.rowMajor vectors) (List.replicate q true)
      (MatrixStage4ActiveCount.cfg none MatrixStage4ActiveCount.initial []
        (List.replicate (Construction.activeRank vectors α i) true)) =
      cfg none initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate (Construction.activeRank vectors α i) true)
        (List.replicate q true) [] := by
    unfold countFrame renameCfg liftCfg cfg MatrixStage4ActiveCount.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem active_rank_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    ∃ t ≤ i.val *
        (3*(α.val+i.val*q)+3*(n*q)+2*q+12)+i.val+2,
      run t (cfg (some gatherStart) initial
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate i.val true) (List.replicate q true) []) =
      cfg none initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate (Construction.activeRank vectors α i) true)
        (List.replicate q true) [] := by
  obtain ⟨a,ha,hg⟩ := gather_run vectors i α
  obtain ⟨b,hb,hc⟩ := count_run vectors i α
  exact ⟨a+b,by omega,(run_add hg b).trans hc⟩

theorem active_slot_run {n q s : ℕ}
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s)
    (i : Fin n) (α : Fin q) (hi : vectors i α = true) :
    ∃ t ≤ i.val *
        (3*(α.val+i.val*q)+3*(n*q)+2*q+12)+i.val+2,
      run t (cfg (some gatherStart) initial
        (List.replicate α.val true) (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate i.val true) (List.replicate q true) []) =
      cfg none initial
        (List.replicate (α.val+i.val*q) true)
        (MatrixMaterialization.rowMajor vectors)
        [] (List.replicate
          (Construction.activeSlot vectors cap α ⟨i,hi⟩).val true)
        (List.replicate q true) [] := by
  simpa only [Construction.activeSlot, Construction.activeRank] using
    active_rank_run vectors i α

end EthInapproximability.CurrentPaper.MatrixStage4ActiveRankMachine
