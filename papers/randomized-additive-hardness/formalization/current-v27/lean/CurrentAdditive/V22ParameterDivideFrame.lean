import CurrentAdditive.V22ParameterDivide

namespace V22ParameterDivide
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
variable {Base : Type*} [DecidableEq Base]
abbrev Control := ((Option Bool × Option Bool) × Bool) × Option Bool

def framedProgram {J : Type*} [DecidableEq J]
    (left right target : Base) (ι : Stack Base ↪ J) (l : Label) :
    TM2.Stmt (fun _ : J => Bool) Label Control :=
  BitMachineStackEmbedding.stmt ι id id id none (program left right target l)

theorem run_install_framed_from_ambient {J : Type*} [DecidableEq J]
    (left right target : Base) (n m : ℕ)
    (ι : Stack Base ↪ J) (S : J → List Bool)
    (hleft : S (ι (.inl left)) = List.replicate n true)
    (hright : S (ι (.inl right)) = List.replicate m true)
    (htarget : S (ι (.inl target)) = [])
    (hfresh : ∀ k : Fin 9, S (ι (.inr k)) = []) :
    let B : Base → List Bool := fun j => S (ι (.inl j))
    ∃ t ≤ clock n m, ((advance (framedProgram left right target ι))^[t])
      (⟨some startLabel,startControl,S⟩ : TM2.Cfg (fun _ : J => Bool) Label Control) =
      ⟨none,startControl,bank ι S (terminal B target n m)⟩ := by
  dsimp only
  let B : Base → List Bool := fun j => S (ι (.inl j))
  have hplace : bank ι S (initial B)=S := by
    apply bank_eq_self
    intro j
    cases j with
    | inl j => rfl
    | inr j => exact (hfresh j).symm
  obtain ⟨u,hu,he⟩ := run_install B left right target n m hleft hright htarget
  have hh : (((advance (program left right target))^[u])
      (⟨some startLabel,startControl,initial B⟩ : TM2.Cfg (fun _ : Stack Base => Bool) Label Control)).l=none := by
    rw [he]
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none (program left right target)
    (framedProgram left right target ι) (by intro l; rfl)
    (⟨some startLabel,startControl,initial B⟩ : TM2.Cfg (fun _ : Stack Base => Bool) Label Control) u hh
  rw [he] at hr
  change ((advance (framedProgram left right target ι))^[t])
    ⟨some startLabel,startControl,bank ι S (initial B)⟩ =
    ⟨none,startControl,bank ι S (terminal B target n m)⟩ at hr
  rw [hplace] at hr
  exact ⟨t,ht.trans hu,hr⟩

theorem ambient_target {J : Type*} [DecidableEq J]
    (B : Base → List Bool) (target : Base) (n m : ℕ) (ι : Stack Base ↪ J) (S : J → List Bool) :
    bank ι S (terminal B target n m) (ι (.inl target))=List.replicate (n/m) true := by
  rw [bank_at,terminal_target]

theorem ambient_base_other {J : Type*} [DecidableEq J]
    (B : Base → List Bool) (target j : Base) (hj : j≠target) (n m : ℕ)
    (ι : Stack Base ↪ J) (S : J → List Bool) :
    bank ι S (terminal B target n m) (ι (.inl j))=B j := by
  rw [bank_at,terminal_base_other B target j hj]

end
end V22ParameterDivide
