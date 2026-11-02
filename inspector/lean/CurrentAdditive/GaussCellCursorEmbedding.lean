import CurrentAdditive.GaussWordGridTraversal
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! The three physical cursor/answer banks are identified with the traversal
slots by an injective stack map. Every unused ghost bank remains foreign. -/

namespace CurrentAdditive.GaussCellCursorEmbedding

noncomputable section

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

variable (N : Nat) (hN : 30 ≤ N)

def cursor (j : Fin N) : GaussWordGridTraversal.CellStack N :=
  if j.val = 7 then .inr 0 else
  if j.val = 19 then .inr 1 else
  if j.val = 29 then .inr 2 else .inl j

theorem cursor_injective : Function.Injective (cursor N) := by
  intro a b h
  apply Fin.ext
  by_cases ha7 : a.val=7 <;> by_cases hb7 : b.val=7 <;>
    by_cases ha19 : a.val=19 <;> by_cases hb19 : b.val=19 <;>
    by_cases ha29 : a.val=29 <;> by_cases hb29 : b.val=29
  all_goals simp_all [cursor]

def slots : Fin N ↪ GaussWordGridTraversal.CellStack N :=
  ⟨cursor N,cursor_injective N⟩

@[simp] theorem slots_row : slots N ⟨7,by omega⟩ = .inr 0 := by simp [slots,cursor]
@[simp] theorem slots_col : slots N ⟨19,by omega⟩ = .inr 1 := by simp [slots,cursor]
@[simp] theorem slots_answer : slots N ⟨29,by omega⟩ = .inr 2 := by simp [slots,cursor]

variable {K J L V : Type*} [DecidableEq K] [DecidableEq J]

def relocate (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) : TM2.Stmt (fun _ : J => Bool) L V :=
  BitMachineStackEmbedding.stmt ι id id id none (P l)

/-- An actual whole-bank local return becomes an actual whole-bank ambient
return, with exactly the selected answer bank changed. No assumption about
the other bank contents is introduced by this embedding. -/
theorem outputs_update (ι : K ↪ J)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (start : L) (initial final : V) (S : J → List Bool)
    (target : K) (answer : List Bool) (t : Nat)
    (hrun : ((advance P)^[t])
      (⟨some start,initial,fun j => S (ι j)⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none,final,Function.update (fun j => S (ι j)) target answer⟩) :
    ∃ u ≤ t, ((advance (relocate ι P))^[u])
      (⟨some start,initial,S⟩ : TM2.Cfg (fun _ : J => Bool) L V) =
      ⟨none,final,Function.update S (ι target) answer⟩ := by
  have hh := congrArg (fun c => c.l) hrun
  obtain ⟨u,hu,h⟩ := BitMachineStackEmbedding.outputs ι S id id id
    (fun _ => rfl) none P (relocate ι P) (fun _ => rfl)
    (⟨some start,initial,fun j => S (ι j)⟩ : TM2.Cfg (fun _ : K => Bool) L V)
    t hh
  rw [hrun] at h
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,Option.map_some,Option.map_none,id_eq] at h
  rw [BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_restrict] at h
  simpa only [BitMachineStackEmbedding.bank_restrict] using And.intro hu h |>.elim
    (fun hu h => ⟨u,hu,h⟩)

#print axioms cursor_injective
#print axioms outputs_update

end
end CurrentAdditive.GaussCellCursorEmbedding
