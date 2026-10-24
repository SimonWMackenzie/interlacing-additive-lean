import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Register-framed unary address stages

Source: frozen v8 `B-effectivity-details.tex`, `thm:paper-materialization`,
the charged local row-major arithmetic. Six injectively selected registers
run the literal address controller; all other registers and finite foreign
control are unchanged. Register and label maps are fixed program syntax.
The frame below describes configurations only and is not a machine operation.
-/

namespace EthInapproximability.CurrentPaper.MatrixScalarAddressStage

open Turing BitMachineEncoding

variable {K L W : Type*} [DecidableEq K]

abbrev LocalLabel := MatrixAddressMachine.Label
abbrev LocalStatement := TM2.Stmt (fun _ : Fin 6 => Bool) LocalLabel Bool
abbrev Statement (K L W : Type*) := TM2.Stmt (fun _ : K => Bool) L (Bool × W)
abbrev Config (K L W : Type*) := TM2.Cfg (fun _ : K => Bool) L (Bool × W)

/-- Fixed syntactic register selection and continuation substitution.
No label equivalence, register search or arithmetic instruction is needed. -/
def mapStmt (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L) :
    LocalStatement → Statement K L W
  | .push k b q => .push (register k) (fun v => b v.1) (mapStmt register label next q)
  | .peek k f q => .peek (register k) (fun v b => (f v.1 b, v.2))
      (mapStmt register label next q)
  | .pop k f q => .pop (register k) (fun v b => (f v.1 b, v.2))
      (mapStmt register label next q)
  | .load f q => .load (fun v => (f v.1, v.2)) (mapStmt register label next q)
  | .branch f q r => .branch (fun v => f v.1)
      (mapStmt register label next q) (mapStmt register label next r)
  | .goto f => .goto (fun v => label (f v.1))
  | .halt => .goto (fun _ => next)

noncomputable def frame (register : Fin 6 ↪ K) (foreign : K → List Bool)
    (slots : Fin 6 → List Bool) : K → List Bool := Function.extend register slots foreign

@[simp] theorem frame_apply (register : Fin 6 ↪ K) (foreign : K → List Bool)
    (slots : Fin 6 → List Bool) (k : Fin 6) :
    frame register foreign slots (register k) = slots k :=
  register.injective.extend_apply slots foreign k

theorem frame_other (register : Fin 6 ↪ K) (foreign : K → List Bool)
    (slots : Fin 6 → List Bool) (k : K) (hk : ¬ ∃ i, register i = k) :
    frame register foreign slots k = foreign k :=
  Function.extend_apply' slots foreign k hk

theorem frame_update (register : Fin 6 ↪ K) (foreign : K → List Bool)
    (slots : Fin 6 → List Bool) (k : Fin 6) (bits : List Bool) :
    frame register foreign (Function.update slots k bits) =
      Function.update (frame register foreign slots) (register k) bits := by
  funext j
  by_cases hj : ∃ i, register i = j
  · obtain ⟨i, rfl⟩ := hj
    by_cases hi : i = k
    · subst i
      simp
    · have hne : register i ≠ register k := fun h => hi (register.injective h)
      simp [Function.update_of_ne hi, Function.update_of_ne hne]
  · have hne : j ≠ register k := fun h => hj ⟨k, h.symm⟩
    rw [frame_other _ _ _ _ hj, Function.update_of_ne hne, frame_other _ _ _ _ hj]

theorem frame_eq (register : Fin 6 ↪ K) (foreign : K → List Bool)
    (slots : Fin 6 → List Bool) (h : ∀ i, slots i = foreign (register i)) :
    frame register foreign slots = foreign := by
  funext j
  by_cases hj : ∃ i, register i = j
  · obtain ⟨i, rfl⟩ := hj
    exact (frame_apply _ _ _ _).trans (h i)
  · exact frame_other _ _ _ _ hj

noncomputable def frameCfg (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (w : W) (foreign : K → List Bool) (c : MatrixAddressMachine.Config) : Config K L W :=
  ⟨some (c.l.elim next label), (c.var, w), frame register foreign c.stk⟩

theorem map_stepAux (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (q : LocalStatement) (s : Bool) (w : W) (slots : Fin 6 → List Bool)
    (foreign : K → List Bool) :
    TM2.stepAux (mapStmt register label next q) (s, w) (frame register foreign slots) =
      frameCfg register label next w foreign (TM2.stepAux q s slots) := by
  induction q generalizing s slots with
  | push k b q ih =>
      simp only [mapStmt, TM2.stepAux, frame_apply]
      rw [← frame_update]
      exact ih _ _
  | peek k f q ih => simpa only [mapStmt, TM2.stepAux, frame_apply] using ih _ _
  | pop k f q ih =>
      simp only [mapStmt, TM2.stepAux, frame_apply]
      rw [← frame_update]
      exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases h : f s <;> simp [mapStmt, TM2.stepAux, h, ihq, ihr]
  | goto f => rfl
  | halt => rfl

theorem framed_step (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (Q : L → Statement K L W)
    (hQ : ∀ l, Q (label l) = mapStmt register label next (MatrixAddressMachine.program l))
    (w : W) (foreign : K → List Bool) (c : MatrixAddressMachine.Config)
    (hc : c.l ≠ none) :
    advance Q (frameCfg register label next w foreign c) =
      frameCfg register label next w foreign (advance MatrixAddressMachine.program c) := by
  rcases c with ⟨l, s, slots⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      simpa only [advance, frameCfg, Option.elim_some, TM2.step, hQ, Option.getD_some] using
        map_stepAux register label next (MatrixAddressMachine.program l) s w slots foreign

theorem framed_run_until (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (Q : L → Statement K L W)
    (hQ : ∀ l, Q (label l) = mapStmt register label next (MatrixAddressMachine.program l))
    (w : W) (foreign : K → List Bool) (c : MatrixAddressMachine.Config) (n : ℕ)
    (hc : ∀ j < n, (MatrixAddressMachine.run j c).l ≠ none) :
    ((advance Q)^[n]) (frameCfg register label next w foreign c) =
      frameCfg register label next w foreign (MatrixAddressMachine.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun j hj => hc j (by omega)),
        framed_step register label next Q hQ w foreign _ (hc n (by omega))]
      simp only [MatrixAddressMachine.run, Function.iterate_succ_apply']

theorem framed_outputs (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (Q : L → Statement K L W)
    (hQ : ∀ l, Q (label l) = mapStmt register label next (MatrixAddressMachine.program l))
    (w : W) (foreign : K → List Bool) (c : MatrixAddressMachine.Config) (bound : ℕ)
    (hc : (MatrixAddressMachine.run bound c).l = none) :
    ∃ t ≤ bound, ((advance Q)^[t]) (frameCfg register label next w foreign c) =
      frameCfg register label next w foreign (MatrixAddressMachine.run bound c) := by
  obtain ⟨t, ht, _, he, hfirst⟩ :=
    BitMachineSubroutine.first_halt_cfg MatrixAddressMachine.program c bound hc
  refine ⟨t, ht, ?_⟩
  rw [framed_run_until register label next Q hQ w foreign c t hfirst]
  exact congrArg (frameCfg register label next w foreign) he

/-- A complete multiplication-plus-addition stage in the ambient bank.
Only the output register changes; the suffix already in that register stays
in place. The row, width, column, both work registers and all foreign state
are preserved. The continuation is reached within the literal address bound. -/
theorem address_stage (register : Fin 6 ↪ K) (label : LocalLabel → L) (next : L)
    (Q : L → Statement K L W)
    (hQ : ∀ l, Q (label l) = mapStmt register label next (MatrixAddressMachine.program l))
    (w : W) (bank : K → List Bool) (row width column : ℕ) (s : Bool)
    (hr : bank (register 0) = List.replicate row true)
    (hw : bank (register 1) = List.replicate width true)
    (hc : bank (register 2) = List.replicate column true)
    (hwork₁ : bank (register 3) = []) (hwork₂ : bank (register 4) = []) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width column,
      ((advance Q)^[t]) (⟨some (label .outer), (s, w), bank⟩ : Config K L W) =
        ⟨some next, (false, w), Function.update bank (register 5)
          (List.replicate (row * width + column) true ++ bank (register 5))⟩ := by
  let initial := MatrixAddressMachine.cfg (some .outer) s
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] [] (bank (register 5))
  let final := MatrixAddressMachine.cfg none false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] []
    (List.replicate (row * width + column) true ++ bank (register 5))
  have hrun : MatrixAddressMachine.run (MatrixAddressMachine.exactTime row width column)
      initial = final := MatrixAddressMachine.address_run row width column s (bank (register 5))
  have hinit : frame register bank initial.stk = bank := by
    apply frame_eq
    intro i
    fin_cases i <;> simp [initial, MatrixAddressMachine.cfg, hr, hw, hc, hwork₁, hwork₂]
  have hfinalLocal : final.stk = Function.update initial.stk 5
      (List.replicate (row * width + column) true ++ bank (register 5)) := by
    funext i
    fin_cases i <;> simp [initial, final, MatrixAddressMachine.cfg]
  have hfinal : frame register bank final.stk = Function.update bank (register 5)
      (List.replicate (row * width + column) true ++ bank (register 5)) := by
    rw [hfinalLocal, frame_update, hinit]
  obtain ⟨t, ht, he⟩ := framed_outputs register label next Q hQ w bank initial
    (MatrixAddressMachine.exactTime row width column) (by rw [hrun]; rfl)
  rw [hrun] at he
  refine ⟨t, ht, ?_⟩
  change ((advance Q)^[t])
      (⟨some (label .outer), (s, w), frame register bank initial.stk⟩ : Config K L W) =
    ⟨some next, (false, w), frame register bank final.stk⟩ at he
  simpa only [hinit, hfinal] using he

end EthInapproximability.CurrentPaper.MatrixScalarAddressStage
