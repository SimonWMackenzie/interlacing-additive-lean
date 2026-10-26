import EthInapproximability.CurrentPaper.MatrixTableInterlaceRowReverse
import EthInapproximability.CurrentPaper.MatrixTableInterlaceTransfer
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# One controller for ordered transfer into row-block reversal

The three-stack order-preserving transfer and the six-stack row-block
controller share the transfer target/reversal input stack.  This physically
charges the word handoff.  The unary block width is an explicit input.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceRowBridge

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev Stack := MatrixTableInterlaceTransfer.Stack ⊕ Fin 5
abbrev Label := MatrixTableInterlaceTransfer.Label ⊕
  SamplerMachineBlockReverse.Label
abbrev Control := MatrixTableInterlaceTransfer.Control ×
  SamplerMachineBlockReverse.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

private def perm : Fin 8 ≃ Fin 8 where
  toFun := ![2,3,4,5,6,7,0,1]
  invFun := ![6,7,0,1,2,3,4,5]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def rowSlots : SamplerMachineBlockReverse.Stack ⊕ Fin 2 ≃ Stack :=
  (finSumFinEquiv.trans perm).trans finSumFinEquiv.symm

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some SamplerMachineBlockReverse.Label.check)
      (MatrixTableInterlaceTransfer.program l)
  | .inr l => renameStmt rowSlots
      (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (SamplerMachineBlockReverse.program l))

def cfg (l : Option Label) (v : Control)
    (source temp input width saved scratch acc output : List Bool) : Config :=
  ⟨l,v,Sum.elim (![source,temp,input] : Fin 3 → List Bool)
    (![width,saved,scratch,acc,output] : Fin 5 → List Bool)⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def transferFrame (w : SamplerMachineBlockReverse.Control)
    (foreign : Fin 5 → List Bool)
    (c : MatrixTableInterlaceTransfer.Config) : Config :=
  liftCfg (some SamplerMachineBlockReverse.Label.check) w foreign c

def rowFrame (v : MatrixTableInterlaceTransfer.Control)
    (foreign : Fin 2 → List Bool)
    (c : SamplerMachineBlockReverse.Config) : Config :=
  renameCfg rowSlots (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    (liftCfg none v foreign c)

private theorem transfer_input_frame (bits width : List Bool) :
    transferFrame SamplerMachineBlockReverse.initial
      (![width,[],[],[],[]] : Fin 5 → List Bool)
      (MatrixTableInterlaceTransfer.cfg (some .toTemp) none bits [] []) =
    cfg (some (.inl .toTemp))
      (none,SamplerMachineBlockReverse.initial) bits [] [] width [] [] [] [] := by
  rfl

private theorem transfer_output_frame (bits width : List Bool) :
    transferFrame SamplerMachineBlockReverse.initial
      (![width,[],[],[],[]] : Fin 5 → List Bool)
      (MatrixTableInterlaceTransfer.cfg none none [] [] bits) =
    cfg (some (.inr .check))
      (none,SamplerMachineBlockReverse.initial) [] [] bits width [] [] [] [] := by
  rfl

theorem transfer_phase (bits width : List Bool) :
    ∃ t ≤ 2*bits.length+2,
      run t (cfg (some (.inl .toTemp))
        (none,SamplerMachineBlockReverse.initial) bits [] [] width [] [] [] []) =
      cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] [] bits width [] [] [] [] := by
  have hlocal := MatrixTableInterlaceTransfer.transfer_run bits []
  obtain ⟨t,ht,he⟩ := lift_outputs MatrixTableInterlaceTransfer.program program
    (some SamplerMachineBlockReverse.Label.check) (fun _ => rfl)
    SamplerMachineBlockReverse.initial
    (![width,[],[],[],[]] : Fin 5 → List Bool)
    (MatrixTableInterlaceTransfer.cfg (some .toTemp) none bits [] [])
    (2*bits.length+2) (by
      change (MatrixTableInterlaceTransfer.run (2*bits.length+2) _).l = none
      rw [hlocal]
      rfl)
  change run t (transferFrame _ _ _) =
    transferFrame _ _ (MatrixTableInterlaceTransfer.run _ _) at he
  rw [hlocal, transfer_input_frame, transfer_output_frame] at he
  simpa only [List.append_nil] using (show ∃ t ≤ 2*bits.length+2,
    run t (cfg (some (.inl .toTemp))
      (none,SamplerMachineBlockReverse.initial) bits [] [] width [] [] [] []) =
    cfg (some (.inr .check))
      (none,SamplerMachineBlockReverse.initial) [] [] (bits ++ []) width [] [] [] []
    from ⟨t,ht,he⟩)

private theorem row_input_frame (bits width : List Bool) :
    rowFrame none (![[],[]] : Fin 2 → List Bool)
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial bits width [] [] [] []) =
    cfg (some (.inr .check))
      (none,SamplerMachineBlockReverse.initial) [] [] bits width [] [] [] [] := by
  unfold rowFrame renameCfg liftCfg cfg SamplerMachineBlockReverse.cfg
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem row_output_frame (bits width : List Bool) :
    rowFrame none (![[],[]] : Fin 2 → List Bool)
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial [] width [] [] bits []) =
    cfg (some (.inr .check))
      (none,SamplerMachineBlockReverse.initial) [] [] [] width [] [] bits [] := by
  unfold rowFrame renameCfg liftCfg cfg SamplerMachineBlockReverse.cfg
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem no_halt_before {K L V : Type} [DecidableEq K]
    {P : L → TM2.Stmt (fun _ : K => Bool) L V}
    {c : TM2.Cfg (fun _ : K => Bool) L V} {t : ℕ}
    (h : (((advance P)^[t]) c).l ≠ none) :
    ∀ k < t, (((advance P)^[k]) c).l ≠ none := by
  intro k hk hk0
  let d := ((advance P)^[k]) c
  have hd : d.l = none := hk0
  have hstep : advance P d = d := by
    rcases d with ⟨l,v,S⟩
    cases l with
    | none => rfl
    | some l => simp at hd
  have hfixed : ∀ n : ℕ, ((advance P)^[n]) d = d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        exact hstep
  have ht : t = (t-k)+k := by omega
  rw [ht, Function.iterate_add_apply, hfixed] at h
  exact h hd

theorem reverse_phase (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : 0 < rows*cols) :
    run (blocks*SamplerMachineBlockReverse.blockStep (rows*cols))
      (cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] []
        (MatrixMaterialization.rowMajor f)
        (List.replicate (rows*cols) true) [] [] [] []) =
      cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] [] []
        (List.replicate (rows*cols) true) [] []
        (MatrixMaterialization.rowMajor (fun r c => f
          (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c)) [] := by
  let t := blocks*SamplerMachineBlockReverse.blockStep (rows*cols)
  let c := SamplerMachineBlockReverse.cfg (some .check)
    SamplerMachineBlockReverse.initial (MatrixMaterialization.rowMajor f)
    (List.replicate (rows*cols) true) [] [] [] []
  have hlocal := MatrixTableInterlaceRowReverse.rowBlock_run
    blocks rows cols f hwidth
  have hn : ∀ k < t,
      (((advance SamplerMachineBlockReverse.program)^[k]) c).l ≠ none := by
    apply no_halt_before
    change (SamplerMachineBlockReverse.run t c).l ≠ none
    rw [hlocal]
    simp [SamplerMachineBlockReverse.cfg]
  have h := lift_run_until_renamed rowSlots (Equiv.sumComm _ _)
    (Equiv.prodComm _ _) SamplerMachineBlockReverse.program program none
    (fun _ => rfl) none (![[],[]] : Fin 2 → List Bool) c t hn
  change run t (rowFrame none _ c) =
    rowFrame none _ (SamplerMachineBlockReverse.run t c) at h
  rw [hlocal, row_input_frame, row_output_frame] at h
  exact h

theorem transfer_then_reverse (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : 0 < rows*cols) :
    ∃ t ≤ 2*(MatrixMaterialization.rowMajor f).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*cols),
      run t (cfg (some (.inl .toTemp))
        (none,SamplerMachineBlockReverse.initial)
        (MatrixMaterialization.rowMajor f) [] []
        (List.replicate (rows*cols) true) [] [] [] []) =
      cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] [] []
        (List.replicate (rows*cols) true) [] []
        (MatrixMaterialization.rowMajor (fun r c => f
          (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c)) [] := by
  obtain ⟨u,hu,he⟩ := transfer_phase
    (MatrixMaterialization.rowMajor f) (List.replicate (rows*cols) true)
  have h := run_add he (blocks*SamplerMachineBlockReverse.blockStep (rows*cols))
  rw [reverse_phase blocks rows cols f hwidth] at h
  exact ⟨u+blocks*SamplerMachineBlockReverse.blockStep (rows*cols), by omega, h⟩

theorem numberedInterlace_bridge (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤ 2*(MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*(cols^blocks)),
      run t (cfg (some (.inl .toTemp))
        (none,SamplerMachineBlockReverse.initial)
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f)) [] []
        (List.replicate (rows*(cols^blocks)) true) [] [] [] []) =
      cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] [] []
        (List.replicate (rows*(cols^blocks)) true) [] []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f)) [] := by
  obtain ⟨t,ht,he⟩ := transfer_then_reverse blocks rows (cols^blocks)
    (MatrixTableInterlace.interlaced (blocks := blocks) f) hwidth
  refine ⟨t,ht,?_⟩
  simpa only [MatrixTableInterlaceRowReverse.numberedInterlace_eq] using he

theorem bridge_bound_polynomial (blocks rows cols : ℕ) :
    2*((blocks*rows)*cols)+2 +
      blocks*SamplerMachineBlockReverse.blockStep (rows*cols) ≤
      7*(blocks+rows+cols+blocks*rows*cols+1)^2 := by
  let n := blocks+rows+cols+blocks*rows*cols+1
  have hlen : (blocks*rows)*cols+1 ≤ n := by dsimp [n]; omega
  have hsq := Nat.pow_le_pow_left hlen 2
  have hr := MatrixTableInterlaceRowReverse.rowBlock_bound_polynomial
    blocks rows cols
  change blocks*SamplerMachineBlockReverse.blockStep (rows*cols) ≤ 5*n^2 at hr
  change 2*((blocks*rows)*cols)+2 +
    blocks*SamplerMachineBlockReverse.blockStep (rows*cols) ≤ 7*n^2
  nlinarith

end EthInapproximability.CurrentPaper.MatrixTableInterlaceRowBridge
