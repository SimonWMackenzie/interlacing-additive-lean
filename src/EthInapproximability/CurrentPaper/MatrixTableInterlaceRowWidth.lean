import EthInapproximability.CurrentPaper.MatrixTableInterlaceRowBridge
import EthInapproximability.CurrentPaper.MatrixAddressMachine

/-!
# Physical width preparation for the numbered interlace table

One fixed Boolean-stack controller first multiplies supplied unary old-row
and new-column counts, then passes the resulting width on a shared stack to
the word-transfer and row-block reversal controller.  The two original
counts and literal interlace word remain explicit inputs.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceRowWidth

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev AStack := Fin 6
abbrev RStack := MatrixTableInterlaceRowBridge.Stack
abbrev Stack := AStack ⊕ Fin 7
abbrev Label := MatrixAddressMachine.Label ⊕ MatrixTableInterlaceRowBridge.Label
abbrev Control := Bool × MatrixTableInterlaceRowBridge.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

private def perm : Fin 13 ≃ Fin 13 where
  toFun := ![6,7,8,5,9,10,11,12,0,1,2,3,4]
  invFun := ![8,9,10,11,12,3,0,1,2,4,5,6,7]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def rowSlots : RStack ⊕ Fin 5 ≃ Stack :=
  ((finSumFinEquiv : RStack ≃ Fin 8).sumCongr (Equiv.refl (Fin 5))).trans
    ((finSumFinEquiv.trans perm).trans finSumFinEquiv.symm)

def rowStart : Label := .inr (.inl .toTemp)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl MatrixTableInterlaceTransfer.Label.toTemp))
      (MatrixAddressMachine.program l)
  | .inr l => renameStmt rowSlots (Equiv.sumComm _ _)
      (Equiv.prodComm _ _)
      (liftStmt none (MatrixTableInterlaceRowBridge.program l))

def cfg (l : Option Label) (v : Control)
    (rows cols column aSaved aScratch width : List Bool)
    (source temp input saved scratch acc output : List Bool) : Config :=
  ⟨l,v,Sum.elim (![rows,cols,column,aSaved,aScratch,width] : Fin 6 → List Bool)
    (![source,temp,input,saved,scratch,acc,output] : Fin 7 → List Bool)⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def addressFrame (v : MatrixTableInterlaceRowBridge.Control)
    (foreign : Fin 7 → List Bool) (c : MatrixAddressMachine.Config) : Config :=
  liftCfg (some (.inl MatrixTableInterlaceTransfer.Label.toTemp)) v foreign c

def rowFrame (v : Bool) (foreign : Fin 5 → List Bool)
    (c : MatrixTableInterlaceRowBridge.Config) : Config :=
  renameCfg rowSlots (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    (liftCfg none v foreign c)

private theorem address_input_frame (rows cols : ℕ) (bits : List Bool) :
    addressFrame (none,SamplerMachineBlockReverse.initial)
      (![bits,[],[],[],[],[],[]] : Fin 7 → List Bool)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate rows true) (List.replicate cols true) [] [] [] []) =
    cfg (some (.inl .outer)) (false,(none,SamplerMachineBlockReverse.initial))
      (List.replicate rows true) (List.replicate cols true) [] [] [] []
      bits [] [] [] [] [] [] := by
  rfl

private theorem address_output_frame (rows cols : ℕ) (bits : List Bool) :
    addressFrame (none,SamplerMachineBlockReverse.initial)
      (![bits,[],[],[],[],[],[]] : Fin 7 → List Bool)
      (MatrixAddressMachine.cfg none false
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true)) =
    cfg (some rowStart) (false,(none,SamplerMachineBlockReverse.initial))
      (List.replicate rows true) (List.replicate cols true) [] [] []
      (List.replicate (rows*cols) true) bits [] [] [] [] [] [] := by
  rfl

theorem address_phase (rows cols : ℕ) (bits : List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime rows cols 0,
      run t (cfg (some (.inl .outer))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] [] []
        bits [] [] [] [] [] []) =
      cfg (some rowStart) (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true) bits [] [] [] [] [] [] := by
  have hlocal : MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime rows cols 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate rows true) (List.replicate cols true) [] [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true) := by
    simpa using MatrixAddressMachine.address_run rows cols 0 false []
  obtain ⟨t,ht,he⟩ := lift_outputs MatrixAddressMachine.program program
    (some (.inl MatrixTableInterlaceTransfer.Label.toTemp)) (fun _ => rfl)
    (none,SamplerMachineBlockReverse.initial)
    (![bits,[],[],[],[],[],[]] : Fin 7 → List Bool)
    (MatrixAddressMachine.cfg (some .outer) false
      (List.replicate rows true) (List.replicate cols true) [] [] [] [])
    (MatrixAddressMachine.exactTime rows cols 0) (by
      change (MatrixAddressMachine.run _ _).l = none
      rw [hlocal]
      rfl)
  change run t (addressFrame _ _ _) =
    addressFrame _ _ (MatrixAddressMachine.run _ _) at he
  rw [hlocal, address_input_frame, address_output_frame] at he
  exact ⟨t,ht,he⟩

private theorem row_input_frame (rows cols : ℕ) (bits : List Bool) :
    rowFrame false (![List.replicate rows true,List.replicate cols true,[],[],[]] :
      Fin 5 → List Bool)
      (MatrixTableInterlaceRowBridge.cfg (some (.inl .toTemp))
        (none,SamplerMachineBlockReverse.initial) bits [] []
        (List.replicate (rows*cols) true) [] [] [] []) =
    cfg (some rowStart) (false,(none,SamplerMachineBlockReverse.initial))
      (List.replicate rows true) (List.replicate cols true) [] [] []
      (List.replicate (rows*cols) true) bits [] [] [] [] [] [] := by
  unfold rowFrame renameCfg liftCfg cfg MatrixTableInterlaceRowBridge.cfg
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem row_output_frame (rows cols : ℕ) (bits : List Bool) :
    rowFrame false (![List.replicate rows true,List.replicate cols true,[],[],[]] :
      Fin 5 → List Bool)
      (MatrixTableInterlaceRowBridge.cfg (some (.inr .check))
        (none,SamplerMachineBlockReverse.initial) [] [] []
        (List.replicate (rows*cols) true) [] [] bits []) =
    cfg (some (.inr (.inr .check)))
      (false,(none,SamplerMachineBlockReverse.initial))
      (List.replicate rows true) (List.replicate cols true) [] [] []
      (List.replicate (rows*cols) true) [] [] [] [] [] bits [] := by
  unfold rowFrame renameCfg liftCfg cfg MatrixTableInterlaceRowBridge.cfg
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
    | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]
  have ht : t = (t-k)+k := by omega
  rw [ht, Function.iterate_add_apply, hfixed] at h
  exact h hd

theorem row_phase (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : 0 < rows*cols) :
    ∃ t ≤ 2*(MatrixMaterialization.rowMajor f).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*cols),
      run t (cfg (some rowStart)
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true)
        (MatrixMaterialization.rowMajor f) [] [] [] [] [] []) =
      cfg (some (.inr (.inr .check)))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true) [] [] [] [] []
        (MatrixMaterialization.rowMajor (fun r c => f
          (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c)) [] := by
  obtain ⟨t,ht,he⟩ := MatrixTableInterlaceRowBridge.transfer_then_reverse
    blocks rows cols f hwidth
  let c := MatrixTableInterlaceRowBridge.cfg (some (.inl .toTemp))
    (none,SamplerMachineBlockReverse.initial)
    (MatrixMaterialization.rowMajor f) [] []
    (List.replicate (rows*cols) true) [] [] [] []
  have hn : ∀ k < t,
      (((advance MatrixTableInterlaceRowBridge.program)^[k]) c).l ≠ none := by
    apply no_halt_before
    change (MatrixTableInterlaceRowBridge.run t c).l ≠ none
    rw [he]
    simp [MatrixTableInterlaceRowBridge.cfg]
  have h := lift_run_until_renamed rowSlots (Equiv.sumComm _ _)
    (Equiv.prodComm _ _) MatrixTableInterlaceRowBridge.program program none
    (fun _ => rfl) false
    (![List.replicate rows true,List.replicate cols true,[],[],[]] : Fin 5 → List Bool)
    c t hn
  change run t (rowFrame false _ c) =
    rowFrame false _ (MatrixTableInterlaceRowBridge.run t c) at h
  rw [he, row_input_frame, row_output_frame] at h
  exact ⟨t,ht,h⟩

theorem width_then_reverse (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : 0 < rows*cols) :
    ∃ t ≤ MatrixAddressMachine.exactTime rows cols 0 +
      (2*(MatrixMaterialization.rowMajor f).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*cols)),
      run t (cfg (some (.inl .outer))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] [] []
        (MatrixMaterialization.rowMajor f) [] [] [] [] [] []) =
      cfg (some (.inr (.inr .check)))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate cols true) [] [] []
        (List.replicate (rows*cols) true) [] [] [] [] []
        (MatrixMaterialization.rowMajor (fun r c => f
          (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c)) [] := by
  obtain ⟨u,hu,he₁⟩ := address_phase rows cols (MatrixMaterialization.rowMajor f)
  obtain ⟨v,hv,he₂⟩ := row_phase blocks rows cols f hwidth
  have h := run_add he₁ v
  rw [he₂] at h
  exact ⟨u+v, by omega, h⟩

/-- Starting with unary old rows and the computed interlace-column count,
the single controller physically prepares the block width, transfers the
literal interlace word, and leaves the exact paper-numbered interlace word. -/
theorem numberedInterlace_width_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤ MatrixAddressMachine.exactTime rows (cols^blocks) 0 +
      (2*(MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*(cols^blocks))),
      run t (cfg (some (.inl .outer))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate (cols^blocks) true)
        [] [] [] []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f))
        [] [] [] [] [] []) =
      cfg (some (.inr (.inr .check)))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate (cols^blocks) true)
        [] [] [] (List.replicate (rows*(cols^blocks)) true)
        [] [] [] [] []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f)) [] := by
  obtain ⟨t,ht,he⟩ := width_then_reverse blocks rows (cols^blocks)
    (MatrixTableInterlace.interlaced (blocks := blocks) f) hwidth
  refine ⟨t,ht,?_⟩
  simpa only [MatrixTableInterlaceRowReverse.numberedInterlace_eq] using he

theorem width_bridge_bound_polynomial (blocks rows cols : ℕ) :
    MatrixAddressMachine.exactTime rows cols 0 +
      (2*((blocks*rows)*cols)+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*cols)) ≤
      11*(blocks+rows+cols+blocks*rows*cols+1)^2 := by
  let n := blocks+rows+cols+blocks*rows*cols+1
  have hsmall : rows+cols+1 ≤ n := by dsimp [n]; omega
  have hsquares := Nat.pow_le_pow_left hsmall 2
  have haddr := MatrixAddressMachine.exactTime_bound rows cols 0
  have hbridge := MatrixTableInterlaceRowBridge.bridge_bound_polynomial
    blocks rows cols
  change MatrixAddressMachine.exactTime rows cols 0 ≤
    4*(rows+cols+0+1)^2 at haddr
  change 2*((blocks*rows)*cols)+2 +
    blocks*SamplerMachineBlockReverse.blockStep (rows*cols) ≤ 7*n^2 at hbridge
  change MatrixAddressMachine.exactTime rows cols 0 +
    (2*((blocks*rows)*cols)+2 +
      blocks*SamplerMachineBlockReverse.blockStep (rows*cols)) ≤ 11*n^2
  nlinarith

end EthInapproximability.CurrentPaper.MatrixTableInterlaceRowWidth
