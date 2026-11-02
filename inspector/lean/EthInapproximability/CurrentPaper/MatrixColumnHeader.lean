import EthInapproximability.CurrentPaper.MatrixColumnDecode
import EthInapproximability.CurrentPaper.MatrixSelectorAlignment

/-!
# Column decoding and the exact source-row header

Source: locked v8 `03-exact-hardness.tex`, the aligned-selector condition,
and Appendix B `thm:paper-materialization`. One physical controller decodes
the literal unary column label, compares the four actual coordinates, and
loads the three actual tail bits into finite control. No alignment bit,
sampled word, active rank, or entry answer is supplied.

The two dimensions are initially unary registers. Binary input decoding and
computing their product are separate operations, not part of this interface.
-/

namespace EthInapproximability.CurrentPaper.MatrixColumnHeader

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev Label := MatrixColumnDecode.Full.Label ⊕ MatrixSelectorAlignment.Label
abbrev Control := MatrixColumnDecode.Full.Control × MatrixSelectorAlignment.Control
abbrev Header := MatrixMaterializationMachine.Control
abbrev Config := TM2.Cfg (fun _ : Fin 15 => Bool) Label Control

def decodeBank : Fin 15 ⊕ Fin 0 ≃ Fin 15 := finSumFinEquiv

private def alignmentPerm : Fin 15 ≃ Fin 15 where
  toFun i := ![13, 12, 11, 10, 2, 5, 1, 9, 14, 0, 3, 4, 6, 7, 8] i
  invFun i := ![9, 6, 4, 10, 11, 5, 12, 13, 14, 7, 3, 2, 1, 0, 8] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def alignmentBank : Fin 9 ⊕ Fin 6 ≃ Fin 15 := finSumFinEquiv.trans alignmentPerm

def decoderControl : MatrixColumnDecode.Full.Control :=
  (((false, false, false, false), (false, false, false, false)), (0, false))

def initialHeader : Header := MatrixMaterializationMachine.header true (fun _ => false)

def program : Label → TM2.Stmt (fun _ : Fin 15 => Bool) Label Control
  | .inl l => renameStmt decodeBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.scan 0)) (MatrixColumnDecode.Full.program l))
  | .inr l => renameStmt alignmentBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (MatrixSelectorAlignment.program l))

def cfg (l : Option Label) (header : Header)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits : List Bool) : Config :=
  ⟨l, (decoderControl, header, none, none),
    ![tail, base, [], d₀, r₀, [], d₁, d₂, d₃, families, q₀, q₁, q₂, q₃, tailBits]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem decode_cfg (l : Option MatrixColumnDecode.Full.Label)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits : List Bool) :
    renameCfg decodeBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (MatrixSelectorAlignment.Label.scan 0)) MatrixSelectorAlignment.initial
        (fun i : Fin 0 => Fin.elim0 i)
        (MatrixColumnDecode.Full.cfg l tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits)) =
      cfg (l.elim (some (.inr (.scan 0))) (fun l => some (.inl l))) initialHeader
        tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits := by
  cases l <;> apply congrArg (fun S =>
    (⟨_, (decoderControl, initialHeader, none, none), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem alignment_cfg (l : Option MatrixSelectorAlignment.Label) (h : Header)
    (α family : Fin 4 → List Bool) (base families tailBits : List Bool) :
    renameCfg alignmentBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none decoderControl
        (![( [] : List Bool), family 2, family 3, family 1, family 0, []] : Fin 6 → List Bool)
        (MatrixSelectorAlignment.cfg l (h, none, none) α [] []
          (![base, families] : Fin 2 → List Bool) tailBits)) =
      cfg (l.map Sum.inr) h [] base (family 2) (family 3) (family 1) (family 0) [] families
        (α 3) (α 2) (α 1) (α 0) tailBits := by
  cases l <;> apply congrArg (fun S => (⟨_, (decoderControl, h, none, none), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

theorem aligned_iff_values {d N₁ : ℕ} (c : ExactConstruction.Columns d N₁) :
    (∀ p, (c.2 p).1.val = (c.2 0).1.val) ↔ ExactConstruction.aligned c := by
  constructor
  · intro h p
    exact Fin.ext (h p)
  · intro h p
    exact congrArg Fin.val (h p)

/-- The final finite-control header is computed from the decoded coordinates
and tail bits. All eight selector fields and both dimension registers remain
available to the subsequent entry controller; the tail-bit stack is consumed. -/
theorem header_run {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) :
    let c := (MatrixMaterialization.columnCode d N₁).symm code
    ∃ t ≤ 64 * code.val + 12 * (d * N₁) + 12 * N₁ + 12 * d + 52,
      run t (cfg (some (.inl (.inl (.inl (.inl .start))))) initialHeader
        (List.replicate code.val true) (List.replicate (d * N₁) true)
        [] [] [] [] [] (List.replicate N₁ true) [] [] [] [] []) =
      cfg none (MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1)
        [] (List.replicate (d * N₁) true)
        (List.replicate (c.2 2).2.val true) (List.replicate (c.2 3).2.val true)
        (List.replicate (c.2 1).2.val true) (List.replicate (c.2 0).2.val true) []
        (List.replicate N₁ true) (List.replicate (c.2 3).1.val true)
        (List.replicate (c.2 2).1.val true) (List.replicate (c.2 1).1.val true)
        (List.replicate (c.2 0).1.val true) [] := by
  dsimp only
  let c := (MatrixMaterialization.columnCode d N₁).symm code
  let α := fun p : Fin 4 => (c.2 p).1.val
  let family := fun p : Fin 4 => List.replicate (c.2 p).2.val true
  let coordinates := fun p : Fin 4 => List.replicate (α p) true
  obtain ⟨kd, hkd, hrd⟩ := MatrixColumnDecode.Full.column_run code
  have hhd : (((advance MatrixColumnDecode.Full.program)^[kd])
      (MatrixColumnDecode.Full.cfg (some (.inl (.inl (.inl .start))))
        (List.replicate code.val true) (List.replicate (d * N₁) true)
        [] [] [] [] [] (List.replicate N₁ true) [] [] [] [] [])).l = none := by
    change (MatrixColumnDecode.Full.run kd _).l = none
    rw [hrd]
    rfl
  obtain ⟨td, htd, hrund⟩ := lift_outputs_renamed decodeBank (Equiv.refl _) (Equiv.refl _)
    MatrixColumnDecode.Full.program program (some (MatrixSelectorAlignment.Label.scan 0))
    (fun _ => rfl) MatrixSelectorAlignment.initial (fun i : Fin 0 => Fin.elim0 i)
    (MatrixColumnDecode.Full.cfg (some (.inl (.inl (.inl .start))))
      (List.replicate code.val true) (List.replicate (d * N₁) true)
      [] [] [] [] [] (List.replicate N₁ true) [] [] [] [] []) kd hhd
  change (((advance MatrixColumnDecode.Full.program)^[kd]) _) = _ at hrd
  rw [hrd, decode_cfg, decode_cfg] at hrund
  have hra := MatrixSelectorAlignment.unary_alignment_run α
    (![List.replicate (d * N₁) true, List.replicate N₁ true] : Fin 2 → List Bool) c.1 []
  have hal : (∀ p, α p = α 0) ↔ ExactConstruction.aligned c := aligned_iff_values c
  simp only [hal] at hra
  have htail : c.1 0 :: c.1 1 :: c.1 2 :: [] = List.ofFn c.1 := rfl
  rw [htail] at hra
  have hha : (((advance MatrixSelectorAlignment.program)^[MatrixSelectorAlignment.time coordinates])
      (MatrixSelectorAlignment.cfg (some (.scan 0)) MatrixSelectorAlignment.initial coordinates [] []
        (![List.replicate (d * N₁) true, List.replicate N₁ true] : Fin 2 → List Bool)
        (List.ofFn c.1))).l = none := by
    change (MatrixSelectorAlignment.run _ _).l = none
    rw [hra]
    rfl
  obtain ⟨ta, hta, hruna⟩ := lift_outputs_renamed alignmentBank
    (Equiv.sumComm _ _) (Equiv.prodComm _ _) MatrixSelectorAlignment.program program none
    (fun _ => rfl) decoderControl
    (![( [] : List Bool), family 2, family 3, family 1, family 0, []] : Fin 6 → List Bool)
    (MatrixSelectorAlignment.cfg (some (.scan 0)) MatrixSelectorAlignment.initial coordinates [] []
      (![List.replicate (d * N₁) true, List.replicate N₁ true] : Fin 2 → List Bool)
      (List.ofFn c.1)) (MatrixSelectorAlignment.time coordinates) hha
  change (((advance MatrixSelectorAlignment.program)^[MatrixSelectorAlignment.time coordinates]) _) = _ at hra
  rw [hra] at hruna
  simp only [MatrixSelectorAlignment.initial] at hruna
  rw [alignment_cfg, alignment_cfg] at hruna
  refine ⟨td + ta, ?_, (run_add hrund ta).trans hruna⟩
  have ht := MatrixSelectorAlignment.unary_time_linear α
  have h₀ := (c.2 0).1.isLt
  have h₁ := (c.2 1).1.isLt
  have h₂ := (c.2 2).1.isLt
  have h₃ := (c.2 3).1.isLt
  change ta ≤ MatrixSelectorAlignment.time (fun p => List.replicate (α p) true) at hta
  dsimp [α] at ht hta
  omega

end EthInapproximability.CurrentPaper.MatrixColumnHeader
