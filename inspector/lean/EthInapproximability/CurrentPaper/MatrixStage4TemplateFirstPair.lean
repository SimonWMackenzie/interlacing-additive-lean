import EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstConnector

/-!
# Preserved family-pair address through first-symbol production

The row-field suffix needs the computed `ℓ*q+α` after the first-symbol
controller halts. This owner strengthens the previous existential terminal
theorem with that physically preserved bank, without editing the frozen
controller or supplying the selected address as a new input.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstPair

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

def fieldPairSlot : MatrixStage4TemplateFieldDecode.Stack :=
  .inl (.inl (.inl (.inr 4)))

def finalPairSlot : MatrixStage4TemplateFirstConnector.Stack :=
  .inl fieldPairSlot

theorem field_pair_preserved {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    (MatrixStage4TemplateFieldDecode.output code p ell f).stk fieldPairSlot =
      List.replicate (ell.val*q+
        MatrixStage4TemplateEntryMachine.selectedAlpha code p) true := by
  unfold MatrixStage4TemplateFieldDecode.output
  dsimp only [MatrixStage4TemplateFieldDecode.cfg]
  rw [bank_outside MatrixStage4TemplateFieldDecode.decodeSlots _ _ fieldPairSlot
    (by decide)]
  unfold MatrixStage4TemplateFieldDecode.priorBank
  change (MatrixStage4TemplateFieldGather.output code p ell f).stk
    (.inl (.inl (.inr 4))) = _
  unfold MatrixStage4TemplateFieldGather.output
  dsimp only [MatrixStage4TemplateFieldGather.cfg]
  rw [bank_outside MatrixStage4TemplateFieldGather.gatherSlots _ _
    (.inl (.inl (.inr 4))) (by decide)]
  unfold MatrixStage4TemplateFieldGather.priorBank
  change (MatrixStage4TemplateFieldStart.fieldOutput code p ell m).stk
    (.inl (.inr 4)) = _
  unfold MatrixStage4TemplateFieldStart.fieldOutput
  dsimp only [MatrixStage4TemplateFieldStart.cfg]
  simpa only [MatrixStage4TemplateFieldStart.fieldSlots,
    MatrixAddressMachine.cfg] using
    (bank_at MatrixStage4TemplateFieldStart.fieldSlots
      (MatrixStage4TemplateFieldStart.priorBank
        (MatrixStage4TemplateFieldStart.pairOutput code p ell) m)
      (MatrixAddressMachine.cfg none false
        (List.replicate
          (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)
          true)
        (List.replicate m true) [] [] []
        (List.replicate
          ((ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)*m)
          true)).stk 0)

theorem actual_first_symbol_pair {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let γ := (((rawColumnCode a s q cy).symm code).2 p).2
    let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
    ∃ t ≤ MatrixStage4TemplateFirstConnector.actualBound family code p ell,
      (MatrixStage4TemplateFirstConnector.run t
        (MatrixStage4TemplateFirstConnector.actualSource family code p ell)).l = none ∧
      (MatrixStage4TemplateFirstConnector.run t
        (MatrixStage4TemplateFirstConnector.actualSource family code p ell)).stk
        (.inr 23) = List.replicate (γ (firstCoordinate a s j)).val true ∧
      (MatrixStage4TemplateFirstConnector.run t
        (MatrixStage4TemplateFirstConnector.actualSource family code p ell)).stk
        finalPairSlot =
        List.replicate (ell.val*q+
          MatrixStage4TemplateEntryMachine.selectedAlpha code p) true := by
  dsimp
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  let pos := MatrixStage4FirstDigitMachine.firstPosition (s := s) j
  let n := (firstWordCode a s cy γ).val
  let outer := cy^(firstLength a s)
  let exponent := firstLength a s-1
  let f := MatrixStage4FamilyData.familyFirst family
  let cDigit := MatrixStage4FirstDigitMachine.source n outer cy exponent pos
  obtain ⟨tp,htp,hp⟩ :=
    MatrixStage4TemplateFieldDecode.field_decode_run code p ell f
  have hh : (MatrixStage4TemplateFieldDecode.run tp
      (MatrixStage4TemplateFieldDecode.source code p ell f)).l = none := by
    rw [hp]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4TemplateFirstConnector.prior_phase
    MatrixStage4TemplateFieldDecode.start
    MatrixStage4TemplateFieldDecode.initial
    (MatrixStage4TemplateFieldDecode.source code p ell f).stk
    outer cy exponent tp hh
  have h₁' : MatrixStage4TemplateFirstConnector.run t₁
      (MatrixStage4TemplateFirstConnector.actualSource family code p ell) =
      MatrixStage4TemplateFirstConnector.cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateFieldDecode.output code p ell f).var,
          MatrixStage4FirstDigitMachine.initial)
        (MatrixStage4TemplateFirstConnector.priorBank
          (MatrixStage4TemplateFieldDecode.output code p ell f)
          outer cy exponent) := by
    simp only [MatrixStage4TemplateFieldDecode.source,
      MatrixStage4TemplateFieldDecode.cfg] at hp h₁
    rw [hp] at h₁
    simpa only [MatrixStage4TemplateFirstConnector.actualSource,
      MatrixStage4TemplateFirstConnector.start,
      MatrixStage4TemplateFirstConnector.initial,
      outer, exponent, f] using h₁
  let S := MatrixStage4TemplateFirstConnector.priorBank
    (MatrixStage4TemplateFieldDecode.output code p ell f)
    outer cy exponent
  have hj : (MatrixStage4TemplateFieldDecode.output code p ell f).stk
      (.inr 0) = List.replicate pos.val true := by
    simpa only [f, pos, MatrixStage4FirstDigitMachine.firstPosition_val] using
      MatrixStage4TemplateFirstConnector.decoded_first_value family code p ell
  have hw : (MatrixStage4TemplateFieldDecode.output code p ell f).stk
      MatrixStage4TemplateFirstConnector.wordSlot = List.replicate n true := by
    simpa only [f, n, γ] using
      MatrixStage4TemplateFirstConnector.decoded_word_preserved code p ell f
  have hinput : ∀ k : MatrixStage4FirstDigitMachine.Stack,
      S (MatrixStage4TemplateFirstConnector.digitSlots k) = cDigit.stk k := by
    intro k
    simpa only [S, cDigit] using
      MatrixStage4TemplateFirstConnector.digit_input_matches
        (MatrixStage4TemplateFieldDecode.output code p ell f).stk
        n outer cy exponent pos hj hw k
  obtain ⟨td,htd,hd,hsymbol⟩ :=
    MatrixStage4FirstDigitMachine.first_word_digit_output γ j
  have hd' : (MatrixStage4FirstDigitMachine.run td cDigit).l = none := by
    simpa only [cDigit, n, outer, exponent, pos] using hd
  have hsymbol' : (MatrixStage4FirstDigitMachine.run td cDigit).stk
      (.inr 14) = List.replicate (γ (firstCoordinate a s j)).val true := by
    simpa only [cDigit, n, outer, exponent, pos] using hsymbol
  have hstart : cDigit.l = some MatrixStage4FirstDigitMachine.start := rfl
  have hvar : cDigit.var = MatrixStage4FirstDigitMachine.initial := rfl
  obtain ⟨t₂,ht₂,h₂⟩ := MatrixStage4TemplateFirstConnector.digit_phase
    S cDigit td hstart hinput hd'
  have h12 := MatrixStage4TemplateFirstConnector.run_add h₁' 1
  rw [MatrixStage4TemplateFirstConnector.bridge] at h12
  have h123 := MatrixStage4TemplateFirstConnector.run_add h12 t₂
  change MatrixStage4TemplateFirstConnector.run (t₁+1+t₂)
      (MatrixStage4TemplateFirstConnector.actualSource family code p ell) =
    MatrixStage4TemplateFirstConnector.run t₂
      (MatrixStage4TemplateFirstConnector.cfg
        (some (.inr (.inr MatrixStage4FirstDigitMachine.start)))
        (MatrixStage4TemplateFieldDecode.initial,
          MatrixStage4FirstDigitMachine.initial) S) at h123
  rw [← hvar, h₂] at h123
  refine ⟨t₁+1+t₂, ?_, ?_, ?_, ?_⟩
  · dsimp [MatrixStage4TemplateFirstConnector.actualBound,
      f, γ, j, pos, n, outer, exponent] at htp htd ⊢
    omega
  · rw [h123]
    rfl
  · rw [h123]
    have hout := bank_at MatrixStage4TemplateFirstConnector.digitSlots S
      (MatrixStage4FirstDigitMachine.run td cDigit).stk (.inr 14)
    simpa only [MatrixStage4TemplateFirstConnector.cfg,
      MatrixStage4TemplateFirstConnector.digitSlots, hsymbol'] using hout
  · rw [h123]
    simp only [MatrixStage4TemplateFirstConnector.cfg]
    have hout :
        bank MatrixStage4TemplateFirstConnector.digitSlots S
          (MatrixStage4FirstDigitMachine.run td cDigit).stk finalPairSlot =
        S finalPairSlot :=
      bank_outside MatrixStage4TemplateFirstConnector.digitSlots S _
        finalPairSlot (by decide)
    rw [hout]
    simpa only [S, finalPairSlot,
      MatrixStage4TemplateFirstConnector.priorBank,
      MatrixStage4TemplateFirstConnector.cfg, f] using
      field_pair_preserved code p ell f

end EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstPair
