import CurrentAdditive.V40MidpointRequest

noncomputable section
namespace CurrentAdditive.V40MidpointRequest

open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding
open EncodedCommunication BitMachineStackEmbedding MinimumRatioContext

def HighClean (S : Bank) : Prop := ∀ i : Stack, 32 ≤ i.val → S i = []

theorem high_ne_low (i : Stack) (hi : 32 ≤ i.val) (j : Fin 32) : i ≠ low j := by
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  change i.val = j.val at hv
  omega

theorem clean_update (S : Bank) (h : HighClean S) (j : Fin 32) (word : List Bool) :
    HighClean (Function.update S (low j) word) := by
  intro i hi
  rw [Function.update_of_ne (high_ne_low i hi j)]
  exact h i hi

theorem outputs (S : Bank) (B k : ℕ) (word : List Bool)
    (hB : S (low 0) = List.replicate B true)
    (hk : S (low 1) = List.replicate k true)
    (hword : S (low 5) = word)
    (h2 : S (low 2) = []) (h3 : S (low 3) = []) (h4 : S (low 4) = [])
    (h6 : S (low 6) = []) (h7 : S (low 7) = []) (hblank : HighClean S) :
    ∃ t ≤ clock B k word,
      ((advance program)^[t])
        (⟨some start, control, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control, final S B k word⟩ := by
  let num := 2*B+k
  let Sn := Function.update S (low 2) (List.replicate num true)
  let Sf := Function.update Sn (low 3) (natField num)
  let Sm := Function.update Sf (low 6) (AFront.Projection.matrixPart word)
  let So := Function.update Sm (low 7) (AFront.Projection.matrixPart word)
  have hnclean : HighClean Sn := clean_update S hblank _ _
  have hfclean : HighClean Sf := clean_update Sn hnclean _ _
  obtain ⟨a, ha, hrA⟩ := copy_numerator S B k hB hk h2 h4
  obtain ⟨b, hb, hrB⟩ := MachineInvokeFull.invoke_run_uniform fieldSlots Sn
    (List.replicate num true) (natField num)
    ((UnaryBinaryEncoding.coefficient+10)*(num+1)^2)
    (by simp [Sn, fieldSlots, slots])
    (by simpa [Sf, Sn, fieldSlots, slots, Function.update] using h3)
    (by simpa [Sn, fieldSlots, slots, Function.update] using h4)
    (by intro i; exact hnclean _ (by dsimp [fieldSlots, slots]; omega))
    (by simpa only [List.length_replicate] using
      SourceFieldWriter.unary_field_outputs (List.replicate num true))
  obtain ⟨ab, hab, hrAB⟩ := BitMachineRawSequence.runs pBBK fieldProgram sBBK
    (MachineInvokeFull.start fieldSlots) cBBK cBBK
    (MachineInvokeFull.control fieldSlots) (MachineInvokeFull.control fieldSlots)
    S Sn Sf a b hrA hrB
  obtain ⟨c, hc, hrC⟩ := MachineInvokeFull.invoke_run_uniform matrixSlots Sf word
    (AFront.Projection.matrixPart word) (3*(word.length+1))
    (by simpa [Sf, Sn, matrixSlots, slots, Function.update] using hword)
    (by simpa [Sf, Sn, matrixSlots, slots, Function.update] using h6)
    (by simpa [Sf, Sn, matrixSlots, slots, Function.update] using h4)
    (by intro i; exact hfclean _ (by dsimp [matrixSlots, slots]; omega))
    (AFront.Projection.matrixMachine_outputs word)
  obtain ⟨abc, habc, hrABC⟩ := BitMachineRawSequence.runs pField matrixProgram sField
    (MachineInvokeFull.start matrixSlots) cField cField
    (MachineInvokeFull.control matrixSlots) (MachineInvokeFull.control matrixSlots)
    S Sf Sm ab c (by simpa only [pField, sField, cField] using hrAB) hrC
  have hd := MatrixStage4ScalarPreparationOps.copy_run outputSlots Sm
    (by simpa [Sm, Sf, Sn, outputSlots, copySlots, Function.update] using h4)
  change ((advance copyMatrix)^[2*(Sm (low 6)).length+2])
    (⟨some .scan, none, Sm⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
    ⟨none, none, Function.update Sm (low 7) (Sm (low 6) ++ Sm (low 7))⟩ at hd
  have hd' : ((advance copyMatrix)^[2*(AFront.Projection.matrixPart word).length+2])
      (⟨some .scan, none, Sm⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, none, So⟩ := by
    simpa [Sm, Sf, Sn, So, Function.update, h7] using hd
  obtain ⟨abcd, habcd, hrABCD⟩ := BitMachineRawSequence.runs pMatrix copyMatrix sMatrix .scan
    cMatrix cMatrix (none : Option Bool) none S Sm So abc
    (2*(AFront.Projection.matrixPart word).length+2)
    (by simpa only [pMatrix, sMatrix, cMatrix] using hrABC) hd'
  have he := MatrixStage4ScalarPreparationOps.copy_run headerSlots So
    (by simpa [So, Sm, Sf, Sn, headerSlots, copySlots, Function.update] using h4)
  change ((advance copyHeader)^[2*(So (low 3)).length+2])
    (⟨some .scan, none, So⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
    ⟨none, none, Function.update So (low 7) (So (low 3) ++ So (low 7))⟩ at he
  have he' : ((advance copyHeader)^[2*(natField num).length+2])
      (⟨some .scan, none, So⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, final S B k word⟩ := by
    simpa [So, Sm, Sf, Sn, num, final, Function.update] using he
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs pOutput copyHeader sOutput .scan
    cOutput cOutput (none : Option Bool) none S So (final S B k word)
    abcd (2*(natField num).length+2)
    (by simpa only [pOutput, sOutput, cOutput] using hrABCD) he'
  refine ⟨t, ?_, ?_⟩
  · change b ≤ fieldClock B k at hb
    change c ≤ matrixClock word at hc
    unfold clock
    dsimp only [num] at *
    omega
  · simpa only [program, start, control] using hr

theorem final_request (S : Bank) (B k : ℕ) (i : Instance) :
    final S B k (encodeInstance i) (low 7) =
      natField (2*B+k) ++ AModel.matrixWord i.rows i.cols i.table := by
  simp only [final, Function.update_self, AFront.Projection.matrixPart_encodeInstance]
  rfl

theorem final_preserves (S : Bank) (B k : ℕ) (word : List Bool) (j : Fin 32)
    (hj2 : j ≠ 2) (hj3 : j ≠ 3) (hj6 : j ≠ 6) (hj7 : j ≠ 7) :
    final S B k word (low j) = S (low j) := by
  simp [final, Function.update, hj2, hj3, hj6, hj7]

#print axioms outputs
#print axioms final_request

end CurrentAdditive.V40MidpointRequest
