import CurrentAdditive.V39DeadTaggedCompiler

namespace CurrentAdditive.V39DeadTaggedCompiler

open Turing
open EthInapproximability.CurrentPaper EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization

abbrev Label := BitMachineRawSequence.Label Paper2.TaggedCompiler.Label Unit
abbrev Control := BitMachineRawSequence.Control Paper2.TaggedCompiler.Control Unit

noncomputable def machine := ofFinite (0 : Fin 8) (7 : Fin 8)
  (BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third))
  ((none : Paper2.TaggedCompiler.Control), ()) program

theorem machine_deadTagged (q₁ q₂ s : ℕ) (c : Code) :
    ∃ t ≤ Paper2.TaggedCompiler.polynomialClock q₁ q₂ s (encodeCode c).length + 2,
      machine.run t
        (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label) (Fintype.equivFin Control)
          (⟨some (BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third)),
            ((none : Paper2.TaggedCompiler.Control), ()),
            Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control)) =
        renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label) (Fintype.equivFin Control)
          (⟨none, (none, ()),
            Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
              (encodeCode (deadTaggedCode q₁ q₂ s c))⟩ : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) := by
  obtain ⟨t, ht, hr⟩ := physical_deadTagged q₁ q₂ s c
  refine ⟨t, ?_, ?_⟩
  · simpa only [Paper2.TaggedCompiler.taggedClock_eq_polynomial] using ht
  · exact (ofFinite_run (0 : Fin 8) (7 : Fin 8)
      (BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third))
      ((none : Paper2.TaggedCompiler.Control), ()) program
      (⟨some (BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third)),
        ((none : Paper2.TaggedCompiler.Control), ()),
        Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) t).trans
      (congrArg (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label) (Fintype.equivFin Control)) hr)

theorem deadTagged_serialized_size (q₁ q₂ s : ℕ) (c : Code) :
    (encodeCode (deadTaggedCode q₁ q₂ s c)).length =
      (encodeCode (taggedCode q₁ q₂ s c)).length + 1 := by
  rw [old_serialization, current_serialization]
  simp only [List.length_append]
  rcases header_lengths with ⟨hOld, hNew⟩
  omega

#print axioms machine_deadTagged
#print axioms deadTagged_serialized_size

end CurrentAdditive.V39DeadTaggedCompiler
