import CurrentAdditive.V39DeadTaggedCompiler

namespace CurrentAdditive.V39DeadTaggedFlat

open Turing
open EthInapproximability.CurrentPaper EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev Label := BitMachineRawSequence.Label Paper2.TaggedCompiler.Label Unit
abbrev Control := Paper2.TaggedCompiler.Control

def program (l : Label) : TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  BitMachineInline.stmt id Prod.fst (fun v => (v, ())) none
    (V39DeadTaggedCompiler.program l)

def start : Label := BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third)

theorem physical_tagged (q₁ q₂ s : ℕ) (c : Code) :
    ∃ t ≤ Paper2.TaggedCompiler.taggedClock q₁ q₂ s c + 2,
      ((advance program)^[t])
        (⟨some start, none, Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ :
          TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) =
        ⟨none, none, Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
          (encodeCode (V39DeadTaggedCompiler.deadTaggedCode q₁ q₂ s c))⟩ := by
  obtain ⟨t, ht, hr⟩ := V39DeadTaggedCompiler.physical_deadTagged q₁ q₂ s c
  change ((advance V39DeadTaggedCompiler.program)^[t])
    (⟨some start, ((none : Control), ()), Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ :
      TM2.Cfg (fun _ : Fin 8 => Bool) Label (Control × Unit)) = _ at hr
  have hhalt : (((advance V39DeadTaggedCompiler.program)^[t])
      (⟨some start, ((none : Control), ()), Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) Label (Control × Unit))).l = none := by rw [hr]
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs id Prod.fst (fun v : Control => (v, ()))
    (by intro v; rcases v with ⟨v, u⟩; cases u; rfl) none
    V39DeadTaggedCompiler.program program (fun _ => rfl)
    (⟨some start, ((none : Control), ()), Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ :
      TM2.Cfg (fun _ : Fin 8 => Bool) Label (Control × Unit)) t hhalt
  rw [hr] at hur
  exact ⟨u, by omega, by simpa only [BitMachineInline.cfg, id_eq, Prod.fst] using hur⟩

#print axioms physical_tagged

end CurrentAdditive.V39DeadTaggedFlat
