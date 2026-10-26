import CurrentAdditive.QuarticFrontLift

/-! Generic finite-program size charges for the two new private front phases. -/

namespace Paper2.CurrentAdditive.QuarticFrontSizeTransfer

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable section

set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

theorem loaded_size (P : Fin 3 → List Bool) (t : ℕ) (v : Option Bool)
    (hr : ((advance (CopyAll.prog packetCopies))^[t])
      (⟨some (.inl ⟨0, by omega⟩), none,
        Wrap.widen (Lift.a FS) P⟩ :
        TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, v, loaded P⟩) :
    (BitMachineBankCodec.encode (loaded P)).length ≤
      (BitMachineBankCodec.encode (Wrap.widen (Lift.a FS) P)).length +
        2 * (Lift.a FS + 3) *
          (BitMachineStackGrowth.perStep (CopyAll.prog packetCopies) * t) := by
  have h := Lift.size_run (CopyAll.prog packetCopies)
    (⟨some (.inl ⟨0, by omega⟩), none,
      Wrap.widen (Lift.a FS) P⟩ :
      TM2.Cfg (fun _ : K => Bool) _ _) t
  rw [hr] at h
  exact h

theorem after_raw_size (Δ : ℕ) (γ : ℚ) (P : Fin 3 → List Bool)
    (B : FS → List Bool) (t : ℕ)
    (hstk : (((advance (rawProg Δ γ))^[t])
      (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
        loaded P⟩ : TM2.Cfg (fun _ : K => Bool) _ _)).stk = afterRaw P B) :
    (BitMachineBankCodec.encode (afterRaw P B)).length ≤
      (BitMachineBankCodec.encode (loaded P)).length +
        2 * (Lift.a FS + 3) *
          (BitMachineStackGrowth.perStep (rawProg Δ γ) * t) := by
  have h := Lift.size_run (rawProg Δ γ)
    (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
      loaded P⟩ : TM2.Cfg (fun _ : K => Bool) _ _) t
  rw [hstk] at h
  exact h

#print axioms loaded_size
#print axioms after_raw_size

end
end Paper2.CurrentAdditive.QuarticFrontSizeTransfer
