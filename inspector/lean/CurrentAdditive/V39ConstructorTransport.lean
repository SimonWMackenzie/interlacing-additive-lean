import CurrentAdditive.V39CurrentCodeConstructor

/-! The fixed current constructor embeds in arbitrary ambient banks while
preserving every bank outside its fixed stack injection. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39ConstructorTransport

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V39CurrentCodeConstructor

variable {K : Type} [DecidableEq K]

theorem physical_from_bank (ι : Stack ↪ K) (S : K → List Bool)
    (n p q₁ q₂ s w Q k m : Nat) (hs : 3 ≤ s)
    (hS : ∀ j, S (ι j) = V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m j) :
    ∃ t ≤ V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m,
      ((advance (fun l => stackStmt ι (V39DeadSampleJoin.program l)))^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : K => Bool) Label Control) =
        ⟨none,control,bank ι S (finalBank n p q₁ q₂ s w Q k m)⟩ := by
  obtain ⟨t,ht,hr⟩ := physical_construct n p q₁ q₂ s w Q k m hs
  have he := BitMachineStackRun.run ι S V39DeadSampleJoin.program
    (⟨some start,control,V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) t
  have hbank : bank ι S (V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m) = S :=
    bank_eq_self ι S _ (fun j => (hS j).symm)
  rw [hr] at he
  exact ⟨t,ht,by simpa only [stackCfg,hbank] using he⟩

theorem foreign_retained (ι : Stack ↪ K) (S : K → List Bool)
    (n p q₁ q₂ s w Q k m : Nat) (i : K) (hi : ¬ ∃ j, ι j = i) :
    bank ι S (finalBank n p q₁ q₂ s w Q k m) i = S i :=
  bank_outside ι S _ i hi

#print axioms physical_from_bank
#print axioms foreign_retained

end CurrentAdditive.V39ConstructorTransport
