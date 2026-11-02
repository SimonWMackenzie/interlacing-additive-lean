import CurrentAdditive.V39PhysicalShapeSample

set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39PhysicalShapeSample
noncomputable section
open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V39RecursiveGenerator V38OneStep

variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

/-- The complete physical auxiliary-shape and current-sample controller can
share its public count cells with a preceding raw-input parameter compiler. -/
theorem physical_from_bank {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (S : K → List Bool)
    (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool)
    (hS : ∀ j, S (ι j)=initial n p q₁ q₂ s w Q k m
      (RoundedCodeLoop.tapeWord (V39PhysicalSample.blockLength n p q₂ s w Q N) N bits ++ suffix)
      (V39PhysicalSample.blockLength n p q₂ s w Q N) j) :
    ∃ t ≤ clock n p q₁ q₂ s w Q k m (V39PhysicalSample.blockLength n p q₂ s w Q N) N,
      ((advance (fun l => stackStmt ι (program l)))^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : K => Bool) Label _) =
        ⟨none,control,bank ι S (final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix)⟩ := by
  obtain ⟨t,ht,hr⟩ := physical_shape_and_sample n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix
  have he := BitMachineStackRun.run ι S program
    (⟨some start,control,initial n p q₁ q₂ s w Q k m
      (RoundedCodeLoop.tapeWord (V39PhysicalSample.blockLength n p q₂ s w Q N) N bits ++ suffix)
      (V39PhysicalSample.blockLength n p q₂ s w Q N)⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label _) t
  rw [hr] at he
  have hi := bank_eq_self ι S _ (fun j => (hS j).symm)
  exact ⟨t,ht,by simpa only [stackCfg,hi] using he⟩

theorem physical_output (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) {K : Type*} [DecidableEq K] (ι : Stack ↪ K) (S : K → List Bool) :
    bank ι S (final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix)
      (ι (sampleSlots (.inl V39PhysicalSample.source))) =
      V39GeneratorCode.sampleWord n p q₁ q₂ s w Q k m
        (V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits) := by
  rw [bank_at,final_sample_output]

theorem output_event_error_200 (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (suffix : List Bool) (E : List Bool → Prop) :
    |(RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N).prob
      (fun bits => E (final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix
        (sampleSlots (.inl V39PhysicalSample.source)))) -
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun z => E (V39GeneratorCode.sampleWord n p q₁ q₂ s w Q k m z))| ≤ (1:ℝ)/200 := by
  simp_rw [final_sample_output]
  exact V39PhysicalSample.budget_labels_event_error_200 n p q₁ q₂ s w Q hs hq₁ k m N hN
    (fun z => E (V39GeneratorCode.sampleWord n p q₁ q₂ s w Q k m z))

#print axioms physical_from_bank
#print axioms output_event_error_200
end
end CurrentAdditive.V39PhysicalShapeSample
