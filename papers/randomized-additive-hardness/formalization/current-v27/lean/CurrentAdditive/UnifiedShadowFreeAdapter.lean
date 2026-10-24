import CurrentAdditive.FieldSearchShadowFreeBank
import CurrentAdditive.UnifiedFieldListMachine

/-! Same fixed unified field program, with the unused shadow modulus empty. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
open CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine

noncomputable def shadowFreeStart (d n : Nat)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) :
    CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Config :=
  BitMachineStackEmbedding.cfg searchSlots (shadowFreeSharedBank d n c.stk)
    Label.search searchEmbed (some .bridge) c

def concreteShadowFreeStart (d n : Nat)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) :
    CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Config :=
  ⟨(match c.l with
    | none => some .bridge
    | some l => some (.search l)),
    searchEmbed c.var, shadowFreeSharedBank d n c.stk⟩

theorem shadowFreeStart_eq_concrete (d n : Nat)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) :
    shadowFreeStart d n c = concreteShadowFreeStart d n c := by
  have hb : BitMachineStackEmbedding.bank searchSlots
      (shadowFreeSharedBank d n c.stk) c.stk = shadowFreeSharedBank d n c.stk := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    rfl
  rcases c with ⟨l, v, S⟩
  cases l <;>
    simp only [shadowFreeStart, concreteShadowFreeStart, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hb]
theorem run_packed_after_shadowFree_search (d tail n ts : Nat)
    (htail : tail < 2 ^ d) (hd : 0 < d)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config)
    (r : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers)
    (S : SearchStack → List Bool)
    (hsearch :
      (((advance CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program)^[ts]) c) =
        ⟨some (.outer .success), r, S⟩)
    (hmod : S 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    ∃ t ≤ ts + 2 + FieldListOutputMachine.timeBound d tail n,
      (run t (shadowFreeStart d n c)).l = none ∧
      (run t (shadowFreeStart d n c)).stk
        (printerSlots FieldListOutputMachine.output) = packedBits d tail n := by
  let P := CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program
  let cSuccess : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config :=
    ⟨some (.outer .success), r, S⟩
  have hs : ((advance P)^[ts + 1]) c = ⟨none, r, S⟩ := by
    rw [Function.iterate_succ_apply', hsearch]
    exact search_success_halts r S
  have hhalt : (((advance P)^[ts + 1]) c).l = none := by rw [hs]
  obtain ⟨u, hu, hphase⟩ := search_phase (shadowFreeSharedBank d n c.stk) c
    (ts + 1) hhalt
  rw [hs] at hphase
  have hcfg :
      BitMachineStackEmbedding.cfg searchSlots (shadowFreeSharedBank d n c.stk)
        Label.search searchEmbed (some .bridge)
        (⟨none, r, S⟩ :
          CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) =
      ⟨some .bridge, searchEmbed r, shadowFreeSharedBank d n S⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg]
    congr 1
    exact shadowFree_search_bank_replace d n c.stk S
  have hbridge :
      run (u + 1) (shadowFreeStart d n c) =
        ⟨some (.printer printerStart),
          printerEmbed FieldListOutputMachine.initial,
          shadowFreeSharedBank d n S⟩ := by
    rw [run_add, show run u (shadowFreeStart d n c) =
      BitMachineStackEmbedding.cfg searchSlots (shadowFreeSharedBank d n c.stk)
        Label.search searchEmbed (some .bridge) (⟨none, r, S⟩ :
          CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) from by
            rw [run_eq_any (inferInstance : DecidableEq Stack)]
            exact hphase]
    rw [hcfg]
    rw [run_eq_any (inferInstance : DecidableEq Stack)]
    simp only [Function.iterate_one, advance]
    rw [show TM2.step program
      ⟨some .bridge, searchEmbed r, shadowFreeSharedBank d n S⟩ =
      some ⟨some (.printer printerStart),
        printerEmbed FieldListOutputMachine.initial,
        shadowFreeSharedBank d n S⟩ from
      bridge_step r FieldListOutputMachine.initial (shadowFreeSharedBank d n S)]
    rfl
  obtain ⟨tp, v, last, htp, hlast, hp⟩ :=
    FieldListOutputMachine.run_packed_field_bits d tail n htail hd
  let printerCfg : FieldListOutputMachine.Config :=
    FieldListOutputMachine.cfg (some printerStart)
      FieldListOutputMachine.initial (FieldListOutputMachine.mapStart d tail n).stk []
  have hp' : (((advance FieldListOutputMachine.program)^[tp]) printerCfg) =
      FieldListOutputMachine.cfg none FieldListOutputMachine.initial
        (Function.update
          (FieldListOutputMachine.mapEnd d tail n v last
            (packedBits d tail n).reverse).stk
          (.inl SeedCallbackMachine.output) [])
        (packedBits d tail n) := by
    rw [← FieldListOutputMachine.run_eq_any
      (inferInstance : DecidableEq FieldListOutputMachine.Stack)]
    exact hp
  have hpHalt : (((advance FieldListOutputMachine.program)^[tp]) printerCfg).l = none := by
    rw [hp']; rfl
  obtain ⟨up, hup, hprinter⟩ := printer_phase (shadowFreeSharedBank d n S)
    printerCfg tp hpHalt
  rw [hp'] at hprinter
  have hstart :
      BitMachineStackEmbedding.cfg printerSlots (shadowFreeSharedBank d n S)
        Label.printer printerEmbed none printerCfg =
      ⟨some (.printer printerStart),
        printerEmbed FieldListOutputMachine.initial,
        shadowFreeSharedBank d n S⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, printerCfg, FieldListOutputMachine.cfg]
    congr 1
    exact shadowFree_printer_bank_embedding d n tail htail S hmod
  have hfinal :
      run (u + 1 + up) (shadowFreeStart d n c) =
      BitMachineStackEmbedding.cfg printerSlots (shadowFreeSharedBank d n S)
        Label.printer printerEmbed none
        (FieldListOutputMachine.cfg none FieldListOutputMachine.initial
          (Function.update
            (FieldListOutputMachine.mapEnd d tail n v last
              (packedBits d tail n).reverse).stk
            (.inl SeedCallbackMachine.output) [])
          (packedBits d tail n)) := by
    rw [run_add, hbridge, ← hstart]
    rw [run_eq_any (inferInstance : DecidableEq Stack)]
    exact hprinter
  refine ⟨u + 1 + up, ?_, ?_, ?_⟩
  · omega
  · rw [hfinal]
    rfl
  · rw [hfinal]
    exact BitMachineStackEmbedding.bank_at printerSlots
      (shadowFreeSharedBank d n S) _ FieldListOutputMachine.output

#print axioms run_packed_after_shadowFree_search

end CurrentAdditive.FieldSearchCompletion
