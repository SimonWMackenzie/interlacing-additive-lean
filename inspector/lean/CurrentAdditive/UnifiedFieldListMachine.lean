import CurrentAdditive.FieldSearchPrinterHandoff
import CurrentAdditive.TrialSearchCombinedMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! One finite TM2 program with a physical trial-search phase, one
administrative handoff transition, and the checked ordered field-list
printer. Search stack 0 is the printer's modulus bank. The global search
totality theorem is supplied separately by the search worker. -/

namespace CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

namespace Search
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
end Search
namespace Printer
open CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine
end Printer

private instance finiteDecEq (m : Nat) : DecidableEq (Fin m) := instDecidableEqFin m

inductive Label where
  | search (l : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Label)
  | bridge
  | printer (l : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Label)
  deriving Fintype

abbrev Control :=
  CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers ×
    CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def dummySearch : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers :=
  ⟨none, (false, none, none), (false, none), (false, false, none)⟩

def printerStart : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Label :=
  .inl (.inl (.inr (.inl SamplerMachineFactorSplit.Label.scanU)))

def searchEmbed (r : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers) :
    Control := (r, CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.initial)
def printerEmbed (v : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Control) :
    Control := (dummySearch, v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .search l => BitMachineStackEmbedding.stmt searchSlots Label.search
      searchEmbed Prod.fst (some .bridge)
      (CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program l)
  | .bridge => load (fun _ => printerEmbed
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.initial)
      (goto (fun _ => .printer printerStart))
  | .printer l => BitMachineStackEmbedding.stmt printerSlots Label.printer
      printerEmbed Prod.snd none
      (CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.program l)

def stackDecEq : DecidableEq Stack :=
  @instDecidableEqSum SearchStack PrinterStack
    (inferInstanceAs (DecidableEq SearchStack))
    FieldListOutputMachine.stackDecEq

def run (t : Nat) (q : Config) : Config :=
  ((@advance Stack Label Control stackDecEq program)^[t]) q

theorem run_eq_any (D : DecidableEq Stack) (t : Nat) (q : Config) :
    run t q = ((@advance Stack Label Control D program)^[t]) q := by
  have h : stackDecEq = D := Subsingleton.elim _ _
  unfold run
  rw [h]

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

theorem search_statement (l : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Label) :
    program (.search l) = BitMachineStackEmbedding.stmt searchSlots Label.search
      searchEmbed Prod.fst (some .bridge)
      (CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program l) := rfl

theorem printer_statement (l : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Label) :
    program (.printer l) = BitMachineStackEmbedding.stmt printerSlots Label.printer
      printerEmbed Prod.snd none
      (CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.program l) := rfl

/-- Any physically checked halting search run is inlined into this same
program, preserving every printer-only stack and ending at the one-step
handoff label. The conclusion is a literal TM2 run, not a cost oracle. -/
theorem search_phase (foreign : Stack → List Bool)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config)
    (t : Nat)
    (hhalt : (((advance CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program)^[t]) c).l = none) :
    ∃ u ≤ t,
      ((advance program)^[u])
        (BitMachineStackEmbedding.cfg searchSlots foreign Label.search
          searchEmbed (some .bridge) c) =
        BitMachineStackEmbedding.cfg searchSlots foreign Label.search
          searchEmbed (some .bridge)
          (((advance CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program)^[t]) c) := by
  exact BitMachineStackEmbedding.outputs searchSlots foreign Label.search
    searchEmbed Prod.fst (by intro x; rfl) (some .bridge)
    CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program program
    search_statement c t hhalt

theorem bridge_step (r : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers)
    (v : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Control)
    (S : Stack → List Bool) :
    TM2.step program ⟨some .bridge, (r, v), S⟩ =
      some ⟨some (.printer printerStart),
        printerEmbed CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.initial,
        S⟩ := by
  rfl

theorem search_success_halts
    (r : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Registers)
    (S : Fin 12 → List Bool) :
    advance CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program
      ⟨some (.outer .success), r, S⟩ = ⟨none, r, S⟩ := by
  rfl

/-- The ordered packed-field printer runs within the same finite program,
reading the successful search's stack 0 as its modulus bank. -/
theorem printer_phase (foreign : Stack → List Bool)
    (c : CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.Config)
    (t : Nat)
    (hhalt : (((advance CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.program)^[t]) c).l = none) :
    ∃ u ≤ t,
      ((advance program)^[u])
        (BitMachineStackEmbedding.cfg printerSlots foreign Label.printer
          printerEmbed none c) =
        BitMachineStackEmbedding.cfg printerSlots foreign Label.printer
          printerEmbed none
          (((advance CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.program)^[t]) c) := by
  exact BitMachineStackEmbedding.outputs printerSlots foreign Label.printer
    printerEmbed Prod.snd (by intro x; rfl) none
    CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.program program
    printer_statement c t hhalt

noncomputable def searchStart (d tail n : Nat)
    (c : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) : Config :=
  BitMachineStackEmbedding.cfg searchSlots (sharedBank d tail n c.stk)
    Label.search searchEmbed (some .bridge) c

def packedBits (d tail n : Nat) : List Bool :=
  CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
    (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n

/-- A checked successful search and the checked ordered printer execute as
one literal finite TM2 program. The search clock remains an explicit premise
until the global first-passing controller theorem is supplied. -/
theorem run_packed_after_search (d tail n ts : Nat)
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
      (run t (searchStart d tail n c)).l = none ∧
      (run t (searchStart d tail n c)).stk
        (printerSlots FieldListOutputMachine.output) = packedBits d tail n := by
  let P := CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program
  let cSuccess : CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config :=
    ⟨some (.outer .success), r, S⟩
  have hs : ((advance P)^[ts + 1]) c = ⟨none, r, S⟩ := by
    rw [Function.iterate_succ_apply', hsearch]
    exact search_success_halts r S
  have hhalt : (((advance P)^[ts + 1]) c).l = none := by rw [hs]
  obtain ⟨u, hu, hphase⟩ := search_phase (sharedBank d tail n c.stk) c
    (ts + 1) hhalt
  rw [hs] at hphase
  have hcfg :
      BitMachineStackEmbedding.cfg searchSlots (sharedBank d tail n c.stk)
        Label.search searchEmbed (some .bridge)
        (⟨none, r, S⟩ :
          CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) =
      ⟨some .bridge, searchEmbed r, sharedBank d tail n S⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg]
    congr 1
    exact search_bank_replace d tail n c.stk S
  have hbridge :
      run (u + 1) (searchStart d tail n c) =
        ⟨some (.printer printerStart),
          printerEmbed FieldListOutputMachine.initial,
          sharedBank d tail n S⟩ := by
    rw [run_add, show run u (searchStart d tail n c) =
      BitMachineStackEmbedding.cfg searchSlots (sharedBank d tail n c.stk)
        Label.search searchEmbed (some .bridge) (⟨none, r, S⟩ :
          CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.Config) from by
            rw [run_eq_any (inferInstance : DecidableEq Stack)]
            exact hphase]
    rw [hcfg]
    rw [run_eq_any (inferInstance : DecidableEq Stack)]
    simp only [Function.iterate_one, advance]
    rw [show TM2.step program
      ⟨some .bridge, searchEmbed r, sharedBank d tail n S⟩ =
      some ⟨some (.printer printerStart),
        printerEmbed FieldListOutputMachine.initial,
        sharedBank d tail n S⟩ from
      bridge_step r FieldListOutputMachine.initial (sharedBank d tail n S)]
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
  obtain ⟨up, hup, hprinter⟩ := printer_phase (sharedBank d tail n S)
    printerCfg tp hpHalt
  rw [hp'] at hprinter
  have hstart :
      BitMachineStackEmbedding.cfg printerSlots (sharedBank d tail n S)
        Label.printer printerEmbed none printerCfg =
      ⟨some (.printer printerStart),
        printerEmbed FieldListOutputMachine.initial,
        sharedBank d tail n S⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, printerCfg, FieldListOutputMachine.cfg]
    congr 1
    exact printer_bank_embedding d tail n htail S hmod
  have hfinal :
      run (u + 1 + up) (searchStart d tail n c) =
      BitMachineStackEmbedding.cfg printerSlots (sharedBank d tail n S)
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
      (sharedBank d tail n S) _ FieldListOutputMachine.output

end CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine
