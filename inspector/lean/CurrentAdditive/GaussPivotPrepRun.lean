import CurrentAdditive.GaussPivotPrepController32

namespace CurrentAdditive.GaussPivotPrepRun

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
noncomputable abbrev M := GaussPivotCount32.M
variable {m k : Nat} (s : GaussControlTrace.State m k)

theorem parser_start_bank :
    GaussPivotParser32.frame (GaussPivotPrepBank.extracted s)
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) (GaussPivotPrepBank.packet s) [] [] ) =
    ⟨some (.inl (.scan 0)), none, GaussPivotPrepBank.extracted s⟩ := by
  simp only [GaussPivotParser32.frame,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro q
  cases q with
  | inl q =>
      fin_cases q <;>
        simp [BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents, GaussPivotParser32.locate,
          GaussPivotPrepBank.extracted_other s]
  | inr q =>
      fin_cases q
      · simpa [BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents, GaussPivotParser32.locate]
          using (GaussPivotPrepBank.extracted_30 s).symm
      · simpa [BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents, GaussPivotParser32.locate]
          using (GaussPivotPrepBank.extracted_31 s).symm
      · have h := GaussPivotPrepBank.extracted_other s 29 (by decide)
        simpa [BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents, GaussPivotParser32.locate]
          using h.symm

theorem parser_temp_empty : (GaussPivotPrepBank.parsed s).stk 29 = [] := by
  change BitMachineStackEmbedding.bank GaussPivotParser32.locate (GaussPivotPrepBank.extracted s)
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] []).stk
    (GaussPivotParser32.locate (.inr 2)) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem count_local_halt :
    ∃ t ≤ GaussStateRowCount.polynomialClock (GaussPivotPrepBank.packet s).length + 1,
      GaussPivotCount32.run t
        ⟨some (.inl M.start), M.initial, GaussPivotPrepBank.copied s⟩ =
        ⟨none, (GaussPivotPrepBank.countOut s).var, GaussPivotPrepBank.counted s⟩ := by
  obtain ⟨t, ht, hr⟩ := GaussPivotCount32.count_phase s
    (GaussPivotPrepBank.copied s) (fun j => GaussPivotInputCopy32.count_ready (GaussPivotPrepBank.packet s) j)
  refine ⟨t + 1, by simpa [GaussPivotPrepBank.packet] using Nat.add_le_add_right ht 1, ?_⟩
  rw [GaussPivotCount32.run, Function.iterate_succ_apply', ← GaussPivotCount32.run]
  rw [hr]
  simp [GaussPivotCount32.program, advance, Turing.TM2.step,
    Turing.TM2.stepAux, GaussPivotPrepBank.countOut, GaussPivotPrepBank.counted, GaussPivotPrepBank.packet]

theorem extract_local_halt :
    ∃ t ≤ (2 * (GaussPivotPrepBank.counted s GaussPivotCountExtract32.source).length + 3) +
      (∑ j : Fin M.stackCount,
        ((GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s))
          (GaussPivotCount32.slot j)).length) + M.stackCount + 2,
      GaussPivotCountExtract32.run t
        ⟨some (.copy .scan), ((), none), GaussPivotPrepBank.counted s⟩ =
        ⟨none, ((), none), GaussPivotPrepBank.extracted s⟩ := by
  obtain ⟨t, ht, hr⟩ := GaussPivotCountExtract32.extract_and_cleanup
    (GaussPivotPrepBank.counted s) (GaussPivotPrepBank.counted_31_empty s)
  refine ⟨t + 1, by
    simpa only [M, GaussPivotCountExtract32.M] using
      (Nat.add_le_add_right ht 1), ?_⟩
  rw [GaussPivotCountExtract32.run, Function.iterate_succ_apply',
    ← GaussPivotCountExtract32.run, hr]
  simp [GaussPivotCountExtract32.program, advance, Turing.TM2.step,
    Turing.TM2.stepAux, GaussPivotPrepBank.extracted]

theorem parser_local_halt :
    ∃ t ≤ 9 * ((GaussPivotPrepBank.packet s).length + 1) + 1,
      GaussPivotParser32.run t
        ⟨some (.inl (.scan 0)), none, GaussPivotPrepBank.extracted s⟩ =
        ⟨none, none, (GaussPivotPrepBank.parsed s).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := GaussPivotParser32.parse_state s (GaussPivotPrepBank.extracted s)
  have hs := parser_start_bank s
  unfold GaussPivotPrepBank.packet at hs
  rw [hs] at hr
  refine ⟨t + 1, by simpa [GaussPivotPrepBank.packet] using Nat.add_le_add_right ht 1, ?_⟩
  rw [GaussPivotParser32.run, Function.iterate_succ_apply',
    ← GaussPivotParser32.run, hr]
  have hf : GaussPivotPrepBank.parsed s =
      ⟨some (.inr ()), some true, (GaussPivotPrepBank.parsed s).stk⟩ := rfl
  rw [← GaussPivotPrepBank.parsed, hf]
  simp [GaussPivotParser32.program, advance, Turing.TM2.step,
    Turing.TM2.stepAux]

theorem fields_local_halt :
    ∃ t ≤ GaussPivotFields32.copyClock (GaussPivotPrepBank.parsed s).stk +
      (∑ i : Fin 5,
        ((GaussPivotFields32.after3 (GaussPivotPrepBank.parsed s).stk)
          (GaussPivotFields32.clearBank i)).length) + 7,
      GaussPivotFields32.run t
        ⟨some (.copy 0 .scan), ((), none), (GaussPivotPrepBank.parsed s).stk⟩ =
        ⟨none, ((), none), GaussPivotPrepBank.prepared s⟩ := by
  obtain ⟨t, ht, hr⟩ := GaussPivotFields32.fields_and_cleanup
    (GaussPivotPrepBank.parsed s).stk (parser_temp_empty s)
  refine ⟨t + 1, by omega, ?_⟩
  rw [GaussPivotFields32.run, Function.iterate_succ_apply',
    ← GaussPivotFields32.run, hr]
  simp [GaussPivotFields32.program, advance, Turing.TM2.step,
    Turing.TM2.stepAux, GaussPivotPrepBank.prepared]

theorem copy_global :
    ∃ t ≤ 2 * (GaussPivotPrepBank.packet s).length + 3,
      GaussPivotPrepController32.run t
        (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
        ⟨some .toCount, .copy ((), none), GaussPivotPrepBank.copied s⟩ := by
  let word := GaussPivotPrepBank.packet s
  let c : GaussPivotInputCopy32.Config :=
    ⟨some .scan, ((), none), GaussPivotInputCopy32.startBank word⟩
  have hl : (((advance GaussPivotInputCopy32.program)^[2 * word.length + 3]) c).l =
      none := by
    rw [show ((advance GaussPivotInputCopy32.program)^[2 * word.length + 3]) c =
      GaussPivotInputCopy32.run (2 * word.length + 3) c from rfl]
    rw [GaussPivotInputCopy32.physical_start]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotPrepController32.Label.copy
    GaussPivotPrepController32.Control.copy
    GaussPivotPrepController32.readCopy (by intro v; rfl)
    (some GaussPivotPrepController32.Label.toCount)
    GaussPivotInputCopy32.program GaussPivotPrepController32.program
    (by intro l; rfl) c (2 * word.length + 3) hl
  refine ⟨t, ht, ?_⟩
  change GaussPivotPrepController32.run t _ = _ at he
  have hrun : ((advance GaussPivotInputCopy32.program)^[2 * word.length + 3]) c =
      GaussPivotInputCopy32.run (2 * word.length + 3) c := rfl
  rw [hrun] at he
  rw [GaussPivotInputCopy32.physical_start] at he
  simpa [BitMachineInline.cfg, GaussPivotPrepController32.initial,
    word, GaussPivotPrepBank.copied] using he

theorem count_global :
    ∃ t ≤ GaussStateRowCount.polynomialClock
        (GaussPivotPrepBank.packet s).length + 1,
      GaussPivotPrepController32.run t
        ⟨some (.count (.inl M.start)), .count M.initial,
          GaussPivotPrepBank.copied s⟩ =
        ⟨some .toExtract, .count (GaussPivotPrepBank.countOut s).var,
          GaussPivotPrepBank.counted s⟩ := by
  obtain ⟨u, hu, hr⟩ := count_local_halt s
  let c : GaussPivotCount32.Config :=
    ⟨some (.inl M.start), M.initial, GaussPivotPrepBank.copied s⟩
  have hl : (((advance GaussPivotCount32.program)^[u]) c).l = none := by
    change (GaussPivotCount32.run u c).l = none
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotPrepController32.Label.count
    GaussPivotPrepController32.Control.count
    GaussPivotPrepController32.readCount (by intro v; rfl)
    (some GaussPivotPrepController32.Label.toExtract)
    GaussPivotCount32.program GaussPivotPrepController32.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, ?_⟩
  change GaussPivotPrepController32.run t _ = _ at he
  have hrun : ((advance GaussPivotCount32.program)^[u]) c =
      GaussPivotCount32.run u c := rfl
  rw [hrun] at he
  rw [hr] at he
  simpa [BitMachineInline.cfg, c] using he

theorem extract_global :
    ∃ t ≤ (2 * (GaussPivotPrepBank.counted s
          GaussPivotCountExtract32.source).length + 3) +
      (∑ j : Fin M.stackCount,
        ((GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s))
          (GaussPivotCount32.slot j)).length) + M.stackCount + 2,
      GaussPivotPrepController32.run t
        ⟨some (.extract (.copy .scan)), .extract ((), none),
          GaussPivotPrepBank.counted s⟩ =
        ⟨some .toParse, .extract ((), none), GaussPivotPrepBank.extracted s⟩ := by
  obtain ⟨u, hu, hr⟩ := extract_local_halt s
  let c : GaussPivotCountExtract32.Config :=
    ⟨some (.copy .scan), ((), none), GaussPivotPrepBank.counted s⟩
  have hl : (((advance GaussPivotCountExtract32.program)^[u]) c).l = none := by
    change (GaussPivotCountExtract32.run u c).l = none
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotPrepController32.Label.extract
    GaussPivotPrepController32.Control.extract
    GaussPivotPrepController32.readExtract (by intro v; rfl)
    (some GaussPivotPrepController32.Label.toParse)
    GaussPivotCountExtract32.program GaussPivotPrepController32.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, ?_⟩
  change GaussPivotPrepController32.run t _ = _ at he
  have hrun : ((advance GaussPivotCountExtract32.program)^[u]) c =
      GaussPivotCountExtract32.run u c := rfl
  rw [hrun] at he
  rw [hr] at he
  simpa [BitMachineInline.cfg, c] using he

theorem parser_global :
    ∃ t ≤ 9 * ((GaussPivotPrepBank.packet s).length + 1) + 1,
      GaussPivotPrepController32.run t
        ⟨some (.parse (.inl (.scan 0))), .parse none,
          GaussPivotPrepBank.extracted s⟩ =
        ⟨some .toFields, .parse none, (GaussPivotPrepBank.parsed s).stk⟩ := by
  obtain ⟨u, hu, hr⟩ := parser_local_halt s
  let c : GaussPivotParser32.Config :=
    ⟨some (.inl (.scan 0)), none, GaussPivotPrepBank.extracted s⟩
  have hl : (((advance GaussPivotParser32.program)^[u]) c).l = none := by
    change (GaussPivotParser32.run u c).l = none
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotPrepController32.Label.parse
    GaussPivotPrepController32.Control.parse
    GaussPivotPrepController32.readParse (by intro v; rfl)
    (some GaussPivotPrepController32.Label.toFields)
    GaussPivotParser32.program GaussPivotPrepController32.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, ?_⟩
  change GaussPivotPrepController32.run t _ = _ at he
  have hrun : ((advance GaussPivotParser32.program)^[u]) c =
      GaussPivotParser32.run u c := rfl
  rw [hrun] at he
  rw [hr] at he
  simpa [BitMachineInline.cfg, c] using he

theorem fields_global :
    ∃ t ≤ GaussPivotFields32.copyClock (GaussPivotPrepBank.parsed s).stk +
      (∑ i : Fin 5,
        ((GaussPivotFields32.after3 (GaussPivotPrepBank.parsed s).stk)
          (GaussPivotFields32.clearBank i)).length) + 7,
      GaussPivotPrepController32.run t
        ⟨some (.fields (.copy 0 .scan)), .fields ((), none),
          (GaussPivotPrepBank.parsed s).stk⟩ =
        ⟨some .done, .fields ((), none), GaussPivotPrepBank.prepared s⟩ := by
  obtain ⟨u, hu, hr⟩ := fields_local_halt s
  let c : GaussPivotFields32.Config :=
    ⟨some (.copy 0 .scan), ((), none), (GaussPivotPrepBank.parsed s).stk⟩
  have hl : (((advance GaussPivotFields32.program)^[u]) c).l = none := by
    change (GaussPivotFields32.run u c).l = none
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    GaussPivotPrepController32.Label.fields
    GaussPivotPrepController32.Control.fields
    GaussPivotPrepController32.readFields (by intro v; rfl)
    (some GaussPivotPrepController32.Label.done)
    GaussPivotFields32.program GaussPivotPrepController32.program
    (by intro l; rfl) c u hl
  refine ⟨t, ht.trans hu, ?_⟩
  change GaussPivotPrepController32.run t _ = _ at he
  have hrun : ((advance GaussPivotFields32.program)^[u]) c =
      GaussPivotFields32.run u c := rfl
  rw [hrun] at he
  rw [hr] at he
  simpa [BitMachineInline.cfg, c] using he

def copyBound : Nat := 2 * (GaussPivotPrepBank.packet s).length + 3

def countBound : Nat :=
  GaussStateRowCount.polynomialClock (GaussPivotPrepBank.packet s).length + 1

def extractBound : Nat :=
  (2 * (GaussPivotPrepBank.counted s
    GaussPivotCountExtract32.source).length + 3) +
  (∑ j : Fin M.stackCount,
    ((GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s))
      (GaussPivotCount32.slot j)).length) + M.stackCount + 2

def parserBound : Nat := 9 * ((GaussPivotPrepBank.packet s).length + 1) + 1

def fieldsBound : Nat :=
  GaussPivotFields32.copyClock (GaussPivotPrepBank.parsed s).stk +
  (∑ i : Fin 5,
    ((GaussPivotFields32.after3 (GaussPivotPrepBank.parsed s).stk)
      (GaussPivotFields32.clearBank i)).length) + 7

def clock : Nat :=
  copyBound s + 1 + countBound s + 1 + extractBound s + 1 +
    parserBound s + 1 + fieldsBound s

theorem outputs :
    ∃ t ≤ clock s,
      GaussPivotPrepController32.run t
        (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
        ⟨some .done, .fields ((), none), GaussPivotPrepBank.prepared s⟩ := by
  obtain ⟨t0, h0, hr0⟩ := copy_global s
  obtain ⟨t1, h1, hr1⟩ := count_global s
  obtain ⟨t2, h2, hr2⟩ := extract_global s
  obtain ⟨t3, h3, hr3⟩ := parser_global s
  obtain ⟨t4, h4, hr4⟩ := fields_global s
  have hs0 : GaussPivotPrepController32.run (t0 + 1)
      (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
      ⟨some (.count (.inl M.start)), .count M.initial,
        GaussPivotPrepBank.copied s⟩ :=
    (GaussPivotPrepController32.run_add hr0 1).trans
      (GaussPivotPrepController32.to_count_step _ _)
  have hs1 : GaussPivotPrepController32.run (t0 + 1 + t1 + 1)
      (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
      ⟨some (.extract (.copy .scan)), .extract ((), none),
        GaussPivotPrepBank.counted s⟩ := by
    have hh := (GaussPivotPrepController32.run_add hs0 t1).trans hr1
    exact (GaussPivotPrepController32.run_add hh 1).trans
      (GaussPivotPrepController32.to_extract_step _ _)
  have hs2 : GaussPivotPrepController32.run (t0 + 1 + t1 + 1 + t2 + 1)
      (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
      ⟨some (.parse (.inl (.scan 0))), .parse none,
        GaussPivotPrepBank.extracted s⟩ := by
    have hh := (GaussPivotPrepController32.run_add hs1 t2).trans hr2
    exact (GaussPivotPrepController32.run_add hh 1).trans
      (GaussPivotPrepController32.to_parse_step _ _)
  have hs3 : GaussPivotPrepController32.run
      (t0 + 1 + t1 + 1 + t2 + 1 + t3 + 1)
      (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
      ⟨some (.fields (.copy 0 .scan)), .fields ((), none),
        (GaussPivotPrepBank.parsed s).stk⟩ := by
    have hh := (GaussPivotPrepController32.run_add hs2 t3).trans hr3
    exact (GaussPivotPrepController32.run_add hh 1).trans
      (GaussPivotPrepController32.to_fields_step _ _)
  refine ⟨t0 + 1 + t1 + 1 + t2 + 1 + t3 + 1 + t4, ?_, ?_⟩
  · unfold clock copyBound countBound extractBound parserBound fieldsBound
    omega
  · exact (GaussPivotPrepController32.run_add hs3 t4).trans hr4

theorem outputs_exact :
    ∃ t ≤ clock s,
      (GaussPivotPrepController32.run t
        (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s))).l =
          some .done ∧
      ∀ j : Stack,
        (GaussPivotPrepController32.run t
          (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s))).stk j =
          if j = 8 then GaussPhysical.encodeTypedMatrix s.B
          else if j = 12 then List.replicate s.c true
          else if j = 13 then List.replicate m true
          else if j = 30 then List.replicate s.r true
          else if j = 31 then GaussPivotPrepBank.packet s
          else [] := by
  obtain ⟨t, ht, hr⟩ := outputs s
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hr]
  · intro j
    rw [hr]
    exact GaussPivotPrepBank.prepared_exact s j

#print axioms parser_start_bank
#print axioms count_local_halt
#print axioms extract_local_halt
#print axioms parser_local_halt
#print axioms fields_local_halt
#print axioms copy_global
#print axioms count_global
#print axioms extract_global
#print axioms parser_global
#print axioms fields_global
#print axioms outputs
#print axioms outputs_exact

end
end CurrentAdditive.GaussPivotPrepRun
