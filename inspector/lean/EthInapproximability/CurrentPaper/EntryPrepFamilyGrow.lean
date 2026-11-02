import EthInapproximability.CurrentPaper.EntryPrepFinal4
import EthInapproximability.CurrentPaper.WeightedRawWordsConsumer

/-!
# Lane owner:b-stage4-entry-program-8: the level-wired family tables WITH a growth bound

`level_family_growth` is the admitted `EntryFamilyLevel.level_family_tables` (same fixed
program `EntryFamilyLevel.program`, same start bank, same exit bank, same table conjuncts),
re-derived by exact reuse of the admitted lemmas (`WeightedLevelFields15.level_fields15_identity`,
`EntryFamilyLevel.copy_step`, `EntryFamilyLevel.copies_to_start`,
`EntryFamilyAssembly.family_assembly`, `BitMachineStackRun.run`, `BitMachineRawSequence.runs`),
with ONE extra conjunct: every cell of the level bank `Z` (which carries the existential scalar
scratch `F Q P`) is bounded by its start length plus `perStep WeightedLevelFields15.program *
publicBound15`, by the admitted `BitMachineStackGrowth.run_growth` applied to the SAME phase-F run.
The proof text is the admitted proof with that conjunct added (the label type of the whole
`EntryFamilyLevel.program` has no `Fintype` instance, so `run_growth` is applied to phase F only;
the family region's exit is exact and needs no bound).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Construction MatrixStage4FamilyData
open EntryFamilyLevel

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

theorem level_family_growth (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
    let g := EncodedETHSource.serializeGraph G
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    let t := Parameters.balanceOrder i
    let L := PrimeSampler.size q t (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
      let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
      let X := Function.update (WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns)
        (WeightedLevelColumnSave.wcell 16) (List.replicate (s * L) true)
      let Y := WeightedLevelFields1346.fieldsBank X d.binBase d.rawWidth d.s
      let Z := WeightedLevelFields15.counts15Bank Y d.s
      ∃ n ≤ WeightedLevelFields15.publicBound15 i g (Fintype.card EG) W a s q L
          d.binBase d.rawWidth d.s + copyBound a q L i.rows t +
          EntryFamilyAssembly.assemblyBound a q t i.rows + 6,
        ((advance program)^[n])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))),
            initialControl,
            Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, initialControl,
            Sum.elim Z (EntryFamilyAssembly.exitBank a q t i.rows
              (Iteration.alphabet_pos G c b y lvl M))⟩ ∧
        (∀ j : LS, (Z j).length ≤ (WeightedLevelColumnSave.initialBank i g W j).length +
          BitMachineStackGrowth.perStep WeightedLevelFields15.program *
            WeightedLevelFields15.publicBound15 i g (Fintype.card EG) W a s q L
              d.binBase d.rawWidth d.s) ∧
        EntryFamilyAssembly.exitBank a q t i.rows (Iteration.alphabet_pos G c b y lvl M)
            (EntryFamilyAssembly.cell .first) =
          fieldTable (familyFirst (Iteration.secondFamily G c b y lvl M)) ∧
        EntryFamilyAssembly.exitBank a q t i.rows (Iteration.alphabet_pos G c b y lvl M)
            (EntryFamilyAssembly.cell .row) =
          fieldTable (familyRow (Iteration.secondFamily G c b y lvl M)) := by
  intro d i g s q a t L W''
  obtain ⟨F, Q, P, hY⟩ := WeightedLevelFields15.level_fields15_identity
    G c b y lvl M W h17 h62 h27 h63 h28 h61 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T X Y Z
  obtain ⟨u, hu, hrun, -, -, -, -, -, -, p17, -, -, -, -, -, -, -, ps0, ps1, ps2, -⟩ := hY
  -- growth of the level bank (admitted `run_growth` on the SAME phase-F run)
  have hgrow : ∀ j : LS, (Z j).length ≤ (WeightedLevelColumnSave.initialBank i g W j).length +
      BitMachineStackGrowth.perStep WeightedLevelFields15.program *
        WeightedLevelFields15.publicBound15 i g (Fintype.card EG) W a s q L
          d.binBase d.rawWidth d.s := by
    intro j
    have hg := BitMachineStackGrowth.run_growth WeightedLevelFields15.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
        WeightedLevelFields15.initialControl, WeightedLevelColumnSave.initialBank i g W⟩ :
        TM2.Cfg (fun _ : LS => Bool) _ _) u j
    rw [hrun] at hg
    exact le_trans hg (Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _)
  have hrows : MatrixWeightedEntryController.persistentBank d 17 =
      List.replicate i.rows true :=
    (WeightedLevelIdentity.persistent_fields G c b y lvl M).1
  have z17 : Z (WeightedLevelColumnSave.wcell 17) = List.replicate i.rows true :=
    p17.trans hrows
  have zt : Z EntryLevelTCell.tcell = List.replicate t true :=
    EntryLevelTCell.level_t G c b y lvl M W F Q P
  have hm : 0 < Construction.qOne a * i.rows := Iteration.alphabet_pos G c b y lvl M
  have hrx : 0 < i.rows := M.rows_pos
  -- phase F: the admitted level controller, lifted
  have hF := BitMachineStackRun.run lvlSlots
    (Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA)
    WeightedLevelFields15.program
    ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
      WeightedLevelFields15.initialControl, WeightedLevelColumnSave.initialBank i g W⟩ u
  rw [hrun] at hF
  have hs : bank lvlSlots (Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA)
      (WeightedLevelColumnSave.initialBank i g W) =
      Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA :=
    EntryFamilyAssembly.bank_exact _ _ _ _ (fun _ => rfl) (fun _ _ => rfl)
  have hf : bank lvlSlots (Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA) Z =
      Sum.elim Z blankA := by
    apply EntryFamilyAssembly.bank_exact
    · intro k; rfl
    · intro j hj
      rcases j with j | j
      · exact absurd ⟨j, rfl⟩ hj
      · rfl
  simp only [stackCfg, hs] at hF
  have hF2 : ((advance Pf)^[u])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
        WeightedLevelFields15.initialControl,
        Sum.elim (WeightedLevelColumnSave.initialBank i g W) blankA⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, WeightedLevelFields15.initialControl, Sum.elim Z blankA⟩ := by
    rw [← hf]
    exact hF
  -- five copies
  let A1 := Function.update blankA (EntryFamilyAssembly.xc .a) (List.replicate a true)
  let A2 := Function.update A1 (EntryFamilyAssembly.cell .q) (List.replicate q true)
  let A3 := Function.update A2 (EntryFamilyAssembly.xc .L) (List.replicate L true)
  let A4 := Function.update A3 (EntryFamilyAssembly.cell .rx) (List.replicate i.rows true)
  have k1 := copy_step (WeightedLevelColumnSave.save 0) (EntryFamilyAssembly.xc .a)
    (by decide) Z blankA rfl rfl a ps0
  have k2 := copy_step (WeightedLevelColumnSave.save 1) (EntryFamilyAssembly.cell .q)
    (by decide) Z A1 (by simp [A1, blankA, EntryFamilyAssembly.xc])
    (by simp [A1, blankA, EntryFamilyAssembly.xc, EntryFamilyAssembly.cell])
    q ps1
  have k3 := copy_step (WeightedLevelColumnSave.save 2) (EntryFamilyAssembly.xc .L)
    (by decide) Z A2 (by simp [A2, A1, Function.update, blankA, EntryFamilyAssembly.xc,
      EntryFamilyAssembly.cell])
    (by simp [A2, A1, Function.update, blankA, EntryFamilyAssembly.xc,
      EntryFamilyAssembly.cell])
    L ps2
  have k4 := copy_step (WeightedLevelColumnSave.wcell 17) (EntryFamilyAssembly.cell .rx)
    (by decide) Z A3 (by simp [A3, A2, A1, Function.update, blankA, EntryFamilyAssembly.xc,
      EntryFamilyAssembly.cell])
    (by simp [A3, A2, A1, Function.update, blankA, EntryFamilyAssembly.xc,
      EntryFamilyAssembly.cell])
    i.rows z17
  have k5 := copy_step EntryLevelTCell.tcell (EntryFamilyAssembly.cell .order)
    (by decide) Z A4 (by simp [A4, A3, A2, A1, Function.update, blankA,
      EntryFamilyAssembly.xc, EntryFamilyAssembly.cell])
    (by simp [A4, A3, A2, A1, Function.update, blankA, EntryFamilyAssembly.xc,
      EntryFamilyAssembly.cell])
    t zt
  simp only [A4, A3, A2, A1] at k5
  rw [copies_to_start] at k5
  -- the assembly, lifted
  obtain ⟨nA, hnA, hA⟩ := EntryFamilyAssembly.family_assembly a q t i.rows hm hrx
  have hAL := BitMachineStackRun.run entSlots
    (Sum.elim Z (EntryFamilyAssembly.startBank a q t i.rows L))
    EntryFamilyAssembly.program
    ⟨some (BitMachineRawSequence.leftLabel (Sum.inr false)),
      EntryFamilyAssembly.initialControl,
      EntryFamilyAssembly.startBank a q t i.rows L⟩ nA
  rw [hA] at hAL
  have hs2 : bank entSlots (Sum.elim Z (EntryFamilyAssembly.startBank a q t i.rows L))
      (EntryFamilyAssembly.startBank a q t i.rows L) =
      Sum.elim Z (EntryFamilyAssembly.startBank a q t i.rows L) :=
    EntryFamilyAssembly.bank_exact _ _ _ _ (fun _ => rfl) (fun _ _ => rfl)
  have hf2 : bank entSlots (Sum.elim Z (EntryFamilyAssembly.startBank a q t i.rows L))
      (EntryFamilyAssembly.exitBank a q t i.rows hm) =
      Sum.elim Z (EntryFamilyAssembly.exitBank a q t i.rows hm) := by
    apply EntryFamilyAssembly.bank_exact
    · intro k; rfl
    · intro j hj
      rcases j with j | j
      · rfl
      · exact absurd ⟨j, rfl⟩ hj
  simp only [stackCfg, hs2, hf2] at hAL
  -- compose, innermost first
  obtain ⟨v5, hv5, r5⟩ := BitMachineRawSequence.runs (copyProgram cT) Pa
    _ _ _ _ _ _ _ _ _ _ _ k5 hAL
  obtain ⟨v4, hv4, r4⟩ := BitMachineRawSequence.runs (copyProgram cR) s5
    _ _ _ _ _ _ _ _ _ _ _ k4 r5
  obtain ⟨v3, hv3, r3⟩ := BitMachineRawSequence.runs (copyProgram cL) s4
    _ _ _ _ _ _ _ _ _ _ _ k3 r4
  obtain ⟨v2, hv2, r2⟩ := BitMachineRawSequence.runs (copyProgram cQ) s3
    _ _ _ _ _ _ _ _ _ _ _ k2 r3
  obtain ⟨v1, hv1, r1⟩ := BitMachineRawSequence.runs (copyProgram cA) s2
    _ _ _ _ _ _ _ _ _ _ _ k1 r2
  obtain ⟨v0, hv0, r0⟩ := BitMachineRawSequence.runs Pf s1
    _ _ _ _ _ _ _ _ _ _ _ hF2 r1
  refine ⟨v0, ?_, r0, hgrow, rfl, rfl⟩
  have hc : copyBound a q L i.rows t =
      (2 * a + 2) + (2 * q + 2) + (2 * L + 2) + (2 * i.rows + 2) + (2 * t + 2) := rfl
  rw [hc]
  have hu' : u ≤ WeightedLevelFields15.publicBound15 i g (Fintype.card EG) W a s q L
      d.binBase d.rawWidth d.s := hu
  have hv0' : v0 ≤ u + v1 + 1 := hv0
  have hv1' : v1 ≤ (2 * a + 2) + v2 + 1 := hv1
  have hv2' : v2 ≤ (2 * q + 2) + v3 + 1 := hv2
  have hv3' : v3 ≤ (2 * L + 2) + v4 + 1 := hv3
  have hv4' : v4 ≤ (2 * i.rows + 2) + v5 + 1 := hv4
  have hv5' : v5 ≤ (2 * t + 2) + nA + 1 := hv5
  omega

#print axioms level_family_growth

end

end EthInapproximability.CurrentPaper.EntryPrepFamily
