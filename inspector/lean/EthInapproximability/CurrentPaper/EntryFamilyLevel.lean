import EthInapproximability.CurrentPaper.EntryFamilyAssembly
import EthInapproximability.CurrentPaper.EntryLevelTCell

/-!
# Segment 1 on the actual level: both family tables from the level's own words

Lane owner:b-stage4-entry-program-2, segment 1 (wiring).

ONE fixed controller on `WeightedLevelColumnSave.Stack ⊕ EntryFamilyAssembly.ACell`
(the second summand initially blank):

1. the admitted `WeightedLevelFields15.program` (lifted unchanged), from the
   admitted level start bank `WeightedLevelColumnSave.initialBank i g W`;
2. five charged source-preserving copies from the reached level bank `Z`
   into the family region: save 0 (`a`) → `X.a`, save 1 (`q`) → `q`,
   save 2 (`L`) → `X.L`, writer 17 (`rx = M.rows`) → `rx`,
   `EntryLevelTCell.tcell` (`t`) → `order`;
3. the checked segment-1 assembly `EntryFamilyAssembly.program` (lifted).

Exit: the level bank `Z` unchanged, and the family region equal to
`EntryFamilyAssembly.exitBank a q t M.rows _`, whose table cells are the
literal one-hot tables of the SAME `Iteration.secondFamily G c b y lvl M`.
Every handoff charged; no family word supplied beyond the admitted level
start bank's own inputs.
-/

namespace EthInapproximability.CurrentPaper.EntryFamilyLevel

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Construction MatrixStage4FamilyData

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev LS := WeightedLevelColumnSave.Stack
abbrev ACell := EntryFamilyAssembly.ACell
abbrev Stack := LS ⊕ ACell

def ent (c : ACell) : Stack := .inr c

def lvlSlots : LS ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def entSlots : ACell ↪ Stack := ⟨Sum.inr, Sum.inr_injective⟩

def blankA : ACell → List Bool := fun _ => []

def mkCopy (src : LS) (dst : ACell) (hd : dst ≠ EntryFamilyAssembly.xc .s2) :
    Fin 3 ↪ Stack :=
  ⟨![.inl src, ent dst, ent (EntryFamilyAssembly.xc .s2)], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [ent]⟩

def cA := mkCopy (WeightedLevelColumnSave.save 0) (EntryFamilyAssembly.xc .a) (by decide)
def cQ := mkCopy (WeightedLevelColumnSave.save 1) (EntryFamilyAssembly.cell .q) (by decide)
def cL := mkCopy (WeightedLevelColumnSave.save 2) (EntryFamilyAssembly.xc .L) (by decide)
def cR := mkCopy (WeightedLevelColumnSave.wcell 17) (EntryFamilyAssembly.cell .rx) (by decide)
def cT := mkCopy EntryLevelTCell.tcell (EntryFamilyAssembly.cell .order) (by decide)

theorem copy_step (src : LS) (dst : ACell) (hd : dst ≠ EntryFamilyAssembly.xc .s2)
    (Zb : LS → List Bool) (A : ACell → List Bool)
    (hA2 : A (EntryFamilyAssembly.xc .s2) = []) (hAd : A dst = []) (w : ℕ)
    (hz : Zb src = List.replicate w true) :
    ((advance (copyProgram (mkCopy src dst hd)))^[2 * w + 2])
      (⟨some .scan, none, Sum.elim Zb A⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Sum.elim Zb (Function.update A dst (List.replicate w true))⟩ := by
  have h := copy_run (mkCopy src dst hd) (Sum.elim Zb A) hA2
  have e0 : (Sum.elim Zb A) (mkCopy src dst hd 0) = List.replicate w true := hz
  have e1 : (Sum.elim Zb A) (mkCopy src dst hd 1) = [] := hAd
  rw [e0, List.length_replicate, e1, List.append_nil] at h
  rw [h]
  rw [show mkCopy src dst hd 1 = Sum.inr dst from rfl, ← Sum.elim_update_right]

/-! ## The fixed controller -/

def Pf := fun l => stackStmt lvlSlots (WeightedLevelFields15.program l)
def Pa := fun l => stackStmt entSlots (EntryFamilyAssembly.program l)

def s5 := BitMachineRawSequence.program (copyProgram cT) Pa
  (BitMachineRawSequence.leftLabel (Sum.inr false)) (none : Option Bool)
  EntryFamilyAssembly.initialControl
def s4 := BitMachineRawSequence.program (copyProgram cR) s5
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), EntryFamilyAssembly.initialControl)
def s3 := BitMachineRawSequence.program (copyProgram cL) s4
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((none : Option Bool), EntryFamilyAssembly.initialControl))
def s2 := BitMachineRawSequence.program (copyProgram cQ) s3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((none : Option Bool), ((none : Option Bool),
    EntryFamilyAssembly.initialControl)))
def s1 := BitMachineRawSequence.program (copyProgram cA) s2
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((none : Option Bool), ((none : Option Bool),
    ((none : Option Bool), EntryFamilyAssembly.initialControl))))

def tailControl :=
  ((none : Option Bool), ((none : Option Bool), ((none : Option Bool),
    ((none : Option Bool), ((none : Option Bool), EntryFamilyAssembly.initialControl)))))

/-- The single fixed controller of the level-wired segment 1. -/
def program := BitMachineRawSequence.program Pf s1
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  WeightedLevelFields15.initialControl tailControl

def initialControl := (WeightedLevelFields15.initialControl, tailControl)

def copyBound (a q L rx t : ℕ) : ℕ :=
  (2 * a + 2) + (2 * q + 2) + (2 * L + 2) + (2 * rx + 2) + (2 * t + 2)

theorem copies_to_start (a q L rx t : ℕ) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update blankA (EntryFamilyAssembly.xc .a) (List.replicate a true))
      (EntryFamilyAssembly.cell .q) (List.replicate q true))
      (EntryFamilyAssembly.xc .L) (List.replicate L true))
      (EntryFamilyAssembly.cell .rx) (List.replicate rx true))
      (EntryFamilyAssembly.cell .order) (List.replicate t true) =
    EntryFamilyAssembly.startBank a q t rx L := by
  funext j
  rcases j with c | k | x
  · cases c <;> simp [EntryFamilyAssembly.startBank, EntryFamilyAssembly.full,
      FamilyRowBody.rowBank, EntryFamilyAssembly.cell, EntryFamilyAssembly.xc,
      Function.update, blankA]
  · simp [EntryFamilyAssembly.startBank, EntryFamilyAssembly.full,
      EntryFamilyAssembly.cell, EntryFamilyAssembly.xc, Function.update, blankA]
  · cases x <;> simp [EntryFamilyAssembly.startBank, EntryFamilyAssembly.full,
      EntryFamilyAssembly.xBank, EntryFamilyAssembly.cell, EntryFamilyAssembly.xc,
      Function.update, blankA]

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

/-- Segment 1, wired: from the admitted level start bank, the fixed
controller reaches the admitted level exit bank `Z` together with both
literal one-hot family tables of the actual `Iteration.secondFamily`. -/
theorem level_family_tables (G : EndpointGraph VG EG) (c b y lvl : ℕ)
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
  refine ⟨v0, ?_, r0, rfl, rfl⟩
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

#print axioms copy_step
#print axioms copies_to_start
#print axioms level_family_tables

end

end EthInapproximability.CurrentPaper.EntryFamilyLevel
