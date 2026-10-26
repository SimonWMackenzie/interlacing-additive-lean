import EthInapproximability.CurrentPaper.WeightedLevelFields1346

/-! Lane owner:b-weighted-level-2, unit 2, segment 2 (partial): ONE fixed
controller = the frozen `WeightedLevelStagePrefix.program` followed by the
checked `WeightedLevelFields1346.tailProgram`, run at the actual level
parameters of the SAME `Iteration.step G c b y lvl M`, with one public
output-sensitive clock. The exit bank carries eleven persistent writer fields
of the SAME `ProtectedFullBankBridgeScratch.actualD G c b y lvl M`:
1, 3, 4, 6 (new) and 16, 17, 21, 26, 27, 28, 29 (from the frozen prefix),
plus the retained `a, q, L, s*L`.

The clear cost of writer 1/3/4/6 (content not assumed blank) is majorized by
their initial lengths plus the fixed push constant of the frozen prefix
controller (`BitMachineStackGrowth.perStep`, a finite classical supremum over
its labels) times the prefix public clock. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelFieldsIdentity

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevelColumnSave WeightedLevelFields1346

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-! ## Arithmetic of the admitted semantic input -/

theorem input_fields {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).fullDivisor =
      182 * (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family
        order vectors cap).binBase ∧
    (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).diagonalDivisor =
      2 * (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family
        order vectors cap).rawWidth ∧
    (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).fullBoundary =
      (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).rawWidth *
      (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).fullDivisor ∧
    (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).uniform =
      (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).binBase ^
      (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order
        vectors cap).s := by
  have hsec : Fintype.card (Construction.SecondRows a s q (Fin cy)) =
      MatrixStage4Digits.binBase a s q cy := by
    simp [MatrixStage4Digits.binBase, MatrixStage4Digits.wordBase]
  have hraw : Fintype.card (Construction.RawColumns a s q (Fin cy)) =
      MatrixStage4Codes.cols a s q cy := by
    simp [MatrixStage4Codes.cols]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 182 * Fintype.card (Construction.SecondRows a s q (Fin cy)) =
      182 * MatrixStage4Digits.binBase a s q cy
    rw [hsec]
  · show 2 * Fintype.card (Construction.RawColumns a s q (Fin cy)) =
      2 * MatrixStage4Codes.cols a s q cy
    rw [hraw]
  · show Fintype.card (Construction.RawColumns a s q (Fin cy)) *
        (182 * Fintype.card (Construction.SecondRows a s q (Fin cy))) =
      MatrixStage4Codes.cols a s q cy *
        (182 * Fintype.card (Construction.SecondRows a s q (Fin cy)))
    rw [hraw]
  · show Construction.uniformCopies (Y := Fin cy) a s q =
      MatrixStage4Digits.binBase a s q cy ^ s
    rw [Construction.uniformCopies, hsec]

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

theorem actualD_fields (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    d.fullDivisor = 182 * d.binBase ∧ d.diagonalDivisor = 2 * d.rawWidth ∧
      d.fullBoundary = d.rawWidth * d.fullDivisor ∧ d.uniform = d.binBase ^ d.s := by
  intro d
  exact input_fields _ _ _ _ _ _ _ _ _ _ _ _

theorem bank1 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 1 =
      List.replicate d.uniform true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank3 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 3 =
      List.replicate d.fullBoundary true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank4 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 4 =
      List.replicate d.fullDivisor true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank6 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 6 =
      List.replicate d.diagonalDivisor true := by
  simp [MatrixWeightedEntryController.persistentBank]

/-! ## The fixed controller and its public clock -/

def program := BitMachineRawSequence.program WeightedLevelStagePrefix.program
  WeightedLevelFields1346.tailProgram WeightedLevelFields1346.tailStart
  WeightedLevelStagePrefix.initialControl WeightedLevelFields1346.tailInitial

def initialControl :=
  (WeightedLevelStagePrefix.initialControl, WeightedLevelFields1346.tailInitial)

/-- Fixed push constant of the frozen prefix controller. -/
def prefixPush : ℕ := BitMachineStackGrowth.perStep WeightedLevelStagePrefix.program

def publicBound1346 (i : Parameters.Input) (g : EncodedGraph.Graph) (e : ℕ)
    (W : Fin 64 → List Bool) (a s q L B C S : ℕ) : ℕ :=
  let P := WeightedLevelStagePrefix.publicBound16 i g e W a s q L
  P + (((W 1).length + (W 3).length + (W 4).length + (W 6).length +
      4 * (prefixPush * P) + 6) + (182 + 1) +
    MatrixAddressMachine.exactTime 182 B 0 +
    MatrixAddressMachine.exactTime C (182 * B) 0 + (2 * C + 2) + (2 * C + 2) +
    (1 + 1) + (2 * S + 2) + MatrixWeightedPower.powerBound B S + (182 + 2) + 9) + 1

/-- One level, same constructor, one public clock: eleven persistent writer
fields of `actualD` for the SAME step, physically produced, plus the retained
`a`, `q`, `L`, `s*L`. -/
theorem level_fields_identity (G : EndpointGraph VG EG) (c b y lvl : ℕ)
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
    let L := PrimeSampler.size q (Parameters.balanceOrder i)
      (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
      let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
      let X := Function.update (exitBank T a s q L i.rows i.columns)
        (wcell 16) (List.replicate (s * L) true)
      let Y := fieldsBank X d.binBase d.rawWidth d.s
      ∃ u ≤ publicBound1346 i g (Fintype.card EG) W a s q L
          d.binBase d.rawWidth d.s,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
            initialControl, WeightedLevelColumnSave.initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, initialControl, Y⟩ ∧
        Y (wcell 1) = MatrixWeightedEntryController.persistentBank d 1 ∧
        Y (wcell 3) = MatrixWeightedEntryController.persistentBank d 3 ∧
        Y (wcell 4) = MatrixWeightedEntryController.persistentBank d 4 ∧
        Y (wcell 6) = MatrixWeightedEntryController.persistentBank d 6 ∧
        Y (wcell 16) = MatrixWeightedEntryController.persistentBank d 16 ∧
        Y (wcell 17) = MatrixWeightedEntryController.persistentBank d 17 ∧
        Y (wcell 27) = MatrixWeightedEntryController.persistentBank d 27 ∧
        Y (wcell 28) = MatrixWeightedEntryController.persistentBank d 28 ∧
        Y (wcell 21) = MatrixWeightedEntryController.persistentBank d 21 ∧
        Y (wcell 26) = MatrixWeightedEntryController.persistentBank d 26 ∧
        Y (wcell 29) = MatrixWeightedEntryController.persistentBank d 29 ∧
        Y (save 0) = List.replicate (Iteration.a G c b y lvl M) true ∧
        Y (save 1) = List.replicate (Iteration.q₂ G c b y lvl M) true ∧
        Y (save 2) = List.replicate (Iteration.labels G c b y lvl M) true ∧
        Y (save 3) = List.replicate d.stagePrefixRows true := by
  intro d i g s q a L W''
  obtain ⟨F, Q, P, hX⟩ := WeightedLevelStagePrefix.level_stage_prefix_identity
    G c b y lvl M W h17 h62 h27 h63 h28 h61 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T X Y
  obtain ⟨u, hu, hrun, p16, p17, p27, p28, p21, p26, p29, ps0, ps1, ps2, ps3⟩ := hX
  have hu' : u ≤ WeightedLevelStagePrefix.publicBound16 i g (Fintype.card EG) W a s q L := hu
  obtain ⟨f4, f6, f3, f1⟩ := actualD_fields G c b y lvl M
  have f4' : d.fullDivisor = 182 * d.binBase := f4
  have f6' : d.diagonalDivisor = 2 * d.rawWidth := f6
  have f3' : d.fullBoundary = d.rawWidth * d.fullDivisor := f3
  have f1' : d.uniform = d.binBase ^ d.s := f1
  -- operands of the tail on the reached bank
  have x29 : X (wcell 29) = List.replicate d.binBase true :=
    p29.trans (WeightedLevelIdentity.bank29 d)
  have x21 : X (wcell 21) = List.replicate d.rawWidth true :=
    p21.trans (WeightedLevelIdentity.bank21 d)
  have x28 : X (wcell 28) = List.replicate d.s true :=
    p28.trans (WeightedLevelIdentity.bank28 d)
  have xs4 : X (save 4) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (save 4) = []
    rw [Function.update_of_ne (save_ne_wcell 4 16)]
    rfl
  have xs5 : X (save 5) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (save 5) = []
    rw [Function.update_of_ne (save_ne_wcell 5 16)]
    rfl
  have xs6 : X (save 6) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (save 6) = []
    rw [Function.update_of_ne (save_ne_wcell 6 16)]
    rfl
  have xb (k : Fin 64) (j : Fin 40) (hj : 13 ≤ j.val)
      (hk : ColumnWriterJoin.slots j = k) (hk16 : k ≠ 16) : X (wcell k) = [] := by
    show Function.update (exitBank T a s q L i.rows i.columns) (wcell 16)
      (List.replicate (s * L) true) (wcell k) = []
    rw [Function.update_of_ne (wcell_ne hk16)]
    have hb := (WeightedColumnActualStage.exit_blank T a s q L i.rows i.columns).2.1 j hj
    rw [hk] at hb
    exact hb
  have x30 : X (wcell 30) = [] := xb 30 25 (by decide) (by decide) (by decide)
  have x31 : X (wcell 31) = [] := xb 31 26 (by decide) (by decide) (by decide)
  have x32 : X (wcell 32) = [] := xb 32 27 (by decide) (by decide) (by decide)
  obtain ⟨t, ht, htail⟩ := WeightedLevelFields1346.tail_run X d.binBase d.rawWidth d.s
    x29 x21 x28 xs4 xs5 xs6 x30 x31 x32
  obtain ⟨v, hv, hr⟩ := BitMachineRawSequence.runs
    WeightedLevelStagePrefix.program WeightedLevelFields1346.tailProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    WeightedLevelFields1346.tailStart
    WeightedLevelStagePrefix.initialControl WeightedLevelStagePrefix.initialControl
    WeightedLevelFields1346.tailInitial WeightedLevelFields1346.tailInitial
    (WeightedLevelColumnSave.initialBank i g W) X Y u t hrun htail
  -- public majorant of the charged clear of writer 1/3/4/6
  have grow (k : Fin 64) : (X (wcell k)).length ≤
      (W k).length + prefixPush *
        WeightedLevelStagePrefix.publicBound16 i g (Fintype.card EG) W a s q L := by
    have h := BitMachineStackGrowth.run_growth WeightedLevelStagePrefix.program
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        WeightedLevelStagePrefix.initialControl,
        WeightedLevelColumnSave.initialBank i g W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) u (wcell k)
    rw [hrun] at h
    have hi : WeightedLevelColumnSave.initialBank i g W (wcell k) = W k :=
      WeightedLevelPublicClock.initial_writer i g W k
    have hm : prefixPush * u ≤ prefixPush *
        WeightedLevelStagePrefix.publicBound16 i g (Fintype.card EG) W a s q L :=
      Nat.mul_le_mul_left _ hu'
    change (X (wcell k)).length ≤
      (WeightedLevelColumnSave.initialBank i g W (wcell k)).length +
        BitMachineStackGrowth.perStep WeightedLevelStagePrefix.program * u at h
    rw [hi] at h
    unfold prefixPush
    unfold prefixPush at hm
    omega
  have hclear : clearCost4 X ≤ (W 1).length + (W 3).length + (W 4).length +
      (W 6).length + 4 * (prefixPush *
        WeightedLevelStagePrefix.publicBound16 i g (Fintype.card EG) W a s q L) + 6 := by
    unfold clearCost4
    rw [Fin.sum_univ_four]
    have g1 := grow 1
    have g3 := grow 3
    have g4 := grow 4
    have g6 := grow 6
    change (X (wcell 1)).length + (X (wcell 3)).length + (X (wcell 4)).length +
        (X (wcell 6)).length + 6 ≤ _
    omega
  -- cell facts of the exit bank
  have yo (k : Fin 64) (h1 : k ≠ 1) (h3 : k ≠ 3) (h4 : k ≠ 4) (h6 : k ≠ 6) :
      Y (wcell k) = X (wcell k) := by
    show fieldsBank X d.binBase d.rawWidth d.s (wcell k) = X (wcell k)
    simp only [fieldsBank, Function.update_of_ne (wcell_ne h1),
      Function.update_of_ne (wcell_ne h3), Function.update_of_ne (wcell_ne h4),
      Function.update_of_ne (wcell_ne h6)]
  have ys (j : Fin 7) : Y (save j) = X (save j) := by
    show fieldsBank X d.binBase d.rawWidth d.s (save j) = X (save j)
    simp only [fieldsBank, Function.update_of_ne (save_ne_wcell j 1),
      Function.update_of_ne (save_ne_wcell j 3), Function.update_of_ne (save_ne_wcell j 4),
      Function.update_of_ne (save_ne_wcell j 6)]
  refine ⟨v, ?_, hr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold WeightedLevelFields1346.tailCost at ht
    unfold publicBound1346
    dsimp only
    omega
  · show fieldsBank X d.binBase d.rawWidth d.s (wcell 1) = _
    simp only [fieldsBank, Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 3),
      Function.update_self]
    rw [bank1, f1']
  · show fieldsBank X d.binBase d.rawWidth d.s (wcell 3) = _
    simp only [fieldsBank, Function.update_of_ne (wcell_ne (by decide) : wcell 3 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 3 ≠ wcell 4),
      Function.update_self]
    rw [bank3, f3', f4']
  · show fieldsBank X d.binBase d.rawWidth d.s (wcell 4) = _
    simp only [fieldsBank, Function.update_of_ne (wcell_ne (by decide) : wcell 4 ≠ wcell 6),
      Function.update_self]
    rw [bank4, f4']
  · show fieldsBank X d.binBase d.rawWidth d.s (wcell 6) = _
    simp only [fieldsBank, Function.update_self]
    rw [bank6, f6']
  · rw [yo 16 (by decide) (by decide) (by decide) (by decide)]; exact p16
  · rw [yo 17 (by decide) (by decide) (by decide) (by decide)]; exact p17
  · rw [yo 27 (by decide) (by decide) (by decide) (by decide)]; exact p27
  · rw [yo 28 (by decide) (by decide) (by decide) (by decide)]; exact p28
  · rw [yo 21 (by decide) (by decide) (by decide) (by decide)]; exact p21
  · rw [yo 26 (by decide) (by decide) (by decide) (by decide)]; exact p26
  · rw [yo 29 (by decide) (by decide) (by decide) (by decide)]; exact p29
  · rw [ys 0]; exact ps0
  · rw [ys 1]; exact ps1
  · rw [ys 2]; exact ps2
  · rw [ys 3]; exact ps3

#print axioms input_fields
#print axioms actualD_fields
#print axioms level_fields_identity

end
end EthInapproximability.CurrentPaper.WeightedLevelFieldsIdentity
