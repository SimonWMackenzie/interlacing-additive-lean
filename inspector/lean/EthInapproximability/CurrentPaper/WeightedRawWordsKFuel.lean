import EthInapproximability.CurrentPaper.WeightedRawWordsClock

/-! # S5: one fixed program from master `N` to master `K = unary k`

`k = SlowClock.repetitions (CutoffBitMachine.clock M) n`; for the paper's
`M = CutoffBitMachine.actualMachine c A d` this is
`SlowClock.repetitions (actualClock c A d) n` by definition. Every S5 scratch
region is empty again at exit. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

variable (M : BitMachine.Machine)

def Drv : BitMachine.Machine := ClockRuntime.machine M

def inCell : Global := aux (.nat 3 (Drv M).input.val)
def outCell : Global := aux (.nat 3 (Drv M).output.val)
def srcCell : Global := aux (.nat 2 1)

def kA := copyProg (aux .N) (inCell M) (by intro h; cases h) (by intro h; cases h)
  (by intro h; cases h)
def kC := copyProg (outCell M) srcCell (by intro h; cases h) (by intro h; cases h)
  (by intro h; cases h)

def kS6 := BitMachineRawSequence.program (clearProgram (region0 M)) fuelProgram
  (BitMachineRawSequence.leftLabel ()) ((), none) (none, (false, false))
def kS5 := BitMachineRawSequence.program (projProgram M) (kS6 M)
  (BitMachineRawSequence.leftLabel 0) none (((), none), (none, (false, false)))
def kS4 := BitMachineRawSequence.program (clearProgram (region3 (Drv M))) (kS5 M)
  (BitMachineRawSequence.leftLabel (.inl (.scan 0))) ((), none)
  (none, (((), none), (none, (false, false))))
def kS3 := BitMachineRawSequence.program (kC M) (kS4 M)
  (BitMachineRawSequence.leftLabel 0) none
  (((), none), (none, (((), none), (none, (false, false)))))
def kS2 := BitMachineRawSequence.program (machProgram (Drv M) 3) (kS3 M)
  (BitMachineRawSequence.leftLabel .scan) (Drv M).initial
  (none, (((), none), (none, (((), none), (none, (false, false))))))
/-- The S5 program. -/
def kProgram := BitMachineRawSequence.program (kA M) (kS2 M)
  (BitMachineRawSequence.leftLabel (Drv M).start) none
  ((Drv M).initial, (none, (((), none), (none, (((), none), (none, (false, false)))))))

def kCtrl := ((none : Option Bool),
  ((Drv M).initial, ((none : Option Bool), ((((), (none : Option Bool))),
    ((none : Option Bool), ((((), (none : Option Bool))), ((none : Option Bool), (false, false))))))))

def kBound (n : ℕ) : ℕ :=
  (2 * n + 2) + (ClockRuntime.time M n +
    ((2 * (ClockRuntime.output M (List.replicate n true)).length + 2) +
    (((Drv M).stackCount * (n + BitMachineStackGrowth.perStep (Drv M).program *
        ClockRuntime.time M n) + (Drv M).stackCount + 2) +
    (((2 * ClockStepEncoded.width M + 3) *
        ((ClockRuntime.output M (List.replicate n true)).length + 1) + 1) +
    ((ClockStepEncoded.width M * (ClockRuntime.output M (List.replicate n true)).length +
        ClockStepEncoded.width M + 2) +
    fuelBound (kValue M n) + 1) + 1) + 1) + 1) + 1) + 1

theorem k_run (n : ℕ) (S : Global → List Bool) (hS : KReady S n) :
    ∃ t ≤ kBound M n,
      ((advance (kProgram M))^[t])
        (⟨some (BitMachineRawSequence.leftLabel .scan), kCtrl M, S⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, kCtrl M, Function.update S (aux .K) (List.replicate (kValue M n) true)⟩ := by
  have hnat' : ∀ r i, S (Sum.inr (Aux.nat r i)) = [] := hS.hnat
  set P := ClockRuntime.output M (List.replicate n true) with hPdef
  -- A: copy N into the driver input
  have sA := copy_word (aux .N) (inCell M) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) S
    (hS.hnat _ _) hS.hcs
  rw [hS.hN] at sA
  simp only [List.length_replicate] at sA
  set S1 := Function.update S (inCell M) (List.replicate n true) with hS1
  -- B: the embedded clock driver
  have hout : (Drv M).OutputsWithin (List.replicate n true) P (ClockRuntime.time M n) := by
    have h := ClockRuntime.outputs M (List.replicate n true)
    rw [List.length_replicate] at h
    exact h
  obtain ⟨tB, htB, v, F, sB, hFo, hFl⟩ := mach_run (Drv M) 3 (List.replicate n true) P
    (ClockRuntime.time M n) hout S1
    (by
      intro i
      by_cases hi : i = (Drv M).input
      · subst hi
        rw [if_pos rfl, hS1]
        exact Function.update_self (inCell M) _ S
      · have : aux (.nat 3 i.val) ≠ inCell M := by
          simp only [inCell, aux, ne_eq, Sum.inr.injEq, Aux.nat.injEq, true_and]
          exact fun h => hi (Fin.ext h)
        rw [hS1, Function.update_of_ne this, if_neg hi]
        exact hS.hnat _ _)
  set X2 := bank (machSlots (Drv M) 3) S1 F with hX2
  have hX2out : ∀ j, (¬ ∃ i, machSlots (Drv M) 3 i = j) → X2 j = S1 j :=
    fun j hj => bank_outside _ _ _ j hj
  have notR3 : ∀ j : Aux, (∀ i : ℕ, j ≠ .nat 3 i) → ¬ ∃ i, machSlots (Drv M) 3 i = aux j := by
    rintro j hj ⟨i, hi⟩
    exact hj i.val (Sum.inr.inj hi).symm
  -- C: copy the packet to the projection source
  have hX2o : X2 (outCell M) = P := by
    rw [show outCell M = machSlots (Drv M) 3 (Drv M).output from rfl, hX2, bank_at, hFo]
  have hX2s : X2 srcCell = [] := by
    rw [hX2out srcCell (notR3 (.nat 2 1) (by intro i h; cases h))]
    rw [hS1, Function.update_of_ne (by intro h; cases h)]
    exact hS.hnat 2 1
  have hX2cs : X2 (aux .cs) = [] := by
    rw [hX2out (aux .cs) (notR3 .cs (by intro i h; cases h))]
    rw [hS1, Function.update_of_ne (by intro h; cases h)]
    exact hS.hcs
  have sC := copy_word (outCell M) srcCell (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) X2 hX2s hX2cs
  rw [hX2o] at sC
  -- D: clear the driver region
  have sD := clear_run (region3 (Drv M)) (region3_injective (Drv M)) (Function.update X2 srcCell P)
  have hsumD : (∑ i, ((Function.update X2 srcCell P) (region3 (Drv M) i)).length) ≤
      (Drv M).stackCount * (n + BitMachineStackGrowth.perStep (Drv M).program *
        ClockRuntime.time M n) := by
    apply sum_le_mul
    intro i
    have hne : region3 (Drv M) i ≠ srcCell := by intro h; cases h
    rw [Function.update_of_ne hne, show region3 (Drv M) i = machSlots (Drv M) 3 i from rfl,
      hX2, bank_at]
    have := hFl i
    simpa using this
  have hD : BitMachineClearBank.cleared (region3 (Drv M)) (Function.update X2 srcCell P) =
      Function.update S srcCell P := by
    have hn : ∀ i, region3 (Drv M) i ≠ srcCell := fun i => by intro h; cases h
    rw [cleared_update_comm _ _ _ _ hn, hX2,
      cleared_bank_region (region3 (Drv M)) (machSlots (Drv M) 3) S1 F (fun k => ⟨k, rfl⟩), hS1,
      cleared_update_mem (region3 (Drv M)) S (inCell M) _ ⟨(Drv M).input, rfl⟩,
      cleared_eq_self (region3 (Drv M)) S (fun i => hS.hnat 3 i.val)]
  rw [hD] at sD
  -- E: the counter projection
  obtain ⟨tE, htE, sE⟩ := proj_stage M n S hS
  -- F: clear the projection fields
  set C := BitMachineBankCodec.contents
    (Function.update (ClockStepEncoded.toBank M (ClockInputPreparation.readyBank M
      [(ClockRuntime.state M (List.replicate n true) n).active]
      (List.replicate n true) (Nat.bits (kValue M n)))) (ClockRuntime.counterField M) [])
    [] [] (Nat.bits (kValue M n)) with hC
  set X5 := bank (projSlots M) (Function.update S srcCell P) C with hX5
  have sF := clear_run (region0 M) (region0_injective M) X5
  have hB0len : ∀ i, (C (.inl i)).length ≤ P.length := by
    intro i
    have hP : P = BitMachineBankCodec.encode (ClockStepEncoded.toBank M
        (ClockInputPreparation.readyBank M [(ClockRuntime.state M (List.replicate n true) n).active]
          (List.replicate n true) (Nat.bits (kValue M n)))) := by
      rw [hPdef, ClockRuntime.output_counter]
      simp only [List.length_replicate]
      rfl
    have hd := BitMachineBankCodec.decode_encode (ClockStepEncoded.toBank M
        (ClockInputPreparation.readyBank M [(ClockRuntime.state M (List.replicate n true) n).active]
          (List.replicate n true) (Nat.bits (kValue M n))))
    rw [← hP] at hd
    simp only [hC, BitMachineBankCodec.contents, Sum.elim_inl]
    by_cases hi : i = ClockRuntime.counterField M
    · subst hi; simp
    · rw [Function.update_of_ne hi]
      exact BitMachineBankCodec.decoded_word_length hd i
  have hsumF : (∑ i, (X5 (region0 M i)).length) ≤ ClockStepEncoded.width M * P.length := by
    apply sum_le_mul
    intro i
    rw [show region0 M i = projSlots M (.inl i) from rfl, hX5, bank_at]
    exact hB0len i
  have hF : BitMachineClearBank.cleared (region0 M) X5 =
      Function.update S bitsCell (Nat.bits (kValue M n)) := by
    funext x
    unfold BitMachineClearBank.cleared
    by_cases hc : ∃ i, region0 M i = x
    · rw [if_pos hc]
      obtain ⟨i, rfl⟩ := hc
      rw [Function.update_of_ne (by intro h; cases h)]
      exact (hS.hnat _ _).symm
    · rw [if_neg hc]
      by_cases hr : ∃ k, projSlots M k = x
      · obtain ⟨k, rfl⟩ := hr
        rw [hX5, bank_at]
        rcases k with k | k
        · exact absurd ⟨k, rfl⟩ hc
        · fin_cases k
          · show C (.inr 0) = Function.update S bitsCell _ (aux (.nat 2 1))
            rw [Function.update_of_ne (by intro h; cases h), hS.hnat]
            rfl
          · show C (.inr 1) = Function.update S bitsCell _ (aux (.nat 2 2))
            rw [Function.update_of_ne (by intro h; cases h), hS.hnat]
            rfl
          · show C (.inr 2) = Function.update S bitsCell _ bitsCell
            rw [Function.update_self]
            rfl
      · rw [hX5, bank_outside _ _ _ _ hr]
        have h1 : x ≠ srcCell := fun h => hr ⟨.inr 0, by rw [h]; rfl⟩
        have h2 : x ≠ bitsCell := fun h => hr ⟨.inr 2, by rw [h]; rfl⟩
        rw [Function.update_of_ne h1, Function.update_of_ne h2]
  rw [hF] at sF
  -- G: bits to unary K
  obtain ⟨tG, htG, sG⟩ := fuel_run (kValue M n) (Function.update S bitsCell (Nat.bits (kValue M n)))
    (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (by intro h; cases h)]; exact hS.hK)
    (by rw [Function.update_of_ne (by intro h; cases h)]; exact hS.hnat _ _)
    (by rw [Function.update_of_ne (by intro h; cases h)]; exact hS.hnat _ _)
  have hGfin : Function.update (Function.update (Function.update S bitsCell
      (Nat.bits (kValue M n))) bitsCell []) (aux .K) (List.replicate (kValue M n) true) =
      Function.update S (aux .K) (List.replicate (kValue M n) true) := by
    have hSb : Function.update S bitsCell [] = S := by
      funext x
      by_cases hx : x = bitsCell
      · subst hx
        rw [Function.update_self]
        exact (hS.hnat 2 0).symm
      · rw [Function.update_of_ne hx]
    rw [Function.update_idem, hSb]
  rw [hGfin] at sG
  -- compose
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs (clearProgram (region0 M)) fuelProgram
    0 (BitMachineRawSequence.leftLabel ()) ((), none) ((), none) (none, (false, false))
    (none, (false, false)) X5 _ _ _ _ sF sG
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs (projProgram M) (kS6 M)
    (.inl (.scan 0)) (BitMachineRawSequence.leftLabel 0) none none
    (((), none), (none, (false, false))) (((), none), (none, (false, false)))
    (Function.update S srcCell P) X5 _ _ _ sE r6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs (clearProgram (region3 (Drv M))) (kS5 M)
    0 (BitMachineRawSequence.leftLabel (.inl (.scan 0))) ((), none) ((), none)
    (none, (((), none), (none, (false, false)))) (none, (((), none), (none, (false, false))))
    (Function.update X2 srcCell P) (Function.update S srcCell P) _ _ _ sD r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs (kC M) (kS4 M)
    .scan (BitMachineRawSequence.leftLabel 0) none none
    (((), none), (none, (((), none), (none, (false, false)))))
    (((), none), (none, (((), none), (none, (false, false)))))
    X2 (Function.update X2 srcCell P) _ _ _ sC r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (machProgram (Drv M) 3) (kS3 M)
    (Drv M).start (BitMachineRawSequence.leftLabel .scan) (Drv M).initial v
    (none, (((), none), (none, (((), none), (none, (false, false))))))
    (none, (((), none), (none, (((), none), (none, (false, false))))))
    S1 X2 _ _ _ sB r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (kA M) (kS2 M)
    .scan (BitMachineRawSequence.leftLabel (Drv M).start) none none
    ((Drv M).initial, (none, (((), none), (none, (((), none), (none, (false, false)))))))
    ((Drv M).initial, (none, (((), none), (none, (((), none), (none, (false, false)))))))
    S S1 _ _ _ sA r2
  refine ⟨u1, ?_, r1⟩
  unfold kBound
  rw [← hPdef]
  rw [← hPdef] at htE
  omega

#print axioms k_run

end
end EthInapproximability.CurrentPaper.WeightedRawWords
