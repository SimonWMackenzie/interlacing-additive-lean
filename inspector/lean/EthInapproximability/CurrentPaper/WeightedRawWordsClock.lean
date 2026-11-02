import EthInapproximability.CurrentPaper.WeightedRawWordsFuel
import EthInapproximability.CurrentPaper.ClockRuntime

/-! # S5: the k fuel from master N

For a fixed source machine `M` (for the paper, `CutoffBitMachine.actualMachine c A d`,
whose `clock` is `actualClock c A d` by definition), with `D := ClockRuntime.machine M`:
copy `N` into D's input (region `nat 3`), run the embedded production driver
(`ClockRuntime.outputs`), copy its packet into the projection source, clear
region 3 (existential residue, charged by `run_growth`), run the embedded
production `BankFieldProjection.program (ClockRuntime.counterField M)` (region
`nat 0` plus `nat 2 1`, `nat 2 2`, output `bitsCell`), clear its fields, then
`fuel_run`: master `K` ends as unary `SlowClock.repetitions (clock M) n`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

def machSlots (D : BitMachine.Machine) (r : Fin 4) : Fin D.stackCount ↪ Global :=
  ⟨fun i => aux (.nat r i.val), by
    intro a b h
    simp only [aux, Sum.inr.injEq, Aux.nat.injEq, true_and] at h
    exact Fin.ext h⟩

def machProgram (D : BitMachine.Machine) (r : Fin 4) :=
  fun l => stackStmt (machSlots D r) (D.program l)

theorem mach_run (D : BitMachine.Machine) (r : Fin 4) (input output : List Bool) (time : ℕ)
    (h : D.OutputsWithin input output time) (G : Global → List Bool)
    (hG : ∀ i : Fin D.stackCount, G (aux (.nat r i.val)) = if i = D.input then input else []) :
    ∃ t ≤ time, ∃ (v : Fin D.controlCount) (F : Fin D.stackCount → List Bool),
      ((advance (machProgram D r))^[t])
        (⟨some D.start, D.initial, G⟩ : TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, v, bank (machSlots D r) G F⟩ ∧ F D.output = output ∧
        ∀ i, (F i).length ≤ input.length + BitMachineStackGrowth.perStep D.program * time := by
  obtain ⟨t, ht, hl, ho⟩ := h
  have hstep : D.step = advance D.program := rfl
  have hrun : ((advance D.program)^[t]) (D.init input) =
      ⟨none, (D.run t (D.init input)).var, (D.run t (D.init input)).stk⟩ := by
    have e : D.run t (D.init input) = ((advance D.program)^[t]) (D.init input) := by
      unfold BitMachine.Machine.run; rw [hstep]
    rw [← e]
    rcases hc : D.run t (D.init input) with ⟨l, v, S⟩
    rw [hc] at hl
    cases hl
    rfl
  refine ⟨t, ht, (D.run t (D.init input)).var, (D.run t (D.init input)).stk, ?_, ho, ?_⟩
  · have h := region_run (machSlots D r) D.program _ _ t hrun G
      (by intro k; rw [show machSlots D r k = aux (.nat r k.val) from rfl, hG]; rfl)
    exact h
  · intro i
    have hg := BitMachineStackGrowth.run_growth D.program (D.init input) t i
    rw [hrun] at hg
    have hi : ((D.init input).stk i).length ≤ input.length := by
      show (if i = D.input then input else []).length ≤ _
      split <;> simp
    have hm : BitMachineStackGrowth.perStep D.program * t ≤
        BitMachineStackGrowth.perStep D.program * time := Nat.mul_le_mul_left _ ht
    simp only at hg
    omega


/-! ## Clearing a region that contains every embedded cell -/

theorem cleared_bank_region {K : Type*} [DecidableEq K] {m : ℕ} (cells : Fin m → Global)
    (ι : K ↪ Global) (G : Global → List Bool) (F : K → List Bool)
    (hall : ∀ k, ∃ i, cells i = ι k) :
    BitMachineClearBank.cleared cells (bank ι G F) = BitMachineClearBank.cleared cells G := by
  funext x
  unfold BitMachineClearBank.cleared
  split_ifs with hc
  · rfl
  · apply bank_outside
    rintro ⟨k, rfl⟩
    exact hc (hall k)

/-! ## The embedded counter projection -/

def projSlots (M : BitMachine.Machine) :
    BitMachineBankCodec.Stack (ClockStepEncoded.width M) ↪ Global where
  toFun
    | .inl k => aux (.nat 0 k.val)
    | .inr 0 => aux (.nat 2 1)
    | .inr 1 => aux (.nat 2 2)
    | .inr 2 => bitsCell
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · simp only [aux, Sum.inr.injEq, Aux.nat.injEq, true_and] at h
      exact congrArg Sum.inl (Fin.ext h)
    · fin_cases y <;> simp_all [aux, bitsCell]
    · fin_cases x <;> simp_all [aux, bitsCell]
    · fin_cases x <;> fin_cases y <;> simp_all [aux, bitsCell]

def projProgram (M : BitMachine.Machine) :=
  fun l => stackStmt (projSlots M) (BankFieldProjection.program (ClockRuntime.counterField M) l)

def region3 (D : BitMachine.Machine) : Fin D.stackCount → Global := fun i => aux (.nat 3 i.val)
def region0 (M : BitMachine.Machine) : Fin (ClockStepEncoded.width M) → Global :=
  fun i => aux (.nat 0 i.val)

theorem region3_injective (D : BitMachine.Machine) : Function.Injective (region3 D) := by
  intro a b h
  simp only [region3, aux, Sum.inr.injEq, Aux.nat.injEq, true_and] at h
  exact Fin.ext h

theorem region0_injective (M : BitMachine.Machine) : Function.Injective (region0 M) := by
  intro a b h
  simp only [region0, aux, Sum.inr.injEq, Aux.nat.injEq, true_and] at h
  exact Fin.ext h

/-- Hypotheses on the start bank of the k stage: masters untouched, all
S5 scratch regions and `K` empty, `N = unary n`. -/
structure KReady (S : Global → List Bool) (n : ℕ) : Prop where
  hN : S (aux .N) = List.replicate n true
  hnat : ∀ r i, S (aux (.nat r i)) = []
  hK : S (aux .K) = []
  hcs : S (aux .cs) = []

def kValue (M : BitMachine.Machine) (n : ℕ) : ℕ :=
  SlowClock.repetitions (CutoffBitMachine.clock M) n

theorem proj_stage (M : BitMachine.Machine) (n : ℕ) (S : Global → List Bool)
    (hS : KReady S n) :
    let P := ClockRuntime.output M (List.replicate n true)
    ∃ t ≤ (2 * ClockStepEncoded.width M + 3) * (P.length + 1) + 1,
      ((advance (projProgram M))^[t])
        (⟨some (.inl (.scan 0)), none, Function.update S (aux (.nat 2 1)) P⟩ :
          TM2.Cfg (fun _ : Global => Bool) (BankFieldProjection.Label _)
            BitMachineBankCodec.Control) =
        ⟨none, none, bank (projSlots M) (Function.update S (aux (.nat 2 1)) P)
          (BitMachineBankCodec.contents
            (Function.update (ClockStepEncoded.toBank M (ClockInputPreparation.readyBank M
              [(ClockRuntime.state M (List.replicate n true) n).active]
              (List.replicate n true) (Nat.bits (kValue M n)))) (ClockRuntime.counterField M) [])
            [] [] (Nat.bits (kValue M n)))⟩ := by
  intro P
  set B0 := ClockStepEncoded.toBank M (ClockInputPreparation.readyBank M
    [(ClockRuntime.state M (List.replicate n true) n).active]
    (List.replicate n true) (Nat.bits (kValue M n))) with hB0
  have hP : P = BitMachineBankCodec.encode B0 := by
    show ClockRuntime.output M (List.replicate n true) = _
    rw [ClockRuntime.output_counter]
    simp only [List.length_replicate]
    rfl
  have hd : BitMachineBankCodec.decode (ClockStepEncoded.width M) P = some B0 := by
    rw [hP, BitMachineBankCodec.decode_encode]
  have hj : B0 (ClockRuntime.counterField M) = Nat.bits (kValue M n) := by
    rw [hB0]
    exact ClockPacketState.packet_counter M _ _ _
  obtain ⟨t, ht, hr⟩ := BankFieldProjection.valid_run (ClockRuntime.counterField M) P B0 hd
  refine ⟨t, ht, ?_⟩
  have hnat' : ∀ r i, S (Sum.inr (Aux.nat r i)) = [] := hS.hnat
  have h := region_run (projSlots M) (BankFieldProjection.program (ClockRuntime.counterField M))
    _ _ t hr (Function.update S (aux (.nat 2 1)) P)
    (by
      intro k
      rcases k with k | k
      · simp [BankFieldProjection.cfg, BitMachineBankCodec.contents, projSlots, aux,
          hnat']
      · fin_cases k <;>
          simp [BankFieldProjection.cfg, BitMachineBankCodec.contents, projSlots, aux,
            bitsCell, hnat'])
  rw [hj] at h
  exact h

end

end EthInapproximability.CurrentPaper.WeightedRawWords

namespace EthInapproximability.CurrentPaper.WeightedRawWords
open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

#print axioms mach_run
#print axioms proj_stage

end
end EthInapproximability.CurrentPaper.WeightedRawWords
