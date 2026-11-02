import CurrentAdditive.GaussPackedFetch64
import EthInapproximability.CurrentPaper.BitMachineEncoding

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPackedMachine64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def source : Stack := 61
def output : Stack := 38
def start : GaussPackedFetch64.Label :=
  BitMachineRawSequence.leftLabel (.inl (.scan 0))
def control : GaussPackedFetch64.Control :=
  (none, GaussPackedFetch64.fetchControl)

noncomputable def machine : BitMachine.Machine :=
  BitMachineEncoding.ofFinite source output start control
    GaussPackedFetch64.program

theorem initial_stack (word : List Bool) :
    GaussPackedFetch64.initialStack word =
      fun k : Stack => if k = source then word else [] := by
  unfold GaussPackedFetch64.initialStack GaussPackedParse64.frame
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  let S : Stack → List Bool := fun k => if k = source then word else []
  have hlocal : ∀ q : BitMachineBankCodec.Stack 3,
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk q = S (GaussPackedParse64.locate q) := by
    intro q
    cases q with
    | inl q => fin_cases q <;> simp [S, source, GaussPackedParse64.locate,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr q => fin_cases q <;> simp [S, source, GaussPackedParse64.locate,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  have hb := BitMachineStackEmbedding.bank_eq_self
    GaussPackedParse64.locate S
    (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) word [] []).stk hlocal
  have hf : BitMachineStackEmbedding.bank GaussPackedParse64.locate
      (fun _ : Stack => [])
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk =
      BitMachineStackEmbedding.bank GaussPackedParse64.locate S
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk := by
    funext k
    classical
    by_cases hk : ∃ q, GaussPackedParse64.locate q = k
    · simp [BitMachineStackEmbedding.bank, hk]
    · have hne : k ≠ source := by
        intro he
        apply hk
        refine ⟨.inr 0, ?_⟩
        change (61 : Stack) = k
        exact he.symm
      simp [BitMachineStackEmbedding.bank, hk, S, hne]
  rw [hf]
  exact hb

theorem raw_initial (word : List Bool) :
    rawInit source start control word = GaussPackedFetch64.initial word := by
  simp [rawInit, GaussPackedFetch64.initial, start, control, initial_stack]

theorem canonical_outputs {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    machine.OutputsWithin
      (GaussPackedFetch64.input B i j)
      (CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat (B i j)))
      (7 * ((GaussPackedFetch64.input B i j).length + 1) +
        GaussOneFetchProgram64.preparationClock
          (GaussPackedFetch64.parsedStack (GaussPackedFetch64.packet B i j))
          i.val j.val +
        140 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length + 1)^3 + 2) := by
  obtain ⟨t, ht, hh, ho⟩ := GaussPackedFetch64.canonical_fetch_bank38 B i j
  apply BitMachineEncoding.outputsWithin_of_raw_run
    source output start control GaussPackedFetch64.program
    (GaussPackedFetch64.input B i j)
    (CurrentAdditive.CodeDCodec.encodeRawRat
      (CurrentAdditive.GaussPhysical.rawOfRat (B i j))) t _ ht
  · rw [raw_initial]
    exact hh
  · rw [raw_initial]
    exact ho

#print axioms canonical_outputs

end CurrentAdditive.GaussPackedMachine64
