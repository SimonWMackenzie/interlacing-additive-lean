import CurrentAdditive.V40FirstPassingController
import CurrentAdditive.V40PredicateBody
import CurrentAdditive.V40DeterministicBoundedSearch

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace CurrentAdditive.V40PreparedSearchEngine

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open V39GeneratedConstruction V38Schedule
open CurrentAdditive.MinimumRatioContext

variable (M : BitMachine.Machine)
abbrev Stack := V40PredicateBody.Stack M
abbrev Bank := Stack M → List Bool
def low := V40PredicateBody.low M
def state (B : Bank M) (L : Nat) : Bank M :=
  V40FirstPassingController.bank B (low M 2) (low M 9) L
def program := V40FirstPassingController.program (V40PredicateBody.program M)
  (V40PredicateBody.entry M) (V40PredicateBody.initial M) (low M 2) (low M 9)
abbrev Label := V40FirstPassingController.Label (BitMachineRawSequence.Label
  (BitMachineRawSequence.Label V40ThreeFieldPacket.Label (MachineInvokeFull.LabelFull M)) Bool)
def entry : Label M := .inl (V40PredicateBody.entry M)
def initial := (V40PredicateBody.initial M, (none : Option Bool))
def requestCap (n m U : Nat) := 2 * (n + m + U) + 3
def testCap (C d n m U : Nat) := C * (2 ^ U + n + m + 1) ^ d
def stepCap (C d n m U : Nat) := 4 * requestCap n m U +
  MachineInvokeFull.uniformBound M (List.replicate (requestCap n m U) true) (testCap C d n m U) + 12

private theorem low_ne {a b : Fin 32} (h : a ≠ b) : low M a ≠ low M b := by
  intro he
  exact h (Fin.ext (congrArg (fun k : Stack M => k.val) he))

theorem body_run (p : SourceConstants) (C d : Nat) (B : Bank M) (n m L U : Nat)
    (h0 : B (low M 0) = List.replicate n true)
    (h1 : B (low M 1) = List.replicate m true)
    (hblank : ∀ i : Fin 6, B ⟨i.val + 3, by omega⟩ = [])
    (hscratch : B (low M 31) = [])
    (hhigh : ∀ i, B ((V40PredicateBody.callSlots M).machine i) = [])
    (hM : M.OutputsWithin
      (V40ThreeFieldPacket.bytes (List.replicate n true) (List.replicate m true) (List.replicate L true))
      [V40DeterministicBoundedSearch.test p n m L] (testCap C d n m U))
    (hLU : L ≤ U) :
    ∃ t ≤ stepCap M C d n m U,
      ((advance (V40PredicateBody.program M))^[t])
        (⟨some (V40PredicateBody.entry M), V40PredicateBody.initial M, state M B L⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, V40PredicateBody.initial M, Function.update (state M B L) (low M 9)
          [V40DeterministicBoundedSearch.test p n m L]⟩ := by
  obtain ⟨t, ht, hr⟩ := V40PredicateBody.run M (state M B L)
    (List.replicate n true) (List.replicate m true) (List.replicate L true)
    (V40DeterministicBoundedSearch.test p n m L) (testCap C d n m U)
    (by simpa [state, V40FirstPassingController.bank, low, V40PredicateBody.low, Fin.ext_iff] using h0)
    (by simpa [state, V40FirstPassingController.bank, low, V40PredicateBody.low, Fin.ext_iff] using h1)
    (by simp [state, V40FirstPassingController.bank, low, V40PredicateBody.low, Fin.ext_iff])
    (by
      intro i
      have hi := i.isLt
      have h2 : i.val + 3 ≠ 2 := by omega
      have h9 : i.val + 3 ≠ 9 := by omega
      simpa [state, V40FirstPassingController.bank, low, V40PredicateBody.low,
        Function.update_apply, Fin.ext_iff, h2, h9] using hblank i)
    (by simp [state, V40FirstPassingController.bank, low])
    (by simpa [state, V40FirstPassingController.bank, low, V40PredicateBody.low, Fin.ext_iff] using hscratch)
    (by
      intro i
      have h2 : 32 + i.val ≠ 2 := by omega
      have h9 : 32 + i.val ≠ 9 := by omega
      simpa [state, V40FirstPassingController.bank, low, V40PredicateBody.low,
        V40PredicateBody.callSlots, Function.update_apply, Fin.ext_iff, h2, h9] using hhigh i) hM
  have hlen : (V40ThreeFieldPacket.bytes (List.replicate n true) (List.replicate m true)
      (List.replicate L true)).length ≤ requestCap n m U := by
    simp [V40ThreeFieldPacket.bytes, V40ThreeFieldPacket.words,
      BitMachineBankCodec.encode_length, Fin.sum_univ_succ]
    dsimp [requestCap]
    omega
  refine ⟨t, ht.trans ?_, hr⟩
  unfold stepCap MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

theorem prepared_run (p : SourceConstants) (C d : Nat) (B : Bank M) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n)
    (h0 : B (low M 0) = List.replicate n true)
    (h1 : B (low M 1) = List.replicate m true)
    (hblank : ∀ i : Fin 6, B ⟨i.val + 3, by omega⟩ = [])
    (hscratch : B (low M 31) = [])
    (hhigh : ∀ i, B ((V40PredicateBody.callSlots M).machine i) = [])
    (hM : ∀ L, L ≤ publicUpperLog p floor n → M.OutputsWithin
      (V40ThreeFieldPacket.bytes (List.replicate n true) (List.replicate m true) (List.replicate L true))
      [V40DeterministicBoundedSearch.test p n m L] (testCap C d n m (publicUpperLog p floor n))) :
    ∃ t ≤ (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n + 1) *
        (stepCap M C d n m (publicUpperLog p floor n) + 1),
      ((advance (program M))^[t])
        (⟨some (entry M), initial M, state M B (V40DeterministicBoundedSearch.start floor n)⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, (V40PredicateBody.initial M, some true),
          state M B (publicLogFrom p floor n m hn hlow hdegree)⟩ := by
  have hs : V40DeterministicBoundedSearch.start floor n ≤ publicUpperLog p floor n := le_max_left _ _
  have hscan := V40DeterministicBoundedSearch.bounded_scan_success p floor n m hn hlow hdegree
  have hne : low M 2 ≠ low M 9 := low_ne M (by decide)
  have h := V40FirstPassingController.firstInRange_run (V40PredicateBody.program M)
    (V40PredicateBody.entry M) (V40PredicateBody.initial M) (low M 2) (low M 9) hne B
    (V40DeterministicBoundedSearch.test p n m) (stepCap M C d n m (publicUpperLog p floor n))
    (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n)
    (V40DeterministicBoundedSearch.start floor n) (publicLogFrom p floor n m hn hlow hdegree)
    hscan (by
      intro L hL1 hL2
      exact body_run M p C d B n m L (publicUpperLog p floor n) h0 h1 hblank hscratch hhigh
        (hM L (by omega)) (by omega))
  simpa only [program, entry, initial, state, V40FirstPassingController.run,
    V40FirstPassingController.cfg] using h

end CurrentAdditive.V40PreparedSearchEngine
