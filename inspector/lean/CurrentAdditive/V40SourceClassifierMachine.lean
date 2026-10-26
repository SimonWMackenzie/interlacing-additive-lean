import CurrentAdditive.V40SourceClassifierResources
import CurrentAdditive.V40RawClassifierClock

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentAdditive.V40SourceClassifier
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V38Schedule V39PublicSchedule
local instance : DecidableEq V40RawMidpointRequest.Raw := Classical.decEq _

abbrev gPort := V40RawRequestPacket.graphPort
abbrev kPort := V40RawRequestPacket.kPort
abbrev tPort := V40RawRequestPacket.tapePort
abbrev hgk := V40RawRequestPacket.graph_ne_k
abbrev hgt := V40RawRequestPacket.graph_ne_tape
abbrev hkt := V40RawRequestPacket.k_ne_tape

def bankWidth : ℕ := V39ThreePortFrame.workCount gPort kPort tPort

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def bankWord (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :=
  BitMachineBankCodec.encode (fun i => V39ThreePortFrame.inputBank gPort kPort tPort
    (EncodedGraph.encode (graph D B density cutoff hcutoff w))
    (List.replicate (gap density cutoff hcutoff w) true)
    (tape.take (blockLength density cutoff w))
    ((V39TypedPacket.number gPort kPort tPort hgk hgt hkt).symm i))

def classifierBlock (C : SelectedTape.Algorithm) (density cutoff : ℕ) (w tape : List Bool) :=
  (tape.take (2^(V40RandomizedETHEndpoint.classifierBlockExponent C)*
    blockLength density cutoff w)).drop (blockLength density cutoff w)

def frontWord (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w tape : List Bool) :=
  EncodedComplexity.pair (bankWord D B density cutoff hcutoff w tape)
    (classifierBlock C density cutoff w tape)

theorem frontWord_eq (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w tape : List Bool) :
    V39SourceFront.cutWord D B gPort kPort tPort hgk hgt hkt (density+2) cutoff
      (V40RandomizedETHEndpoint.classifierBlockExponent C) hcutoff w tape =
    frontWord D B C density cutoff hcutoff w tape := by
  have hΦ := V39SourceFront.formula_large hcutoff (routed density cutoff hcutoff w)
    (AEth4.routed4_variables (density+2) cutoff w)
  change EncodedComplexity.pair
    (BitMachineBankCodec.encode (V39SourceFront.framedBank D B gPort kPort tPort hgk hgt hkt
      hcutoff (EncodedCNF.encode (routed density cutoff hcutoff w).val)
      (tape.take (blockLength density cutoff w)))) _ = _
  unfold V39SourceFront.framedBank V39SourceFront.graph V39SourceFront.gap
  rw [hΦ]
  rfl

def sourceClock (a e p : ℕ) (C : SelectedTape.Algorithm) (density cutoff : ℕ)
    (w : List Bool) :=
  AEth5.twoCutTime (density+2) cutoff (V40RandomizedETHEndpoint.classifierBlockExponent C) w+
    30*V39SourceFront.cutScale (density+2) cutoff
      (V40RandomizedETHEndpoint.classifierBlockExponent C) w+30+
    a*(V39SourceFront.cutScale (density+2) cutoff
      (V40RandomizedETHEndpoint.classifierBlockExponent C) w+1)^e*(1+2*p)

theorem source_exists (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    ∃ (M : BitMachine.Machine) (a e p : ℕ), ∀ w tape : List Bool,
      M.OutputsWithin (EncodedComplexity.pair w tape)
        (frontWord D B C density cutoff hcutoff w tape) (sourceClock a e p C density cutoff w) := by
  obtain ⟨M,a,e,p,h⟩ := V39SourceFront.all_input_cut_framed D B gPort kPort tPort hgk hgt hkt
    (density+2) cutoff (V40RandomizedETHEndpoint.classifierBlockExponent C) hcutoff
  refine ⟨M,a,e,p,?_⟩
  intro w tape
  have hw := h w tape
  rw [frontWord_eq D B C density cutoff hcutoff w tape] at hw
  exact hw

def frontMachine (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  Classical.choose (source_exists D B C density cutoff hcutoff)
def frontA (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  Classical.choose (Classical.choose_spec (source_exists D B C density cutoff hcutoff))
def frontE (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (source_exists D B C density cutoff hcutoff)))
def frontP (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (source_exists D B C density cutoff hcutoff))))

theorem front_runs (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w tape : List Bool) :
    (frontMachine D B C density cutoff hcutoff).OutputsWithin (EncodedComplexity.pair w tape)
      (frontWord D B C density cutoff hcutoff w tape)
      (sourceClock (frontA D B C density cutoff hcutoff) (frontE D B C density cutoff hcutoff)
        (frontP D B C density cutoff hcutoff) C density cutoff w) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (source_exists D B C density cutoff hcutoff)))) w tape

def machine (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  BitMachineComposition.composition (frontMachine D B C density cutoff hcutoff)
    (V40RawRequestPacket.classifiedMachine C)

def sampledBits (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :=
  V40SourceBlockView.bits (precision D B density cutoff hcutoff w)
    (reservation D B density cutoff hcutoff w) (tape.take (blockLength density cutoff w))

def residual (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :=
  (tape.take (blockLength density cutoff w)).drop
    (precision D B density cutoff hcutoff w*reservation D B density cutoff hcutoff w)

def output (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w tape : List Bool) :=
  let req := request D B C density cutoff hcutoff hmin w
    (sampledBits D B density cutoff hcutoff w tape)
  C.output req ((classifierBlock C density cutoff w tape).take (C.tapeLength req))

def bankInputCap (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  bankWidth+2*((EncodedGraph.encode (graph D B density cutoff hcutoff w)).length+
    gap density cutoff hcutoff w+blockLength density cutoff w)+3

def frontWordCap (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w : List Bool) :=
  2*bankInputCap D B density cutoff hcutoff w+1+
    2^(V40RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w

def sizeCap (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w : List Bool) :=
  bankInputCap D B density cutoff hcutoff w+
    V39WRaw.clock (graph D B density cutoff hcutoff w) (gap density cutoff hcutoff w)+
    sampleSide (Nat.clog 2 (graph D B density cutoff hcutoff w).vertices)
      (gap density cutoff hcutoff w)^2+
    2^(V40RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w+1

/-- This clock depends only on the routed formula and fixed programs,
including every source/cut handoff and the actual caller/classifier cap. -/
def time (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (w : List Bool) :=
  sourceClock (frontA D B C density cutoff hcutoff) (frontE D B C density cutoff hcutoff)
    (frontP D B C density cutoff hcutoff) C density cutoff w+
    2*frontWordCap D B C density cutoff hcutoff w+2+
    V40RawClassifierClock.cap C (sizeCap D B C density cutoff hcutoff w)

end
end CurrentAdditive.V40SourceClassifier
