import CurrentAdditive.GaussContextSpec
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussListContext

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.BitMachine

/-- Total semantic response for a packed cell packet. Malformed packets
receive the empty word. This is a specification, not an inferred program. -/
def callbackResult (input : List Bool) : List Bool :=
  let value : Option ℚ := do
    let S ← BitMachineBankCodec.decode 12 input
    let flag ← if S 0 = [true] then some true else
      if S 0 = [false] then some false else none
    let current ← decodeRawRat (S 1)
    let column ← decodeRawRat (S 2)
    let row ← decodeRawRat (S 3)
    let pivot ← decodeRawRat (S 4)
    pure (cellPacketValue flag current column row pivot)
  match value with
  | none => []
  | some q => encodeRawRat (rawOfRat q)

theorem callbackResult_packet (x : CellContext)
    (hcurrent : x.current.Valid) (hcolumn : x.column.Valid)
    (hrow : x.row.Valid) (hpivot : x.pivot.Valid) :
    callbackResult (packet x) = encodeRawRat (rawOfRat (value x)) := by
  cases x with
  | mk flag current column row pivot =>
      cases flag <;>
        simp [callbackResult, packet, cellPacket, cellBank,
          BitMachineBankCodec.decode_encode,
          decodeRawRat_encodeRawRat, hcurrent, hcolumn, hrow, hpivot,
          value, cellPacketValue]

theorem callbackResult_typedContext {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    callbackResult (packet (typedContext B r c i j)) =
      encodeRawRat (rawOfRat
        (CurrentAdditive.SequentialTotality.clearTyped B r c i j)) := by
  rw [callbackResult_packet]
  · rw [typedContext_value]
  all_goals simp [typedContext, rawOfRat_valid]

/-- The inherited physical list loop maps the *already constructed*
canonical V2 context list once a concrete cell machine is supplied. This
does not assert a machine producing the context list from a raw matrix. -/
theorem mapped_contexts {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (M : Machine) (bound : List Bool → Nat)
    (hcell : ∀ x ∈ typedContexts B r c,
      M.OutputsWithin (packet x) (callbackResult (packet x))
        (bound (packet x))) :
    (SourceListMachineOuterFramed.machine M).OutputsWithin
      (encodedTypedContexts B r c)
      (SourceListEncoding.encode
        ((typedContexts B r c).map (fun x =>
          encodeRawRat (rawOfRat (value x)))))
      (SourceListMachineOuter.canonicalBound
        (SourceListMachineOuterFramed.itemMachine M)
        ((typedContexts B r c).map packet)
        (SourceListMachineOuterFramed.framedOutput callbackResult)
        (SourceListMachineOuterFramed.framedBound callbackResult bound)) := by
  have hitems : ∀ item ∈ (typedContexts B r c).map packet,
      M.OutputsWithin item (callbackResult item) (bound item) := by
    intro item hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact hcell x hx
  have h := SourceListMachineOuterFramed.outputsWithin M
    ((typedContexts B r c).map packet) callbackResult bound hitems
  have hout : ((typedContexts B r c).map packet).map callbackResult =
      (typedContexts B r c).map
        (fun x => encodeRawRat (rawOfRat (value x))) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, j, rfl⟩ := (typedContexts_mem B r c x).mp hx
    simpa only [Function.comp_def, typedContext_value] using
      callbackResult_typedContext B r c i j
  simpa only [encodedTypedContexts, hout] using h

#print axioms callbackResult_packet
#print axioms callbackResult_typedContext
#print axioms mapped_contexts

end CurrentAdditive.GaussListContext
