import CurrentAdditive.GaussWorkListHeaderJoin
import CurrentAdditive.GaussWorkListFuelCopy

/-! A fixed physical program turns a retained unary column count and prepared
matrix/free-column banks into the ordered, counted V2 coefficient work list. -/

namespace CurrentAdditive.GaussWorkListComplete

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussWorkListFuel.Bank

def workPackets {m k : Nat} (B : Fin m → Fin k → ℚ) (f : Fin k) :
    List (List Bool) :=
  (List.finRange k).map (GaussWorkItemContextSerialize.workPacket B f)

noncomputable def firstProgram := BitMachineRawSequence.program
  GaussWorkListFuelCopy.program GaussWorkListFuel.program
  (.inl ()) none (none, GaussWorkItemRoundComplete.control)

private abbrev InputLabel {α β : Type} (_ : α → β) : Type := α

private abbrev Ccopy := (none : Option Bool)
private noncomputable abbrev Cfuel :=
  ((none : Option Bool), GaussWorkItemRoundComplete.control)
private noncomputable abbrev Cfirst := (Ccopy, Cfuel)
private noncomputable abbrev Cheader :=
  (GaussWorkListHeaderJoin.C1, (none : Option Bool))

noncomputable def program := BitMachineRawSequence.program
  firstProgram GaussWorkListHeaderJoin.program
  (BitMachineRawSequence.leftLabel
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      GaussWorkListHeader.slots))
  Cfirst Cheader

noncomputable def start : InputLabel program := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)

noncomputable def control := (Cfirst, Cheader)

noncomputable def totalClock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) : Nat :=
  (2 * k + 2) + (k * (GaussWorkListFuel.maxRoundClock B f + 1) + 1) +
    GaussWorkListHeaderJoin.headerClock k + 2

theorem physical_work_list {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k)
    (S : Bank → List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hwidth : S ⟨3, by omega⟩ = List.replicate k true)
    (h5 : S ⟨5, by omega⟩ = [])
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = [])
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = [])
    (h13 : S ⟨13, by omega⟩ = [])
    (h14 : S ⟨14, by omega⟩ = [])
    (h15 : S ⟨15, by omega⟩ = [])
    (h24 : S ⟨24, by omega⟩ = [])
    (hblank : ∀ i, S (GaussWorkItemFrameContext.slots.machine i) = []) :
    ∃ t ≤ totalClock B f,
      ((advance program)^[t])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, control,
          Function.update
            (Function.update
              (GaussWorkListFuel.stateAt
                (Function.update S ⟨5, by omega⟩ (List.replicate k true))
                B f k)
              ⟨13, by omega⟩
              (SourceListMachineWriter.result false (List.replicate k true)))
            ⟨24, by omega⟩
            (SourceListEncoding.encode (workPackets B f))⟩ := by
  let S1 := Function.update S ⟨5, by omega⟩ (List.replicate k true)
  let S2 := GaussWorkListFuel.stateAt S1 B f k
  let fields := GaussWorkListSuffix.fieldsAt B f 0
  let header := SourceListMachineWriter.result false (List.replicate k true)
  obtain ⟨a, ha, hrunA⟩ := GaussWorkListFuelCopy.physical_fuel S k hwidth h5 h12
  have hS1 (z : Bank) (hz : z ≠ ⟨5, by omega⟩) : S1 z = S z := by
    simp [S1, hz]
  have hS1at (z : Bank) (hz5 : z ≠ ⟨5, by omega⟩)
      (hz24 : z ≠ ⟨24, by omega⟩) : S2 z = S z := by
    rw [show S2 z = S1 z from GaussWorkListFuel.stateAt_other S1 B f k z hz5 hz24]
    exact hS1 z hz5
  have hS2fixed (z : Bank) (h5z : z.val ≠ 5) (h24z : z.val ≠ 24) :
      S2 z = S z := by
    exact hS1at z
      (by intro h; exact h5z (by simpa using congrArg Fin.val h))
      (by intro h; exact h24z (by simpa using congrArg Fin.val h))
  have hS1mat : S1 ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B := by
    simpa [S1] using hmat
  have hS1f : S1 ⟨1, by omega⟩ = List.replicate f.val true := by
    simpa [S1] using hf
  have hS1fuel : S1 ⟨5, by omega⟩ = List.replicate k true := by simp [S1]
  have hS1fixed (z : Bank) (h5z : z.val ≠ 5) : S1 z = S z := by
    apply hS1 z
    intro h; exact h5z (congrArg Fin.val h)
  have hb : ∀ i, S1 (GaussWorkItemFrameContext.slots.machine i) = [] := by
    intro i
    have hv : (GaussWorkItemFrameContext.slots.machine i).val = 16 + i.val := rfl
    have hz : GaussWorkItemFrameContext.slots.machine i ≠
        (⟨5, by omega⟩ : Bank) := by
      intro he
      have he' := congrArg Fin.val he
      change 16 + i.val = 5 at he'
      omega
    rw [hS1 _ hz]
    exact hblank i
  obtain ⟨b, hbclock, hrunB⟩ := GaussWorkListFuel.physical_fields B f S1
    hS1mat hS1f hS1fuel
    ((hS1fixed _ (by norm_num)).trans h6)
    ((hS1fixed _ (by norm_num)).trans h7)
    ((hS1fixed _ (by norm_num)).trans h8)
    ((hS1fixed _ (by norm_num)).trans h9)
    ((hS1fixed _ (by norm_num)).trans h10)
    ((hS1fixed _ (by norm_num)).trans h11)
    ((hS1fixed _ (by norm_num)).trans h12)
    ((hS1fixed _ (by norm_num)).trans h13)
    ((hS1fixed _ (by norm_num)).trans h14)
    ((hS1fixed _ (by norm_num)).trans h15)
    ((hS1fixed _ (by norm_num)).trans h24) hb
  have hswidth : S2 ⟨3, by omega⟩ = List.replicate k true :=
    (hS2fixed ⟨3, by omega⟩ (by norm_num) (by norm_num)).trans hwidth
  have hs13 : S2 ⟨13, by omega⟩ = [] :=
    (hS2fixed ⟨13, by omega⟩ (by norm_num) (by norm_num)).trans h13
  have hs14 : S2 ⟨14, by omega⟩ = [] :=
    (hS2fixed ⟨14, by omega⟩ (by norm_num) (by norm_num)).trans h14
  have hs15 : S2 ⟨15, by omega⟩ = [] :=
    (hS2fixed ⟨15, by omega⟩ (by norm_num) (by norm_num)).trans h15
  have hs24 : S2 ⟨24, by omega⟩ = fields := by
    simpa [S2, fields] using GaussWorkListFuel.stateAt_output S1 B f k
  have hsblank : ∀ i, S2 (GaussWorkListHeader.slots.machine i) = [] := by
    intro i
    have hv : (GaussWorkListHeader.slots.machine i).val = 16 + i.val := rfl
    have hi : i.val < 8 := by
      simpa only [show (SourceListMachineWriter.framingMachine false).stackCount = 8
        from rfl] using i.isLt
    rw [hS2fixed _ (by omega) (by omega)]
    have heq : GaussWorkListHeader.slots.machine i =
        GaussWorkItemFrameContext.slots.machine i := Fin.ext (by rfl)
    rw [heq]
    exact hblank i
  obtain ⟨c, hc, hrunC⟩ :=
    GaussWorkListHeaderJoin.physical_header_and_prepend S2 k fields
      hswidth hs13 hs14 hs15 hs24 hsblank
  have hpacket : header ++ fields =
      SourceListEncoding.encode (workPackets B f) := by
    simp [header, fields, SourceListMachineWriter.result,
      SourceListEncoding.encode, GaussWorkListSuffix.fields_at_zero,
      workPackets]
  obtain ⟨u, hu, hrunAB⟩ := BitMachineRawSequence.runs
    GaussWorkListFuelCopy.program GaussWorkListFuel.program
    BitMachineCopy.Label.scan (.inl ()) none none
    (none, GaussWorkItemRoundComplete.control)
    (none, GaussWorkItemRoundComplete.control)
    S S1 S2 a b
    (by simpa [S1] using hrunA) (by simpa [S2] using hrunB)
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    firstProgram GaussWorkListHeaderJoin.program
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
        GaussWorkListHeader.slots))
    (none, (none, GaussWorkItemRoundComplete.control))
    (none, (none, GaussWorkItemRoundComplete.control))
    (GaussWorkListHeaderJoin.C1, none)
    (GaussWorkListHeaderJoin.C1, none)
    S S2
    (Function.update (Function.update S2 ⟨13, by omega⟩ header)
      ⟨24, by omega⟩ (header ++ fields))
    u c (by simpa [firstProgram] using hrunAB)
    (by simpa [header, fields] using hrunC)
  refine ⟨t, ?_, ?_⟩
  · dsimp [totalClock]
    omega
  · simpa [program, start, control, S1, S2, header, hpacket] using hrun

#print axioms physical_work_list

end CurrentAdditive.GaussWorkListComplete
