import Paper2.BrFin
import Paper2.CopyList
import Paper2.HeaderJoin
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Lane a-bridge-owner-1, segment 2 (reformulated, see CHECKPOINT): the local
cut controller on the bank `KC = JF ⊕ (out ⊕ in)`. It copies the three input
cells into the graph-front packet cells, runs the segment-1 controller
(front, public counts, exact prefix cut, repack), copies the three packet
cells into the output cells and clears every other cell. The exit bank is
stated exactly: output cells `![encode g, 1^k, word.take D]`, all else empty.
Every stage and handoff is charged; the clear is charged through the admitted
stack-growth bound. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

abbrev KC := FullFront.JF ⊕ (Fin 3 ⊕ Fin 3)
instance instDecKC : DecidableEq KC :=
  @instDecidableEqSum _ _ FullFront.instDecJF inferInstance

def inJ : FullFront.JF ↪ KC := ⟨Sum.inl, Sum.inl_injective⟩
def jc (x : FullFront.JF) : KC := .inl x
def outC (i : Fin 3) : KC := .inr (.inl i)
def inC (i : Fin 3) : KC := .inr (.inr i)

def mk3 (x y z : KC) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Fin 3 ↪ KC :=
  ⟨![x, y, z], by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd h hxy | exact absurd h hxz | exact absurd h hyz
      | exact absurd h.symm hxy | exact absurd h.symm hxz | exact absurd h.symm hyz⟩

def inCopy (i : Fin 3) : Fin 3 ↪ KC :=
  mk3 (inC i) (jc (FullFront.pk i)) (jc FullFront.zs)
    (by simp [inC, jc]) (by simp [inC, jc]) (by simp [jc, FullFront.pk, FullFront.zs])

def outCopy (i : Fin 3) : Fin 3 ↪ KC :=
  mk3 (jc (FullFront.pk i)) (outC i) (jc FullFront.zs)
    (by simp [outC, jc]) (by simp [jc, FullFront.pk, FullFront.zs]) (by simp [outC, jc])

def inList : List (Fin 3 ↪ KC) := [inCopy 0, inCopy 1, inCopy 2]
def outList : List (Fin 3 ↪ KC) := [outCopy 0, outCopy 1, outCopy 2]

def nJ : ℕ := Fintype.card FullFront.JF

def eJ (x : FullFront.JF) : Fin nJ := Fintype.equivFin FullFront.JF x

def clearCells : Fin (nJ + 3) → KC := fun j =>
  if h : j.val < nJ then jc ((Fintype.equivFin FullFront.JF).symm ⟨j.val, h⟩)
  else inC ⟨j.val - nJ, by omega⟩

theorem clearCells_inj : Function.Injective clearCells := by
  intro i j h
  unfold clearCells at h
  by_cases hi : i.val < nJ <;> by_cases hj : j.val < nJ <;>
    simp only [hi, hj, dite_true, dite_false] at h
  · have h' := Sum.inl_injective h
    have := (Fintype.equivFin FullFront.JF).symm.injective h'
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · simp [jc, inC] at h
  · simp [jc, inC] at h
  · have h' := Sum.inr_injective (Sum.inr_injective h)
    have := congrArg Fin.val h'
    simp only at this
    exact Fin.ext (by omega)

theorem clearCells_jc (x : FullFront.JF) :
    ∃ j, clearCells j = jc x := by
  refine ⟨⟨(eJ x).val, by have := (eJ x).isLt; omega⟩, ?_⟩
  have hl : (eJ x).val < nJ := (eJ x).isLt
  simp only [clearCells, hl, dite_true]
  congr 1
  simp [eJ]

theorem clearCells_inC (i : Fin 3) :
    ∃ j, clearCells j = inC i := by
  refine ⟨⟨nJ + i.val, by omega⟩, ?_⟩
  have hl : ¬ (nJ + i.val < nJ) := by omega
  simp only [clearCells, hl, dite_false]
  congr 1
  ext
  simp

theorem clearCells_ne_out (j : Fin (nJ + 3)) (i : Fin 3) : clearCells j ≠ outC i := by
  unfold clearCells
  split <;> simp [jc, inC, outC]

theorem clearFrom_eq (W : KC → List Bool) :
    ClearAll.clearFrom clearCells 0 W =
      fun z => match z with
        | .inr (.inl i) => W (outC i)
        | _ => [] := by
  funext z
  rcases z with x | i | i
  · obtain ⟨j, hj⟩ := clearCells_jc x
    simp only [ClearAll.clearFrom]
    rw [if_pos ⟨j, Nat.zero_le _, hj⟩]
  · simp only [ClearAll.clearFrom]
    rw [if_neg]
    · rfl
    · rintro ⟨j, -, hj⟩
      exact clearCells_ne_out j i hj
  · obtain ⟨j, hj⟩ := clearCells_inC i
    simp only [ClearAll.clearFrom]
    rw [if_pos ⟨j, Nat.zero_le _, hj⟩]

def liftedPacket (a b Δ : ℕ) := fun l => stackStmt inJ (packetProgram a b Δ l)

def packetCtl0 (a b Δ : ℕ) : ctlT (packetProgram a b Δ) :=
  ((FullFront.fullCtl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
    ((none : Option Bool), (none : Option Bool)))

def tailProgram :=
  BitMachineRawSequence.program (CopyList.program outList) (ClearAll.prog clearCells)
    (⟨0, by omega⟩ : Fin (nJ + 3 + 1)) (CopyList.initialControl outList) (none : Option Bool)

def midProgram (a b Δ : ℕ) :=
  BitMachineRawSequence.program (liftedPacket a b Δ) tailProgram
    (BitMachineRawSequence.leftLabel (CopyList.first outList)) (packetCtl0 a b Δ)
    (CopyList.initialControl outList, (none : Option Bool))

def cutProgram (a b Δ : ℕ) :=
  BitMachineRawSequence.program (CopyList.program inList) (midProgram a b Δ)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))))
    (CopyList.initialControl inList)
    (packetCtl0 a b Δ, (CopyList.initialControl outList, (none : Option Bool)))

def cutStart (a b Δ : ℕ) : labelT (cutProgram a b Δ) :=
  BitMachineRawSequence.leftLabel (CopyList.first inList)

def cutCtl0 (a b Δ : ℕ) : ctlT (cutProgram a b Δ) :=
  (CopyList.initialControl inList,
    (packetCtl0 a b Δ, (CopyList.initialControl outList, (none : Option Bool))))

/-- The start bank on `KC`: the three input cells, everything else empty. -/
def startKC (X : Fin 3 → List Bool) : KC → List Bool :=
  fun z => match z with
    | .inr (.inr i) => X i
    | _ => []

/-- The exit bank on `KC`: the three output cells, everything else empty. -/
def exitKC (Y : Fin 3 → List Bool) : KC → List Bool :=
  fun z => match z with
    | .inr (.inl i) => Y i
    | _ => []

end

end Paper2.ABridge
