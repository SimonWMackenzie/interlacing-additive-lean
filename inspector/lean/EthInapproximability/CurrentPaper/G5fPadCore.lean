import EthInapproximability.CurrentPaper.G5eYk
import EthInapproximability.CurrentPaper.G5cCounters
import EthInapproximability.CurrentPaper.U4PostPadWriter

/-!
# The pad join after the `y_k` emission (private lane owner:b-g5-6, segment 2, generic core)

A NEW module (the unchecked owner-5 draft `G5ePadCore.lean` is not imported; its design is reused and
its failing proofs are replaced). Bank `HP = G5eYkCore.H8 ⊕ (HW ⊕ Unit)`: the `y_k` bank `H8`, the
admitted pad writer's bank `HW = MatrixTableWriter.Stack 10`, and one cell `pc` holding unary `p`
(an INPUT of the theorem, like `k`).

ONE fixed program `padCore A a₀ v₀ = liftY A ; (prep ; liftW writer)` with charged handoffs
(`BitMachineRawSequence.program`), generic in the first-stage program `A` over `H8`:
1. `A` on the `H8` region (the instance in `G5fPad` is the owner-5 `y_k` program);
2. `prep` = three charged copies (consumer raw word 3 = unary rows, raw word 4 = unary columns,
   cell 55 = the row-major word, into writer cells 0, 1, 2; each via the blank temporary `zc 1`)
   then the frozen owner-3 `G5cCounters.countersProgram` (unary `2^p` into the writer's `rows` and
   `cols` registers from unary `p` in `pc`, writer cells 3, 4 as blank scratch);
3. the admitted padded writer `MatrixTableWriter.program Unit4Post.PadWriter.entryProgram …` on the
   `HW` region, which writes `FinalPadding.table R p hm hr` into the writer's `output` register.
The exit bank is stated exactly: the `H8` bank of `A`'s exit unchanged, the writer bank
`ready (persistentBank m r (rowMajor R)) (2^p) (2^p) 0 0 0 0 [] (table R p hm hr)`, `pc` unchanged.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5fPadCore

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev HW := MatrixTableWriter.Stack 10
abbrev HP := G5eYkCore.H8 ⊕ (HW ⊕ Unit)

instance decHW : DecidableEq HW := inferInstance
instance decHP : DecidableEq HP := inferInstance

open Turing BitMachineEncoding BitMachineStackEmbedding

def iY : G5eYkCore.H8 ↪ HP := ⟨Sum.inl, Sum.inl_injective⟩
def iW : HW ↪ HP := ⟨fun x => Sum.inr (Sum.inl x), by
  intro a b h
  simpa using h⟩
abbrev pc : HP := .inr (.inr ())

def extP (Y : G5eYkCore.H8 → List Bool) (W : HW → List Bool) (u : List Bool) : HP → List Bool :=
  Sum.elim Y (Sum.elim W (fun _ => u))

theorem bank_extY (X Y : G5eYkCore.H8 → List Bool) (W : HW → List Bool) (u : List Bool) :
    bank iY (extP X W u) Y = extP Y W u := by
  funext x
  rcases x with x | x
  · exact bank_at iY (extP X W u) Y x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem bank_extW (Y : G5eYkCore.H8 → List Bool) (X W : HW → List Bool) (u : List Bool) :
    bank iW (extP Y X u) W = extP Y W u := by
  funext x
  rcases x with x | x | x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl
  · exact bank_at iW (extP Y X u) W x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

def liftY {L V : Type} (P : L → TM2.Stmt (fun _ : G5eYkCore.H8 => Bool) L V) :
    L → TM2.Stmt (fun _ : HP => Bool) L V :=
  fun l => stackStmt iY (P l)

def liftW {L V : Type} (P : L → TM2.Stmt (fun _ : HW => Bool) L V) :
    L → TM2.Stmt (fun _ : HP => Bool) L V :=
  fun l => stackStmt iW (P l)

theorem liftY_run {L V : Type} (P : L → TM2.Stmt (fun _ : G5eYkCore.H8 => Bool) L V)
    (l l' : Option L) (v v' : V) (X Y : G5eYkCore.H8 → List Bool) (W : HW → List Bool)
    (u : List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : G5eYkCore.H8 => Bool) L V) = ⟨l', v', Y⟩) :
    ((advance (liftY P))^[t]) (⟨l, v, extP X W u⟩ : TM2.Cfg (fun _ : HP => Bool) L V) =
      ⟨l', v', extP Y W u⟩ := by
  have r := WeightedRawWords.region_run iY P ⟨l, v, X⟩ ⟨l', v', Y⟩ t h (extP X W u) (fun _ => rfl)
  dsimp only at r
  rw [bank_extY] at r
  exact r

theorem liftW_run {L V : Type} (P : L → TM2.Stmt (fun _ : HW => Bool) L V)
    (l l' : Option L) (v v' : V) (Y : G5eYkCore.H8 → List Bool) (X W : HW → List Bool)
    (u : List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : HW => Bool) L V) = ⟨l', v', W⟩) :
    ((advance (liftW P))^[t]) (⟨l, v, extP Y X u⟩ : TM2.Cfg (fun _ : HP => Bool) L V) =
      ⟨l', v', extP Y W u⟩ := by
  have r := WeightedRawWords.region_run iW P ⟨l, v, X⟩ ⟨l', v', W⟩ t h (extP Y X u) (fun _ => rfl)
  dsimp only at r
  rw [bank_extW] at r
  exact r

/-! ## Generic charged copy through a blank temporary -/

def sl3 {K : Type} (a b t : K) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) : Fin 3 ↪ K where
  toFun := ![a, b, t]
  inj' := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

def cp3 {K : Type} [DecidableEq K] (a b t : K) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) :=
  MatrixStage4ScalarPreparationOps.copyProgram (sl3 a b t h1 h2 h3)

theorem cp3_run {K : Type} [DecidableEq K] (a b t : K) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t)
    (S : K → List Bool) (hb : S b = []) (ht : S t = []) :
    ((advance (cp3 a b t h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (sl3 a b t h1 h2 h3) S ht
  have e0 : (sl3 a b t h1 h2 h3) 0 = a := rfl
  have e1 : (sl3 a b t h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

/-! ## Cell names -/

abbrev tmpP : HP := .inl (G5eYkCore.zc 1)
abbrev raw3P : HP := .inl (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 3))))
abbrev raw4P : HP := .inl (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 4))))
abbrev c55P : HP := .inl (.inl (.inl (RoundInstall.fH 55)))
abbrev wc (i : Fin 10) : HW := .inl (.inl i)
abbrev wb (i : Fin 10) : HP := .inr (.inl (wc i))
abbrev wRows : HP := .inr (.inl (.inr .rows))
abbrev wCols : HP := .inr (.inl (.inr .cols))

def cpM := cp3 raw3P (wb 0) tmpP (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
def cpN := cp3 raw4P (wb 1) tmpP (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
def cpW := cp3 c55P (wb 2) tmpP (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)

theorem nodupR : [wRows, wb 3, wb 4, pc].Nodup := by
  simp [List.nodup_cons]
theorem nodupC : [wCols, wb 3, wb 4, pc].Nodup := by
  simp [List.nodup_cons]
theorem rowsNeCols : wRows ≠ wCols := by intro h; cases h

def ctr := G5cCounters.countersProgram wRows wCols (wb 3) (wb 4) pc nodupR nodupC

def ctr0 : (((Bool × Bool) × Option Bool) × ((Bool × Bool) × Option Bool)) :=
  (((false, false), none), ((false, false), none))

/-- The preparation: three copies, then the two counters (charged handoffs). -/
def prepProgram :=
  BitMachineRawSequence.program cpM
    (BitMachineRawSequence.program cpN
      (BitMachineRawSequence.program cpW ctr
        (BitMachineRawSequence.leftLabel (.inr false)) none ctr0)
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, ctr0))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, (none, ctr0))

def prep0 : Option Bool × (Option Bool × (Option Bool ×
    (((Bool × Bool) × Option Bool) × ((Bool × Bool) × Option Bool)))) :=
  (none, (none, (none, ctr0)))

/-- The admitted padded writer (the fixed `MatrixTableWriter` controller over the admitted entry
program `Unit4Post.PadWriter.entryProgram`). -/
def writer := MatrixTableWriter.program Unit4Post.PadWriter.entryProgram
  Unit4Post.PadWriter.start Unit4Post.PadWriter.initial

/-- Preparation, then the lifted writer. -/
def prepWrite :=
  BitMachineRawSequence.program prepProgram (liftW writer)
    (Sum.inr (MatrixTableWriter.Admin.copy .rows)) prep0 (Unit4Post.PadWriter.initial, none)

/-- ONE fixed program: the first stage `A` on the `H8` region, then preparation and writer. -/
def padCore {LA VA : Type} (A : LA → TM2.Stmt (fun _ : G5eYkCore.H8 => Bool) LA VA) (v₀ : VA) :=
  BitMachineRawSequence.program (liftY A) prepWrite
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    v₀ (prep0, (Unit4Post.PadWriter.initial, none))

/-! ## Bank bookkeeping -/

theorem upd_W (Y : G5eYkCore.H8 → List Bool) (W : HW → List Bool) (u : List Bool) (x : HW)
    (v : List Bool) :
    Function.update (extP Y W u) (Sum.inr (Sum.inl x)) v = extP Y (Function.update W x v) u := by
  funext z
  rcases z with z | z | z
  · exact Function.update_of_ne (by intro h; cases h) _ _
  · by_cases hz : z = x
    · subst hz
      simp only [Function.update_self, extP, Sum.elim_inr, Sum.elim_inl]
    · rw [Function.update_of_ne (by intro h; apply hz; cases h; rfl)]
      simp only [extP, Sum.elim_inr, Sum.elim_inl]
      rw [Function.update_of_ne hz]
  · exact Function.update_of_ne (by intro h; cases h) _ _

/-- The blank writer bank. -/
def W0 : HW → List Bool := fun _ => []

/-- The pad writer's start bank. -/
def Wready (m r : ℕ) (w : List Bool) (p : ℕ) (out : List Bool) : HW → List Bool :=
  (MatrixTableWriter.ready (Unit4Post.PadWriter.persistentBank m r w) (2 ^ p) (2 ^ p) 0 0 0 0 []
    out).contents

theorem final_W (m r p : ℕ) (w : List Bool) :
    Function.update (Function.update (Function.update (Function.update (Function.update W0
      (wc 0) (List.replicate m true)) (wc 1) (List.replicate r true)) (wc 2) w)
      (.inr .rows) (List.replicate (2 ^ p) true)) (.inr .cols) (List.replicate (2 ^ p) true) =
    Wready m r w p [] := by
  funext z
  rcases z with (i | i) | e
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases e <;> rfl

/-- **Preparation run.** From an `H8` bank `Y` (raw words 3, 4 = unary `m`, `r`; cell 55 = `w`;
`zc 1` blank), the blank writer bank and unary `p` in `pc`, the fixed `prepProgram` reaches the pad
writer's exact start bank, `Y` and `pc` unchanged. -/
theorem prep_run (Y : G5eYkCore.H8 → List Bool) (m r p : ℕ) (w : List Bool)
    (h3 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 3)))) = List.replicate m true)
    (h4 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 4)))) = List.replicate r true)
    (h55 : Y (.inl (.inl (RoundInstall.fH 55))) = w)
    (ht : Y (G5eYkCore.zc 1) = []) :
    ∃ t ≤ (2 * m + 2) + (2 * r + 2) + (2 * w.length + 2) + (2 * (4 * 2 ^ p + 5 * p + 7) + 1) + 3,
      ((advance prepProgram)^[t])
        ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), prep0,
          extP Y W0 (List.replicate p true)⟩ =
        ⟨none, prep0, extP Y (Wready m r w p []) (List.replicate p true)⟩ := by
  set S0 := extP Y W0 (List.replicate p true) with hS0
  have s1 := cp3_run raw3P (wb 0) tmpP (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) S0 rfl ht
  have e1 : S0 raw3P = List.replicate m true := h3
  rw [e1, List.length_replicate, hS0, upd_W] at s1
  have s2 := cp3_run raw4P (wb 1) tmpP (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (extP Y (Function.update W0 (wc 0) (List.replicate m true))
      (List.replicate p true)) rfl ht
  have e2 : (extP Y (Function.update W0 (wc 0) (List.replicate m true))
      (List.replicate p true)) raw4P = List.replicate r true := h4
  rw [e2, List.length_replicate, upd_W] at s2
  have s3 := cp3_run c55P (wb 2) tmpP (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (extP Y (Function.update (Function.update W0 (wc 0)
      (List.replicate m true)) (wc 1) (List.replicate r true)) (List.replicate p true)) rfl ht
  have e3 : (extP Y (Function.update (Function.update W0 (wc 0)
      (List.replicate m true)) (wc 1) (List.replicate r true)) (List.replicate p true)) c55P = w := h55
  rw [e3, upd_W] at s3
  set S3 := extP Y (Function.update (Function.update (Function.update W0 (wc 0)
      (List.replicate m true)) (wc 1) (List.replicate r true)) (wc 2) w) (List.replicate p true)
    with hS3
  obtain ⟨t4, ht4, s4⟩ := G5cCounters.counters_run wRows wCols (wb 3) (wb 4) pc nodupR nodupC
    rowsNeCols S3 p rfl rfl rfl rfl rfl
  rw [hS3, upd_W, upd_W, final_W] at s4
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs cpW ctr BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (.inr false)) none none ctr0 ctr0 _ _ _ _ _ s3 s4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs cpN _ BitMachineCopy.Label.scan _ none none
    _ _ _ _ _ _ _ s2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs cpM _ BitMachineCopy.Label.scan _ none none
    _ _ _ _ _ _ _ s1 r2
  exact ⟨u1, by omega, r1⟩

/-- **Preparation and writer.** -/
theorem prepWrite_run (Y : G5eYkCore.H8 → List Bool) {m r : ℕ} (R : Fin m → Fin r → Bool)
    (hm : 0 < m) (hr : 0 < r) (p : ℕ)
    (h3 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 3)))) = List.replicate m true)
    (h4 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 4)))) = List.replicate r true)
    (h55 : Y (.inl (.inl (RoundInstall.fH 55))) = MatrixMaterialization.rowMajor R)
    (ht : Y (G5eYkCore.zc 1) = []) :
    ∃ t ≤ ((2 * m + 2) + (2 * r + 2) + (2 * (m * r) + 2) + (2 * (4 * 2 ^ p + 5 * p + 7) + 1) + 3) +
        MatrixTableWriter.writerBound (2 ^ p) (2 ^ p)
          (Unit4Post.PadWriter.callbackBound (2 ^ p) (2 ^ p) m r (m * r)) + 1, ∃ v,
      ((advance prepWrite)^[t])
        ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (prep0, (Unit4Post.PadWriter.initial, none)),
          extP Y W0 (List.replicate p true)⟩ =
        ⟨none, (prep0, v),
          extP Y (Wready m r (MatrixMaterialization.rowMajor R) p (FinalPadding.table R p hm hr))
            (List.replicate p true)⟩ := by
  obtain ⟨t1, ht1, s1⟩ := prep_run Y m r p _ h3 h4 h55 ht
  rw [MatrixMaterialization.rowMajor_length] at ht1
  obtain ⟨t2, ht2, v, s2⟩ := Unit4Post.PadWriter.padded_table R p hm hr []
  rw [List.append_nil] at s2
  have s2' := liftW_run writer _ _ _ _ Y _ _ (List.replicate p true) t2 s2
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs prepProgram (liftW writer) _ _ prep0 prep0
    _ _ _ _ _ _ _ s1 s2'
  exact ⟨u, by omega, v, ru⟩

/-- **Segment 2 core.** The first stage `A` followed by preparation and writer, generic in `A`. -/
theorem padCore_run {LA VA : Type} (A : LA → TM2.Stmt (fun _ : G5eYkCore.H8 => Bool) LA VA)
    (a₀ : LA) (v₀ : VA) (X Y : G5eYkCore.H8 → List Bool) (tA : ℕ)
    (hA : ((advance A)^[tA]) (⟨some a₀, v₀, X⟩ : TM2.Cfg (fun _ : G5eYkCore.H8 => Bool) LA VA) =
      ⟨none, v₀, Y⟩)
    {m r : ℕ} (R : Fin m → Fin r → Bool) (hm : 0 < m) (hr : 0 < r) (p : ℕ)
    (h3 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 3)))) = List.replicate m true)
    (h4 : Y (.inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 4)))) = List.replicate r true)
    (h55 : Y (.inl (.inl (RoundInstall.fH 55))) = MatrixMaterialization.rowMajor R)
    (ht : Y (G5eYkCore.zc 1) = []) :
    ∃ t ≤ tA + (((2 * m + 2) + (2 * r + 2) + (2 * (m * r) + 2) + (2 * (4 * 2 ^ p + 5 * p + 7) + 1) + 3) +
        MatrixTableWriter.writerBound (2 ^ p) (2 ^ p)
          (Unit4Post.PadWriter.callbackBound (2 ^ p) (2 ^ p) m r (m * r)) + 1) + 1, ∃ v,
      ((advance (padCore A v₀))^[t])
        ⟨some (BitMachineRawSequence.leftLabel a₀), (v₀, (prep0, (Unit4Post.PadWriter.initial, none))),
          extP X W0 (List.replicate p true)⟩ =
        ⟨none, (v₀, (prep0, v)),
          extP Y (Wready m r (MatrixMaterialization.rowMajor R) p (FinalPadding.table R p hm hr))
            (List.replicate p true)⟩ := by
  have s1 := liftY_run A _ _ _ _ X Y W0 (List.replicate p true) tA hA
  obtain ⟨t2, ht2, v, s2⟩ := prepWrite_run Y R hm hr p h3 h4 h55 ht
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs (liftY A) prepWrite _ _ v₀ v₀
    _ _ _ _ _ _ _ s1 s2
  exact ⟨u, by omega, v, ru⟩

#print axioms cp3_run
#print axioms upd_W
#print axioms final_W
#print axioms prep_run
#print axioms prepWrite_run
#print axioms padCore_run

end EthInapproximability.CurrentPaper.G5fPadCore
