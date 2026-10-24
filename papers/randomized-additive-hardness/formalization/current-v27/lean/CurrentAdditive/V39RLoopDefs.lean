import CurrentAdditive.V39RequestStepK
import Paper2.StepXGrowth
import Paper2.ClearAll
import Paper2.CopyAll
import Paper2.CountedLoop

/-! Unit 3, segment (2): the data of the k-fold request loop.

Loop bank `JL = JT ⊕ (SrcX.JX ⊕ Fin 2)`: the one-level bank `JT = J ⊕ E` of
`TemplateStepX.stepX`, a MASTER region `M` (a second copy of `SrcX.JX`,
never written by any program of the loop) holding the level-independent public
inputs, the loop counter `ctr` and one scratch cell `scr`.

ONE fixed body program (`body`), sequenced by the production
`BitMachineRawSequence` (each handoff one charged step):
1. `prep`: `CopyAll` of every master cell into its `E` twin, except the level
   marks cell of `DefaultWordLoop`, which receives a copy of the loop counter
   (the counter holds exactly `k` marks when level `k+1 → k` runs);
2. `stepL`: `TemplateStepX.stepX` lifted by `Sum.inl`;
3. `ClearAll` of every `JT` cell except `nC 0`, `nC 1` (the level-`k+1` codes)
   and `r2 tagC`, `r2 rowC` (the encoded request);
4. `navL`: the admitted `NavJoin.program`, rerun on the cleared join bank
   (recomputes `outVec k`, in particular `row_k` in `nC 5`, `col_k` in `nC 4`);
5. `ClearAll` of `nC 0`, `nC 1`;
6. `CopyAll`: `nC 5 → nC 0`, `nC 4 → nC 1`, `r2 tagC → r1 Xc`, `r2 rowC → r1 Yc`;
7. `ClearAll` of `nC 2 … nC 8`, `r2 tagC`, `r2 rowC`.
The resulting bank is exactly the level-`k` loop bank of the requested pair. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop

noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell)
open Paper2.TemplateStepX (JT ccX rcX)

abbrev JL := JT ⊕ (SrcX.JX ⊕ Fin 2)

def inT : JT ↪ JL := ⟨Sum.inl, Sum.inl_injective⟩
def mX (z : SrcX.JX) : JL := .inr (.inl z)
def eX (z : SrcX.JX) : JL := .inl (.inr z)
def jC (x : J) : JL := .inl (.inl x)
def ctr : JL := .inr (.inr 0)
def scr : JL := .inr (.inr 1)
/-- The level-marks cell of the `DefaultWordLoop` part of `E`. -/
def marksX : SrcX.JX := .inr (.inr (.inr 0))

/-! ### Step 1: the preparation copies -/

def prepSrc (z : SrcX.JX) : JL := if z = marksX then ctr else mX z

def prepF (z : SrcX.JX) : Fin 3 → JL := ![prepSrc z, eX z, scr]

theorem prepF_injective (z : SrcX.JX) : Function.Injective (prepF z) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (simp only [prepF, prepSrc, eX, mX, ctr, scr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
       split_ifs at h <;> simp_all)

def prepE (z : SrcX.JX) : Fin 3 ↪ JL := ⟨prepF z, prepF_injective z⟩

abbrev NX := Fintype.card SrcX.JX
def exX : Fin NX ≃ SrcX.JX := (Fintype.equivFin SrcX.JX).symm
def prepCps (i : Fin NX) : Fin 3 ↪ JL := prepE (exX i)

def prep := CopyAll.prog prepCps

/-! ### Step 2: the one-level program -/

def stepL := fun l => stackStmt inT (CurrentAdditive.V39RequestStep.stepX l)

/-! ### Step 3: clear every `JT` cell but four -/

def keep (a : JT) : Prop :=
  a = .inl (nC 0) ∨ a = .inl (nC 1) ∨ a = .inl (r2 RequestSelect.tagC) ∨
    a = .inl (r2 RequestSelect.rowC)

instance (a : JT) : Decidable (keep a) := by unfold keep; infer_instance

abbrev CT := {a : JT // ¬ keep a}
abbrev N1 := Fintype.card CT
def e1 : Fin N1 ≃ CT := (Fintype.equivFin CT).symm
def cl1 (i : Fin N1) : JL := .inl (e1 i).1

theorem cl1_injective : Function.Injective cl1 := by
  intro a b h
  simp only [cl1, Sum.inl.injEq] at h
  exact e1.injective (Subtype.ext h)

/-! ### Step 4: the navigation join, rerun -/

def iNLf (x : NavJoin.Stack) : JL := .inl (.inl (.inl x))
def iNL : NavJoin.Stack ↪ JL := ⟨iNLf, fun a b h => by simpa [iNLf] using h⟩
def navL := fun l => stackStmt iNL (NavJoin.program l)

/-! ### Steps 5-7 -/

def cl2 : Fin 2 → JL := ![jC (nC 0), jC (nC 1)]

theorem cl2_injective : Function.Injective cl2 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cl2, jC, nC]

def cpv (a b : JL) (hab : a ≠ b) (ha : a ≠ scr) (hb : b ≠ scr) : Fin 3 ↪ JL :=
  ⟨![a, b, scr], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all⟩

def cp2 : Fin 4 → (Fin 3 ↪ JL) :=
  ![cpv (jC (nC 5)) (jC (nC 0)) (by simp [jC, nC]) (by simp [jC, scr]) (by simp [jC, scr]),
    cpv (jC (nC 4)) (jC (nC 1)) (by simp [jC, nC]) (by simp [jC, scr]) (by simp [jC, scr]),
    cpv (jC (r2 RequestSelect.tagC)) (jC (r1 RequestSelect.Xc))
      (by simp [jC, r1, r2]) (by simp [jC, scr]) (by simp [jC, scr]),
    cpv (jC (r2 RequestSelect.rowC)) (jC (r1 RequestSelect.Yc))
      (by simp [jC, r1, r2]) (by simp [jC, scr]) (by simp [jC, scr])]

def cl3 : Fin 9 → JL :=
  ![jC (nC 2), jC (nC 3), jC (nC 4), jC (nC 5), jC (nC 6), jC (nC 7), jC (nC 8),
    jC (r2 RequestSelect.tagC), jC (r2 RequestSelect.rowC)]

theorem cl3_injective : Function.Injective cl3 := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [cl3, jC, nC, r2, RequestSelect.tagC, RequestSelect.rowC]

/-! ### The ONE fixed body program -/

abbrev oc := (none : Option Bool)

def ctl1 := (oc, CurrentAdditive.V39RequestStep.stepXCtl)
def b1 := BitMachineRawSequence.program prep stepL (leftLabel (leftLabel NavJoin.startLabel))
  oc CurrentAdditive.V39RequestStep.stepXCtl
def b2 := BitMachineRawSequence.program b1 (ClearAll.prog cl1) ⟨0, by omega⟩ ctl1 oc
def ctl2 := (ctl1, oc)
def b3 := BitMachineRawSequence.program b2 navL NavJoin.startLabel ctl2 NavJoin.ctl
def ctl3 := (ctl2, NavJoin.ctl)
def b4 := BitMachineRawSequence.program b3 (ClearAll.prog cl2) ⟨0, by omega⟩ ctl3 oc
def ctl4 := (ctl3, oc)
def b5 := BitMachineRawSequence.program b4 (CopyAll.prog cp2) (.inl ⟨0, by omega⟩) ctl4 oc
def ctl5 := (ctl4, oc)
/-- ONE request level of the loop body (a fixed program; no parameter). -/
def body := BitMachineRawSequence.program b5 (ClearAll.prog cl3) ⟨0, by omega⟩ ctl5 oc
def bodyCtl := (ctl5, oc)
def bodyStart := FetchIndexed.labelOf body (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (.inl ⟨0, by omega⟩ : CopyAll.Lab NX)))))))

/-- The k-fold request loop: ONE fixed program (production `CountedLoop.loop`). -/
def rloop := CountedLoop.loop ctr body bodyStart bodyCtl

/-! ### Banks -/

variable {n p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The master copy of the level-independent public inputs of the source arm:
`SrcX.WXb g r 0 [] []` with the four placed cells and the level marks blank. -/
def master (g : EncodedGraph.Graph) (r : ℕ) (z : SrcX.JX) : List Bool :=
  if z = SrcX.srcAX ∨ z = SrcX.fwX ∨ z = ccX ∨ z = rcX ∨ z = marksX then []
  else SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r 0 [] [] z

/-- The level-`k` bank on `J` (for `k = k' + 1` literally `TemplateStepX.W0f k'`). -/
def J0 (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) :
    J → List Bool :=
  Sum.elim (NavJoin.jb (NavJoin.inVec
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).1)
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2)))
    (Sum.elim (RequestSelect.mk [] [] (RequestSelect.vec
      ((defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode x)
      ((defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode y) [] [] [] [] [])) (fun _ => []))

theorem J0_succ (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    J0 (k + 1) x y = TemplateStepX.W0f k x y := rfl

/-- The loop bank at level `k` with the pair `(x, y)`: `J0` on `J`, `E` blank, the
master copy in `M`, `k` marks in the counter, blank scratch. -/
def bankL (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) :
    JL → List Bool :=
  Sum.elim (Sum.elim (J0 k x y) (fun _ => []))
    (Sum.elim (master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r)
      ![List.replicate k true, []])

/-- `SrcX.WXb` depends on the level only through the code copies and the marks. -/
theorem WXb_level (g : EncodedGraph.Graph) (r k : ℕ) (z : SrcX.JX)
    (h1 : z ≠ SrcX.srcAX) (h2 : z ≠ SrcX.fwX) (h3 : z ≠ ccX) (h4 : z ≠ rcX) (h5 : z ≠ marksX) :
    SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] z =
      SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r 0 [] [] z := by
  rcases z with (((z | z) | z) | (z | z)) | (z | z | z)
  · rfl
  · fin_cases z
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    all_goals rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · fin_cases z
    · exact absurd rfl h5
    · rfl

theorem WXb_marks (g : EncodedGraph.Graph) (r k : ℕ) :
    SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] marksX =
      List.replicate k true := rfl

end

#print axioms prepF_injective
#print axioms cl1_injective
#print axioms cl3_injective
#print axioms WXb_level

end CurrentAdditive.V39RLoop
