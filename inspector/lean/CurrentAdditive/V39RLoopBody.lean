import CurrentAdditive.V39RLoopDefs
import CurrentAdditive.V39RLoopGrowth

/-! Unit 3, segment (2): ONE run of the ONE fixed loop body `RLoop.body` from
the level-`k+1` loop bank (counter decremented to `k` marks) to EXACTLY the
level-`k` loop bank of the requested pair `RecursiveEntries.request activity ξ k x y`,
for every level-`k+1` pair (both raw-row cases, every tag), within the explicit
clock `bodyClock`. -/

set_option maxHeartbeats 64000000
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
open CurrentAdditive.V39RequestStep (stepX stepXCtl stepClock)

open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell)
open Paper2.TemplateStepX (JT ccX rcX W0f W2f selClock)

/-! ### Generic helpers -/

theorem liftL {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JL)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JL → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JL => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem clr_in {K : Type*} [DecidableEq K] {N : ℕ} (cs : Fin N → K) (T : K → List Bool) (a : K)
    (h : ∃ j, cs j = a) : ClearAll.clearFrom cs 0 T a = [] := by
  simp only [ClearAll.clearFrom]
  rw [if_pos (by obtain ⟨j, hj⟩ := h; exact ⟨j, Nat.zero_le _, hj⟩)]

theorem clr_out {K : Type*} [DecidableEq K] {N : ℕ} (cs : Fin N → K) (T : K → List Bool) (a : K)
    (h : ∀ j, cs j ≠ a) : ClearAll.clearFrom cs 0 T a = T a := by
  simp only [ClearAll.clearFrom]
  rw [if_neg (by rintro ⟨j, -, hj⟩; exact h j hj)]

theorem cl1_mem (b : JT) (hb : ¬ keep b) : ∃ j, cl1 j = .inl b :=
  ⟨e1.symm ⟨b, hb⟩, by simp [cl1]⟩

theorem cl1_not (b : JT) (hb : keep b) : ∀ j, cl1 j ≠ .inl b := by
  intro j hj
  simp only [cl1, Sum.inl.injEq] at hj
  exact (e1 j).2 (hj ▸ hb)

theorem cl1_inr (c : SrcX.JX ⊕ Fin 2) : ∀ j, cl1 j ≠ .inr c := by
  intro j hj
  simp [cl1] at hj

theorem prep_dst (i : Fin NX) : prepCps i 1 = eX (exX i) := rfl
theorem prep_src (i : Fin NX) : prepCps i 0 = prepSrc (exX i) := rfl
theorem prep_scr (i : Fin NX) : prepCps i 2 = scr := rfl

theorem prep_hsd : ∀ i j, prepCps i 0 ≠ prepCps j 1 := by
  intro i j
  rw [prep_src, prep_dst]
  unfold prepSrc
  split_ifs <;> simp [eX, mX, ctr]

theorem prep_hzd : ∀ i j, prepCps i 2 ≠ prepCps j 1 := by
  intro i j
  rw [prep_scr, prep_dst]
  simp [eX, scr]

theorem prep_hdd : ∀ i j, prepCps i 1 = prepCps j 1 → i = j := by
  intro i j h
  rw [prep_dst, prep_dst] at h
  simp only [eX, Sum.inl.injEq, Sum.inr.injEq] at h
  exact exX.injective h

theorem prep_notdst (a : JL) (h : ∀ z, a ≠ eX z) : ∀ j, prepCps j 1 ≠ a := by
  intro j hj
  rw [prep_dst] at hj
  exact h _ hj.symm

theorem cp2_hsd : ∀ i j, cp2 i 0 ≠ cp2 j 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cp2, cpv, jC, nC, r1, r2, RequestSelect.tagC, RequestSelect.rowC, RequestSelect.Xc,
      RequestSelect.Yc]

theorem cp2_hzd : ∀ i j, cp2 i 2 ≠ cp2 j 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cp2, cpv, jC, scr]

theorem cp2_hdd : ∀ i j, cp2 i 1 = cp2 j 1 → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [cp2, cpv, jC, nC, r1, RequestSelect.Xc, RequestSelect.Yc]

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- `J0` vanishes off its four written cells. -/
theorem J0_support {n : ℕ} (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
    (a : J) (h0 : a ≠ nC 0) (h1 : a ≠ nC 1) (hX : a ≠ r1 RequestSelect.Xc)
    (hY : a ≠ r1 RequestSelect.Yc) : J0 k x y a = [] := by
  rcases a with (a | a) | ((a | a | a) | a)
  · rfl
  · fin_cases a
    · exact absurd rfl h0
    · exact absurd rfl h1
    all_goals rfl
  · exact RequestSelect.inner_nil a
  · exact RequestSelect.inner_nil a
  · fin_cases a
    · exact absurd rfl hX
    · exact absurd rfl hY
    all_goals rfl
  · rfl

/-- The `E` bank delivered by the preparation copies. -/
def E0k (g : EncodedGraph.Graph) (r k : ℕ) (z : SrcX.JX) : List Bool :=
  if z = marksX then List.replicate k true
  else master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r z

theorem E0k_hE0 (g : EncodedGraph.Graph) (r k : ℕ) (z : SrcX.JX)
    (h1 : z ≠ SrcX.srcAX) (h2 : z ≠ SrcX.fwX) (h3 : z ≠ ccX) (h4 : z ≠ rcX) :
    E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k z =
      SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] z := by
  unfold E0k
  split_ifs with h5
  · subst h5; exact (WXb_marks g r k).symm
  · unfold master
    rw [if_neg (by tauto)]
    exact (WXb_level g r k z h1 h2 h3 h4 h5).symm

theorem E0k_srcA (g : EncodedGraph.Graph) (r k : ℕ) :
    E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k SrcX.srcAX = [] := by
  unfold E0k master
  rw [if_neg (by simp [marksX, SrcX.srcAX]), if_pos (Or.inl rfl)]

/-- The explicit body clock (the sum of the seven checked clocks and six handoffs). -/
def bodyClock (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = CurrentAdditive.LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x0 : CurrentAdditive.V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k+1))
    (y0 : CurrentAdditive.V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k+1)) : ℕ :=
  let x := (CurrentAdditive.V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).1 x0
  let y := (CurrentAdditive.V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).2 y0
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q k
  let c' := seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)
  let activity := CurrentAdditive.V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
  let req := RecursiveEntries.request activity ξ k x y
  let Tst := stepClock g hg hs r hq ξ k x0 y0
  let Lp := (∑ z : SrcX.JX, (master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    g r z).length) + k
  let Lc := (∑ a : JT, ((Sum.elim (W0f k x y) (E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) g r k)) a).length) + CurrentAdditive.V39RLoopGrowth.pushBound * Tst
  let L2 := (encodeCode c'.1).length + (encodeCode c'.2).length
  let L6 := (encodeCode c.1).length + (encodeCode c.2).length + (C.1.encode req.1).length +
    (C.2.encode req.2).length
  let L7 := (∑ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length) +
    (C.1.encode req.1).length + (C.2.encode req.2).length
  (((((NX * (2 * Lp + 3) + 1 + Tst + 1) + (N1 * (Lc + 1) + 1) + 1) +
    NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + 1) + (2 * (L2 + 1) + 1) + 1) +
    (4 * (2 * L6 + 3) + 1) + 1) + (9 * (L7 + 1) + 1) + 1

end

#print axioms liftL
#print axioms clr_in
#print axioms clr_out
#print axioms J0_support
#print axioms E0k_hE0

end CurrentAdditive.V39RLoop
