import Paper2.SSSchedMachine
import Paper2.SmallRatRunC
import Paper2.SmallRatValues

/-! Lane owner:a-small-1, R16 part 3: ONE fixed program per `(Δ, γ)` printing all of lock v12
`eq:schedule` (C-parameters.tex:18-29) from the literal graph bytes.

Bank `KR = SSSched.KS ⊕ Fin 22`. Program (one charged `BitMachineRawSequence` handoff):

  `schedR Δ γ = SSSched.sched Δ γ (frozen, lifted by Sum.inl) ; SmallRatProg.ratProg (embedded by ιR)`

`ιR` maps the nine input cells of `ratProg` onto the cells of the frozen schedule's exit bank that hold
unary n, a, a·m, 2bΔ, 6144b (admitted `QFacts`), s, w (`LProducer` cells), L and Q, and the 22 new cells
onto the fresh `Fin 22` region.  Nothing is inserted: every input of the second part is the frozen first
part's output. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

namespace SmallRatSched

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2
open Paper2.A3Assembly
open Paper2.CountFront (J2 LK QK jc lc qc gB G0 LFacts QFacts)
open SSSched SSSchedMachine SmallRatProg SmallRatValues

abbrev KR := KS ⊕ Fin 22
instance instDecKR : DecidableEq KR := @instDecidableEqSum _ _ instDecKS inferInstance

def ιK : KS ↪ KR := ⟨Sum.inl, Sum.inl_injective⟩

/-- The nine schedule cells read by the second part. -/
def inCellsQ : Fin 9 → KS :=
  ![.inl (jc (qc (.inl 0))), .inl (jc (qc (.inl 15))), .inl (jc (qc (.inl 16))),
    .inl (jc (qc (.inl 12))), .inl (jc (qc (.inl 19))), .inl (jc (lc LProducer.sC)),
    .inl (jc (lc LProducer.wC)), .inl (jc (qc (.inl 2))), .inl (jc (qc (.inl 24)))]

theorem inCellsQ_inj : Function.Injective inCellsQ := by
  intro x y h
  fin_cases x <;> fin_cases y <;>
    first | rfl | (exfalso; revert h; simp [inCellsQ, jc, qc, lc, LProducer.c])

def ιRf : AK → KR := Sum.elim (fun i => .inl (inCellsQ i)) (fun j => .inr j)

theorem ιRf_inj : Function.Injective ιRf := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y <;> simp only [ιRf, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · rw [inCellsQ_inj h]
  · rw [h]

def ιR : AK ↪ KR := ⟨ιRf, ιRf_inj⟩

def PS (Δ : ℕ) (γ : ℚ) := fun l => stackStmt ιK (sched Δ γ l)
def PR := fun l => stackStmt ιR (ratProg l)

/-- **The full schedule machine**: ONE fixed program per `(Δ, γ)`. -/
def schedR (Δ : ℕ) (γ : ℚ) := BitMachineRawSequence.program (PS Δ γ) PR ratStart (schedCtl Δ γ) ratCtl

def rStart (Δ : ℕ) (γ : ℚ) := labelOfP (schedR Δ γ) (leftLabel (schedStart Δ γ))
def rCtl (Δ : ℕ) (γ : ℚ) := (schedCtl Δ γ, ratCtl)

/-- The nine input values of the second part (all read from the frozen schedule's exit bank). -/
def vals (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (g.vertices, γ.num.toNat, γ.num.toNat * g.edges.length, 2 * γ.den * Δ, 6144 * γ.den,
    SourceProfileParameters.width (Nat.clog 2 g.vertices),
    ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices), Nat.clog 2 g.vertices,
    ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)

/-- The final bank of the second part, at the actual values. -/
def RB (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) : AK → List Bool :=
  B19 g.vertices γ.num.toNat (γ.num.toNat * g.edges.length) (2 * γ.den * Δ) (6144 * γ.den)
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)

def RB0 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) : AK → List Bool :=
  B0 g.vertices γ.num.toNat (γ.num.toNat * g.edges.length) (2 * γ.den * Δ) (6144 * γ.den)
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)

/-- The explicit clock of the second part at the actual values. -/
def ratTime (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) : ℕ :=
  ratBd g.vertices γ.num.toNat (γ.num.toNat * g.edges.length) (2 * γ.den * Δ) (6144 * γ.den)
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)

theorem bank_inlK (S : KS → List Bool) : bank ιK (fun _ => []) S = Sum.elim S (fun _ => []) := by
  funext x
  rcases x with x | x
  · exact bank_at ιK _ S x
  · rw [bank_outside ιK _ S _ (by rintro ⟨y, hy⟩; cases hy)]
    rfl

/-- The exit bank of the whole program. -/
def exitBank (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool)
    (FQ : QK → List Bool) (bit : Bool) : KR → List Bool :=
  Sum.elim (finalBank g hg FL FQ bit) (fun j => RB Δ γ g (Sum.inr j))

/-- **The run of the full schedule machine** from the literal graph bytes: exact exit bank (the frozen
schedule's exit bank on `KS`, the second part's final bank on the new cells), within the frozen clock plus
`ratTime + 1`. -/
theorem schedR_run (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    ∃ T ≤ 2 ^ (FrontClock13.cF Δ γ * 45) * ((EncodedGraph.encode g).length + 1) ^ (FrontClock13.cF Δ γ * 45) +
        ratTime Δ γ g + 1,
      ∃ bit : Bool, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
        ((advance (schedR Δ γ))^[T])
            (⟨some (rStart Δ γ), rCtl Δ γ, Sum.elim (Sum.elim (G0 g) (fun _ => [])) (fun _ => [])⟩ :
              TM2.Cfg (fun _ : KR => Bool) _ _) =
          ⟨none, rCtl Δ γ, exitBank Δ γ g hg FL FQ bit⟩ ∧
        LFacts g.vertices FL ∧
        QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
          (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
          (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
        FL LProducer.pC = LProducer.u (LookupSeed.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.sC = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.q1C = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) ∧
        FL LProducer.q2C = LProducer.u (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) ∧
        FL LProducer.wC = LProducer.u (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) ∧
        FQ (.inl 2) = QProducer.u (Nat.clog 2 g.vertices) ∧
        FQ (.inl 24) = QProducer.u
          (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨T, hT, u0, bit, FL, FQ, hr, hLF, hQF, hp, hs, hq1, hq2, hw, hL, hQ, hbit⟩ :=
    SSSchedClock.schedule_machine Δ γ hγ hΔ g hg hn hinc hdeg
  have hQF' := hQF
  obtain ⟨c, q0, -, -, -, -, -, -, -, -, -, -, -, q12, -, -, q15, q16, -, -, q19, -⟩ := hQF'
  -- first part, lifted
  have h1 := BitMachineStackRun.run ιK (fun _ => []) (sched Δ γ)
    (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (G0 g) (fun _ => [])⟩ :
      TM2.Cfg (fun _ : KS => Bool) _ _) T
  rw [hr] at h1
  set W := bank ιK (fun _ => []) (finalBank g hg FL FQ bit) with hWdef
  have h1' : ((advance (PS Δ γ))^[T])
      (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (Sum.elim (G0 g) (fun _ => [])) (fun _ => [])⟩ :
        TM2.Cfg (fun _ : KR => Bool) _ _) = ⟨none, u0, W⟩ := by
    rw [← bank_inlK]
    exact h1
  -- the second part's start bank is the first part's exit bank
  have hWl : ∀ x, W (.inl x) = finalBank g hg FL FQ bit x := fun x => bank_at ιK _ _ x
  have hWr : ∀ j, W (.inr j) = [] := fun j => bank_outside _ _ _ _ (by rintro ⟨y, hy⟩; cases hy)
  have fin_q : ∀ i : Fin 29, i ≠ 1 → finalBank g hg FL FQ bit (.inl (jc (qc (.inl i)))) = FQ (.inl i) := by
    intro i hi
    rw [final_inl g hg FL FQ bit _ (by simp [sA, jc, qc, lc]) (by simpa [sB, jc, qc] using hi)]
    rfl
  have fin_l : ∀ x : LK, x ≠ LProducer.nC → finalBank g hg FL FQ bit (.inl (jc (lc x))) = FL x := by
    intro x hx
    rw [final_inl g hg FL FQ bit _ (by simpa [sA, jc, lc] using hx) (by simp [sB, jc, qc, lc])]
    rfl
  have hstart : bank ιR W (RB0 Δ γ g) = W := by
    apply bank_eq_self
    intro k
    rcases k with i | j
    · show B0 _ _ _ _ _ _ _ _ _ (Sum.inl i) = W (Sum.inl (inCellsQ i))
      rw [hWl]
      fin_cases i
      · exact ((fin_q 0 (by decide)).trans q0).symm
      · exact ((fin_q 15 (by decide)).trans q15).symm
      · exact ((fin_q 16 (by decide)).trans q16).symm
      · exact ((fin_q 12 (by decide)).trans q12).symm
      · exact ((fin_q 19 (by decide)).trans q19).symm
      · have hleft : B0 g.vertices γ.num.toNat (γ.num.toNat * g.edges.length)
            (2 * γ.den * Δ) (6144 * γ.den)
            (SourceProfileParameters.width (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
            (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
              (Nat.clog 2 g.vertices) Δ γ) (Sum.inl (⟨5, by decide⟩ : Fin 9)) =
          LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices)) := by
            simp [B0, LProducer.u, u]
        have hidx : inCellsQ (⟨5, by decide⟩ : Fin 9) = .inl (jc (lc LProducer.sC)) := by rfl
        dsimp only
        rw [hleft, hidx, fin_l LProducer.sC (by decide)]
        exact hs.symm
      · have hleft : B0 g.vertices γ.num.toNat (γ.num.toNat * g.edges.length)
            (2 * γ.den * Δ) (6144 * γ.den)
            (SourceProfileParameters.width (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
            (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
              (Nat.clog 2 g.vertices) Δ γ) (Sum.inl (⟨6, by decide⟩ : Fin 9)) =
          LProducer.u (ParameterizedCanonicalSource.restorationWidth
            (Nat.clog 2 g.vertices)) := by simp [B0, LProducer.u, u]
        have hidx : inCellsQ (⟨6, by decide⟩ : Fin 9) = .inl (jc (lc LProducer.wC)) := by rfl
        dsimp only
        rw [hleft, hidx, fin_l LProducer.wC (by decide)]
        exact hw.symm
      · exact ((fin_q 2 (by decide)).trans hL).symm
      · exact ((fin_q 24 (by decide)).trans hQ).symm
    · show B0 _ _ _ _ _ _ _ _ _ (Sum.inr j) = W (Sum.inr j)
      rw [hWr]
      rfl
  -- second part, embedded
  obtain ⟨t2, ht2, h2⟩ := rat_run g.vertices γ.num.toNat (γ.num.toNat * g.edges.length)
    (2 * γ.den * Δ) (6144 * γ.den) (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
  have h2l := BitMachineStackRun.run ιR W ratProg
    (⟨some ratStart, ratCtl, RB0 Δ γ g⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) t2
  have h2c : ((advance ratProg)^[t2]) (⟨some ratStart, ratCtl, RB0 Δ γ g⟩ :
      TM2.Cfg (fun _ : AK => Bool) _ _) = ⟨none, ratCtl, RB Δ γ g⟩ := h2
  rw [h2c] at h2l
  have h2' : ((advance PR)^[t2]) (⟨some ratStart, ratCtl, W⟩ : TM2.Cfg (fun _ : KR => Bool) _ _) =
      ⟨none, ratCtl, bank ιR W (RB Δ γ g)⟩ := by
    have e : (⟨some ratStart, ratCtl, W⟩ : TM2.Cfg (fun _ : KR => Bool) _ _) =
        stackCfg ιR W (⟨some ratStart, ratCtl, RB0 Δ γ g⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) := by
      simp only [stackCfg]
      rw [hstart]
    rw [e]
    exact h2l
  -- the exit bank in closed form
  have hexit : bank ιR W (RB Δ γ g) = exitBank Δ γ g hg FL FQ bit := by
    funext x
    rcases x with x | j
    · by_cases hx : ∃ k, ιR k = Sum.inl x
      · obtain ⟨k, hk⟩ := hx
        rcases k with i | j
        · rw [← hk, bank_at]
          have hkeep := inputs_kept g.vertices γ.num.toNat (γ.num.toNat * g.edges.length)
            (2 * γ.den * Δ) (6144 * γ.den) (SourceProfileParameters.width (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) i
          change RB Δ γ g (Sum.inl i) = exitBank Δ γ g hg FL FQ bit (ιR (Sum.inl i))
          rw [show RB Δ γ g (Sum.inl i) = RB0 Δ γ g (Sum.inl i) from hkeep]
          have := congrFun hstart (ιR (Sum.inl i))
          rw [bank_at] at this
          rw [this]
          show W (Sum.inl (inCellsQ i)) = finalBank g hg FL FQ bit (inCellsQ i)
          exact hWl _
        · exact absurd hk (by simp [ιR, ιRf])
      · rw [bank_outside _ _ _ _ hx]
        exact hWl x
    · exact bank_at ιR W (RB Δ γ g) (Sum.inr j)
  rw [hexit] at h2'
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs (PS Δ γ) PR (schedStart Δ γ) ratStart
    (schedCtl Δ γ) u0 ratCtl ratCtl _ W _ T t2 h1' h2'
  refine ⟨t, ?_, bit, FL, FQ, hrun, hLF, hQF, hp, hs, hq1, hq2, hw, hL, hQ, hbit⟩
  have : t2 ≤ ratTime Δ γ g := ht2
  omega

/-- The printed schedule values on the new cells (unary), at the actual values. -/
theorem printed (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) :
    RB Δ γ g (Sum.inr 0) = u (etaNum γ g.edges.length) ∧
    RB Δ γ g (Sum.inr 8) = u (etaDen g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
    RB Δ γ g (Sum.inr 11) = u (deltaUDen g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
    RB Δ γ g (Sum.inr 12) = u 1 ∧
    RB Δ γ g (Sum.inr 13) = u (2 ^ Nat.clog 2 g.vertices) ∧
    RB Δ γ g (Sum.inr 16) = u (2 ^ (10 * Nat.clog 2 g.vertices)) ∧
    RB Δ γ g (Sum.inr 18) = u (320 * ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨o0, o8, o11, o12, o13, o16, o18⟩ := outputs g.vertices γ.num.toNat
    (γ.num.toNat * g.edges.length) (2 * γ.den * Δ) (6144 * γ.den)
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) (Nat.clog 2 g.vertices)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
  exact ⟨o0, o8, o11, o12, o13, o16, o18⟩

end

end SmallRatSched

#print axioms SmallRatSched.schedR_run
#print axioms SmallRatSched.printed
