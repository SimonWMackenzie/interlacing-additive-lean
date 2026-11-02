import Paper2.A3LUnsched
import Paper2.A3H3ClockN

/-!
# Unit 3 lift, owner-3 segment 1: hNone (the none-outcome branch) on the H_A3 layout bank

Lane `owner:a-h-a3-lift-3` (private, 26 September 2026). Layout, `Mid2`, `size_run`, `liftP`: frozen owner-1
`A3LLayout` (imported). The branch program is the frozen owner-2 `NoneOut.progN` (the ONE program of
`NoneOut.none_run_canonical`) lifted by ONE stack embedding `ιN`:

* its start region `OS` goes to the master start region (`ιN (.inl x) = ιOS x`); under `Mid2` that region holds
  EXACTLY `startCanon`, which is literally the `OS` part of `NoneOut.entryN` at the canonical counts with
  `word = tapeBits t` (`entryCanon_layout`, by `rfl` on that component);
* its `TK` and `HB` cells go to the (blank) none region, except the header output cell `HeaderA.outH`, which goes to
  the common output cell `outJ` (blank under `Mid2`).

So the entry bank is the `Mid2` bank itself: no copy, no inserted value. The clock is `Clocks.clockN_HA3`; the final
bank size comes from `size_run`.

`Mid2 ∧ ¬ Good` alone does NOT determine the branch: `none_run_canonical` needs `Checks`, and `Mid2` (as fixed by
owner-1) does not record it. The probe precondition contains `Checks`, so every probe `DecideSpec` with exit `Mid2`
is also one with exit `Mid2 ∧ Checks` (`decide_add_cond`, segment 2). `hNone` is therefore proved from
`(Mid2 ∧ Checks) ∧ ¬ GoodN`, where `GoodN` is the LAYOUT.md condition written out literally.

Finite control: the labels and controls of `NoneOut.progN` contain the list-recursive types `CopyList.Label/Control`,
`SamplerAlphabetMachine.Label/Control` and the inductive `SamplerLoopDraw.Label`, which carry no `Fintype`
instance in the admitted objects. The fallback instances derived by owner-1 (`A3LUnsched`) are IMPORTED, not
re-derived; the five missing ones are defined below under lane-unique names (no production declaration changed).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 16384

namespace Paper2.A3Assembly.Lift3

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly.Lift
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-! ### Finite-control instances missing from the admitted objects (lane-unique names) -/

instance lift3FtCLL {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Label xs)
  | [] => show Fintype Unit from inferInstance
  | _ :: xs => by
      haveI := lift3FtCLL xs
      exact show Fintype (BitMachineRawSequence.Label BitMachineCopy.Label (CopyList.Label xs)) from
        inferInstance

instance lift3FtCLC {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Control xs)
  | [] => show Fintype Unit from inferInstance
  | _ :: xs => by
      haveI := lift3FtCLC xs
      exact show Fintype (Option Bool × CopyList.Control xs) from inferInstance

instance lift3FtSAL :
    (xs : List SamplerAlphabetMachine.Source) → Fintype (SamplerAlphabetMachine.Label xs)
  | [] => show Fintype (SourceClauseFixedUnary.Label 514) from inferInstance
  | _ :: xs => by
      haveI := lift3FtSAL xs
      exact show Fintype (BitMachineRawSequence.Label (SamplerAlphabetMachine.Label xs)
        BitMachineCopy.Label) from inferInstance

instance lift3FtSAC :
    (xs : List SamplerAlphabetMachine.Source) → Fintype (SamplerAlphabetMachine.Control xs)
  | [] => show Fintype Unit from inferInstance
  | _ :: xs => by
      haveI := lift3FtSAC xs
      exact show Fintype (SamplerAlphabetMachine.Control xs × Option Bool) from inferInstance

/-- `SamplerLoopDraw.Label` as a sum type. -/
def lift3SLDEquiv : SamplerLoopDraw.Label ≃
    SamplerAffineLoop.Label ⊕ (Unit ⊕ (Bool × SamplerDrawCount.Label)) where
  toFun
    | .loop l => .inl l
    | .dispatch => .inr (.inl ())
    | .draw b l => .inr (.inr (b, l))
  invFun
    | .inl l => .loop l
    | .inr (.inl _) => .dispatch
    | .inr (.inr (b, l)) => .draw b l
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with l | _ | ⟨b, l⟩ <;> rfl

instance lift3FtSLD : Fintype SamplerLoopDraw.Label :=
  Fintype.ofEquiv _ lift3SLDEquiv.symm

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-! ### The embedding of the none bank -/

/-- The none-region cell of a `TK ⊕ HB` cell. -/
def nReg (y : ThrProducer.TK ⊕ HeaderA.HB) : W FS := .inr (.inr (.inr (.inl (.inr y))))

/-- Layout position map of the none bank `JN = OS ⊕ (TK ⊕ HB)`: `OS` to the master start region, the header
output cell to the common output cell, every other cell to its own none-region cell. -/
def nMap : NoneOut.JN → W FS ⊕ Fin 3
  | .inl x => .inl (.inr (.inl x))
  | .inr (.inl y) => .inl (nReg FS (.inl y))
  | .inr (.inr (.inl h)) => .inl (nReg FS (.inr (.inl h)))
  | .inr (.inr (.inr i)) => if i = 5 then .inl (.inl 2) else .inl (nReg FS (.inr (.inr i)))

omit [Fintype FS] [DecidableEq FS] in
theorem nMap_injective : Function.Injective (nMap FS) := by
  intro x y h
  rcases x with x | x | x | x <;> rcases y with y | y | y | y <;>
    simp only [nMap, nReg] at h <;> (try split_ifs at h) <;> simp_all

def ιN : NoneOut.JN ↪ Fin (a FS + 3) :=
  ⟨fun x => pos FS (nMap FS x), fun x y h => nMap_injective FS (pos_injective FS h)⟩

theorem ιN_start (x : SuccessOrient.Stack) : ιN FS (.inl x) = ιOS FS x := rfl

theorem ιN_out : ιN FS (.inr (.inr HeaderA.outH)) = outJ FS := by
  simp [ιN, HeaderA.outH, nMap, outJ]

/-- The entry bank of `none_run_canonical` (the canonical counts, `word = tapeBits t`). -/
def entryCanon (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) : NoneOut.JN → List Bool :=
  NoneOut.entryN g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    ((select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)

/-- **The start check.** On a layout bank whose master start region is `startCanon` and whose output cell is blank,
every cell of the lifted none bank holds exactly the canonical entry bank: the `OS` part is `startCanon` itself
(`rfl`), every other cell is blank on both sides. -/
theorem entryCanon_layout (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (P : Fin 3 → List Bool) (c : Fin 3 → List Bool) (hc : c 2 = []) (Z : FS → List Bool)
    (x : NoneOut.JN) :
    entryCanon Δ γ g hg hn k t x =
      layoutBank FS P (region FS (startCanon Δ γ g hg hn k t) c Z) (ιN FS x) := by
  change _ = layoutBank FS P (region FS (startCanon Δ γ g hg hn k t) c Z) (pos FS (nMap FS x))
  rcases x with x | x | x | x
  · rw [show nMap FS (.inl x) = .inl (.inr (.inl x)) from rfl, layoutBank_inl]
    rfl
  · rw [show nMap FS (.inr (.inl x)) = .inl (nReg FS (.inl x)) from rfl, layoutBank_inl]
    rfl
  · rw [show nMap FS (.inr (.inr (.inl x))) = .inl (nReg FS (.inr (.inl x))) from rfl, layoutBank_inl]
    rfl
  · by_cases h5 : x = 5
    · subst h5
      rw [show nMap FS (.inr (.inr (.inr 5))) = .inl (.inl 2) from rfl, layoutBank_inl]
      change [] = c 2
      rw [hc]
    · rw [show nMap FS (.inr (.inr (.inr x))) = .inl (nReg FS (.inr (.inr x))) from if_neg h5,
        layoutBank_inl]
      rfl

/-! ### The outcome condition (LAYOUT.md `Good`, literal) -/

/-- The physical generator run of the scheduled branch on `physTape (selTape hc t)` (literally the run in the
hypothesis of `NoneOut.none_run_canonical`). -/
def genRun (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (hc : Run.ChecksCond Δ γ g hg hn k t) : Prop :=
  haveI : NeZero g.vertices := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices)) := ⟨by unfold width; positivity⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices) - 2) :=
    ⟨by have h := SourceProfileParameters.width_admissible (Nat.clog 2 g.vertices); omega⟩
  haveI : NeZero (outerWidth (Nat.clog 2 g.vertices)) := ⟨by unfold outerWidth; positivity⟩
  haveI : NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) :=
    ⟨by unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
        positivity⟩
  haveI : NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ) :=
    ⟨by rw [show ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ =
          2 ^ ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ from
          SourceOverheadBounds.actualQ_pow (V := Fin g.vertices) (E := Fin g.edges.length)
            (Nat.clog 2 g.vertices) γ Δ]
        positivity⟩
  let n := g.vertices
  let m := g.edges.length
  let edge := CanonicalEdgeTape.graphEdge g hg
  let L := Nat.clog 2 n
  let p := LookupSeed.width L
  let s := width L
  let q₁ := width L - 2
  let q₂ := outerWidth L
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let mX := sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
    (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
  let mY := sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
    (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
  (GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
      (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
          (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
          (NeZero.pos Q)))
      (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
        (SuccessIdent.selTape hn edge Δ γ k hc t))).isSome = true

/-- **Good** (LAYOUT.md, literal): `Checks` holds and the physical generator run on
`physTape (selTape hc t)` returns `some`. -/
def GoodN (Δ : ℕ) (γ : ℚ) : Run.Cond Δ γ := fun g hg hn k t =>
  ∃ hc : Run.ChecksCond Δ γ g hg hn k t, genRun Δ γ g hg hn k t hc

/-! ### The branch program and hNone -/

/-- The none branch program: `NoneOut.progN` lifted by `ιN` (production `stackStmt`). -/
def nProg := liftP (ιN FS) NoneOut.progN

/-- The per-step push bound of the branch program. -/
def PSN : ℕ := BitMachineStackGrowth.perStep (nProg FS)

/-- Clock constant (exponent `Clocks.EN`), from `Clocks.clockN_HA3`. -/
def NCk : ℕ := 12 * UnaryBinaryEncoding.coefficient + 229

/-- Branch constant (clock and final bank size). -/
def NC (CM : ℕ) : ℕ := NCk + CM + 2 * (a FS + 3) * PSN FS * NCk

/-- **Segment 1 (hNone).** Under `Mid2 ∧ Checks` and `¬ GoodN`, the fixed branch program (from the entry label and
control of `none_run_canonical`) halts within `NC·(n+2)^(max EM EN·(k+1))` with `outputBits` in the common output
cell, and the final bank has encoded size within the same bound. -/
theorem hNone_spec (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) :
    Run.BranchSpec Δ γ (a FS) (nProg FS)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))) NoneOut.ctlN (outJ FS)
      (fun g hg hn k t S => (Mid2 FS Δ γ CM EM g hg hn k t S ∧ Run.ChecksCond Δ γ g hg hn k t) ∧
        ¬ GoodN Δ γ g hg hn k t)
      (NC FS CM) (max EM Clocks.EN) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨⟨b₁, b₂, Z, hS⟩, hsz⟩, hc⟩, hnG⟩ := hpre
  haveI : NeZero g.vertices := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices)) := ⟨by unfold width; positivity⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices) - 2) :=
    ⟨by have h := SourceProfileParameters.width_admissible (Nat.clog 2 g.vertices); omega⟩
  haveI : NeZero (outerWidth (Nat.clog 2 g.vertices)) := ⟨by unfold outerWidth; positivity⟩
  haveI : NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) :=
    ⟨by unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
        positivity⟩
  haveI : NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ) :=
    ⟨by rw [show ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ =
          2 ^ ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ from
          SourceOverheadBounds.actualQ_pow (V := Fin g.vertices) (E := Fin g.edges.length)
            (Nat.clog 2 g.vertices) γ Δ]
        positivity⟩
  -- the none outcome of the physical generator run
  have key := NoneOut.none_run_canonical g hg hn Δ γ k hc t
  have key2 := key (by
    by_contra hne
    exact hnG ⟨hc, Option.ne_none_iff_isSome.mp hne⟩)
  obtain ⟨T, hT, ctl, d, G, F, H, -, hr, -, -, hH⟩ := key2
  -- the entry bank is the Mid2 bank itself
  have hbank : bank (ιN FS) S (entryCanon Δ γ g hg hn k t) = S := by
    apply bank_eq_self
    intro x
    rw [hS]
    exact entryCanon_layout FS Δ γ g hg hn k t _ _ rfl Z x
  have hr' : ((advance NoneOut.progN)^[T]) ⟨some _, NoneOut.ctlN, entryCanon Δ γ g hg hn k t⟩ = _ := hr
  have hL := congrArg (stackCfg (ιN FS) S) hr'
  rw [← BitMachineStackRun.run] at hL
  simp only [stackCfg] at hL
  rw [hbank] at hL
  -- clock
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (g.vertices + 2) ^ (max EM Clocks.EN * (k + 1)) := ⟨_, rfl⟩
  have hMQ : (g.vertices + 2) ^ (EM * (k + 1)) ≤ Q := by
    rw [hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hNQ : (g.vertices + 2) ^ (Clocks.EN * (k + 1)) ≤ Q := by
    rw [hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hCN := Clocks.clockN_HA3 (n := g.vertices) (m := g.edges.length) Δ γ hc k
  have hTk : T ≤ NCk * Q := (hT.trans hCN).trans (Nat.mul_le_mul_left _ hNQ)
  -- size
  have hsize := size_run (nProg FS) ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))),
    NoneOut.ctlN, S⟩ T
  have hr2 : ((advance (nProg FS))^[T]) ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))), NoneOut.ctlN, S⟩ =
      ⟨none, ctl, _⟩ := hL
  rw [hr2] at hsize
  rw [← hQdef]
  refine ⟨T, _, _, ?_, hr2, ?_, ?_⟩
  · have : NCk ≤ NC FS CM := by unfold NC; omega
    exact hTk.trans (Nat.mul_le_mul_right _ this)
  · rw [← ιN_out, bank_at]
    exact hH
  · have h1 : (BitMachineBankCodec.encode S).length ≤ CM * Q := hsz.trans (Nat.mul_le_mul_left _ hMQ)
    have h2 : 2 * (a FS + 3) * (PSN FS * T) ≤ 2 * (a FS + 3) * PSN FS * NCk * Q := by
      have := Nat.mul_le_mul_left (2 * (a FS + 3)) (Nat.mul_le_mul_left (PSN FS) hTk)
      calc 2 * (a FS + 3) * (PSN FS * T) ≤ 2 * (a FS + 3) * (PSN FS * (NCk * Q)) := this
        _ = 2 * (a FS + 3) * PSN FS * NCk * Q := by ring
    have e : NC FS CM * Q = NCk * Q + CM * Q + 2 * (a FS + 3) * PSN FS * NCk * Q := by
      unfold NC; ring
    refine le_trans (b := (BitMachineBankCodec.encode S).length + 2 * (a FS + 3) * (PSN FS * T)) hsize ?_
    rw [e]
    generalize 2 * (a FS + 3) * PSN FS * NCk * Q = X at h2
    generalize 2 * (a FS + 3) * (PSN FS * T) = Y at h2
    generalize NCk * Q = Z'
    omega

end

end Paper2.A3Assembly.Lift3

#print axioms Paper2.A3Assembly.Lift3.nMap_injective
#print axioms Paper2.A3Assembly.Lift3.ιN_out
#print axioms Paper2.A3Assembly.Lift3.entryCanon_layout
#print axioms Paper2.A3Assembly.Lift3.hNone_spec
