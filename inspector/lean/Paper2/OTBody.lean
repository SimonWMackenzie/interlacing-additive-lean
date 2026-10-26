import Paper2.OTOps
import Paper2.OuterTokenFetch
import Paper2.RawRowSplit

/-! Unit 3, segment (1), outer-token equality, fixed-tail tag: ONE fixed body
program on ONE bank `B = FetchIndexed.Stack ⊕ Fin 8`, one iteration of the
outer-token loop at outer index `pp`:

1. the production `FetchIndexed.colProgram` (lifted by `Sum.inl`) with the
   outer code fetches outer word `pp` NON-destructively into the label cell
   (the checked `OuterTokenFetch.fixed_outer_fetch`);
2. the production `RawRowSplit.readU` moves its unary token `(js pp).1` to
   cell `tC` (`OuterTokenFetch.outer_word_token`);
3. `OTOps.clr` clears the rest of the fetched word;
4. the production `MatrixStage4ScalarPreparationOps.copyProgram` copies the
   stored unary token `a` (cell `aC`) to `xC` (scratch `zC`);
5. `OTOps.cmp` compares and clears `xC`, `tC`, pushing `decide (a = (js pp).1)`
   on the accumulator `accC`;
6. `OTOps.inc` pushes one mark on the unary index cell.

Every handoff is a charged `BitMachineRawSequence` step. The counter cell
`ctrC`, `eqC` and `sC` are untouched (used by the loop module). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.OTBody

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)

abbrev B := FetchIndexed.Stack ⊕ Fin 8

def fI : FetchIndexed.Stack ↪ B := ⟨Sum.inl, Sum.inl_injective⟩

def aC : B := .inr 0
def tC : B := .inr 1
def xC : B := .inr 2
def zC : B := .inr 3
def accC : B := .inr 4
def ctrC : B := .inr 5
def eqC : B := .inr 6
def sC : B := .inr 7
def lblB : B := .inl (.inl FetchLabel.lblC)
def idxB : B := .inl FetchIndexed.idxC

/-- The bank: the `FetchIndexed` bank (blank skipper, code, counter cells)
with label `lbl`, the retained word `fw`, the three retained code cells and
the unary index, beside the eight lane cells. -/
def BB (lbl fw cc rc my idx a t x acc ctr eqv sU : List Bool) : B → List Bool :=
  Sum.elim (FetchIndexed.FB [] [] [] lbl fw cc rc my idx) ![a, t, x, [], acc, ctr, eqv, sU]

/-! ### Transport -/

theorem lift {K L V : Type*} [DecidableEq K] (ι : K ↪ B)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (W : B → List Bool) (S T : K → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : B => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem bank_fI (X Z : FetchIndexed.Stack → List Bool) (Y : Fin 8 → List Bool) :
    bank fI (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext j
  cases j with
  | inl j => exact bank_at fI _ Z j
  | inr j => exact bank_outside fI _ Z (.inr j) (by rintro ⟨k, hk⟩; cases hk)

/-! ### Bank updates -/

section Upd
variable (lbl fw cc rc my idx a t x acc ctr eqv sU y : List Bool)

theorem upd_lbl : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) lblB y =
    BB y fw cc rc my idx a t x acc ctr eqv sU := by
  funext j
  rcases j with ((j | j) | j) | j
  · simp [BB, lblB, FetchIndexed.FB, FetchLabel.fb, FetchLabel.lblC, Function.update_apply]
  · fin_cases j <;> simp [BB, lblB, FetchIndexed.FB, FetchLabel.fb, FetchLabel.lblC,
      FetchLabel.ext4, Function.update_apply]
  · simp [BB, lblB, FetchIndexed.FB, FetchLabel.fb, FetchLabel.lblC, Function.update_apply]
  · simp [BB, lblB, Function.update_apply]

theorem upd_idx : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) idxB y =
    BB lbl fw cc rc my y a t x acc ctr eqv sU := by
  funext j
  rcases j with ((j | j) | j) | j
  · simp [BB, idxB, FetchIndexed.FB, FetchIndexed.idxC, Function.update_apply]
  · simp [BB, idxB, FetchIndexed.FB, FetchIndexed.idxC, Function.update_apply]
  · fin_cases j <;> simp [BB, idxB, FetchIndexed.FB, FetchIndexed.idxC,
      FetchIndexed.ext5, Function.update_apply]
  · simp [BB, idxB, Function.update_apply]

theorem upd_a : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) aC y =
    BB lbl fw cc rc my idx y t x acc ctr eqv sU := by
  funext j
  rcases j with j | j
  · simp [BB, aC, Function.update_apply]
  · fin_cases j <;> simp [BB, aC, Function.update_apply]

theorem upd_t : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) tC y =
    BB lbl fw cc rc my idx a y x acc ctr eqv sU := by
  funext j
  rcases j with j | j
  · simp [BB, tC, Function.update_apply]
  · fin_cases j <;> simp [BB, tC, Function.update_apply]

theorem upd_x : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) xC y =
    BB lbl fw cc rc my idx a t y acc ctr eqv sU := by
  funext j
  rcases j with j | j
  · simp [BB, xC, Function.update_apply]
  · fin_cases j <;> simp [BB, xC, Function.update_apply]

theorem upd_acc : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) accC y =
    BB lbl fw cc rc my idx a t x y ctr eqv sU := by
  funext j
  rcases j with j | j
  · simp [BB, accC, Function.update_apply]
  · fin_cases j <;> simp [BB, accC, Function.update_apply]

theorem upd_ctr : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) ctrC y =
    BB lbl fw cc rc my idx a t x acc y eqv sU := by
  funext j
  rcases j with j | j
  · simp [BB, ctrC, Function.update_apply]
  · fin_cases j <;> simp [BB, ctrC, Function.update_apply]

theorem upd_eq : Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) eqC y =
    BB lbl fw cc rc my idx a t x acc ctr y sU := by
  funext j
  rcases j with j | j
  · simp [BB, eqC, Function.update_apply]
  · fin_cases j <;> simp [BB, eqC, Function.update_apply]

theorem BB_lbl : BB lbl fw cc rc my idx a t x acc ctr eqv sU lblB = lbl := rfl
theorem BB_idx : BB lbl fw cc rc my idx a t x acc ctr eqv sU idxB = idx := rfl
theorem BB_a : BB lbl fw cc rc my idx a t x acc ctr eqv sU aC = a := rfl
theorem BB_t : BB lbl fw cc rc my idx a t x acc ctr eqv sU tC = t := rfl
theorem BB_x : BB lbl fw cc rc my idx a t x acc ctr eqv sU xC = x := rfl
theorem BB_z : BB lbl fw cc rc my idx a t x acc ctr eqv sU zC = [] := rfl
theorem BB_acc : BB lbl fw cc rc my idx a t x acc ctr eqv sU accC = acc := rfl
theorem BB_ctr : BB lbl fw cc rc my idx a t x acc ctr eqv sU ctrC = ctr := rfl
theorem BB_eq : BB lbl fw cc rc my idx a t x acc ctr eqv sU eqC = eqv := rfl
theorem BB_s : BB lbl fw cc rc my idx a t x acc ctr eqv sU sC = sU := rfl

theorem BB_fI : BB lbl fw cc rc my idx a t x acc ctr eqv sU =
    Sum.elim (FetchIndexed.FB [] [] [] lbl fw cc rc my idx) ![a, t, x, [], acc, ctr, eqv, sU] :=
  rfl

end Upd

/-! ### Programs -/

def cpFun : Fin 3 → B := ![aC, xC, zC]

theorem cpFun_injective : Function.Injective cpFun := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cpFun, aC, xC, zC]

def cpSlots : Fin 3 ↪ B := ⟨cpFun, cpFun_injective⟩

def P1 := fun l => stackStmt fI (FetchIndexed.colProgram l)
def P2 := RawRowSplit.readU lblB tC
def P3 := OTOps.clr lblB
def P4 := MatrixStage4ScalarPreparationOps.copyProgram cpSlots
def P5 := OTOps.cmp xC tC accC
def P6 := OTOps.inc idxB

abbrev ob := (none : Option Bool)

def b1 := BitMachineRawSequence.program P1 P2 () FetchIndexed.colControl ob
def b2 := BitMachineRawSequence.program b1 P3 () (FetchIndexed.colControl, ob) ob
def b3 := BitMachineRawSequence.program b2 P4 BitMachineCopy.Label.scan
  ((FetchIndexed.colControl, ob), ob) ob
def b4 := BitMachineRawSequence.program b3 P5 OTOps.CL.cmp
  (((FetchIndexed.colControl, ob), ob), ob) ((ob, ob) : OTOps.CCtl)
/-- The loop body: one fixed program. -/
def body := BitMachineRawSequence.program b4 P6 ()
  ((((FetchIndexed.colControl, ob), ob), ob), ((ob, ob) : OTOps.CCtl)) ob

def bodyStart := FetchIndexed.labelOf body
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel FetchIndexed.colStart)))))
def bodyCtl := (((((FetchIndexed.colControl, ob), ob), ob), ((ob, ob) : OTOps.CCtl)), ob)

variable {n p s q₁ q₂ w Q : ℕ}
  [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The exact clock of one body run at outer index `pp` with stored token `a`. -/
def bodyBound (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O : List Bool) (a : ℕ) (pp : Fin s) : ℕ :=
  let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
  let oc := outerColumnCodec q₁ q₂ s C.2
  let rc := outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2
  let cs := List.ofFn (fun a : Fin s => oc.encode (js a))
  ((((FetchIndexed.colBound rc cs pp.val O + ((js pp).1.val + 1) + 1) +
    (((piCodec C.2 (q₁ + s + 1)).encode (js pp).2).length + 1) + 1) + (2 * a + 2) + 1) +
    (a + (js pp).1.val + 3) + 1) + 1 + 1

/-- One body run: fetch outer word `pp`, compare its token with the stored
token `a`, push the answer bit, advance the unary index. Exact banks. -/
theorem body_run (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (pp : Fin s) (O r1 r2 acc ctr sU : List Bool) (a : ℕ) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let oc := outerColumnCodec q₁ q₂ s C.2
    let rc := outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let fw := (piCodec oc s).encode js ++ O
    ∃ t ≤ bodyBound k js O a pp, ∃ v,
      ((advance body)^[t])
        (⟨some bodyStart, bodyCtl,
          BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] acc ctr [] sU⟩ :
          TM2.Cfg (fun _ : B => Bool) _ _) =
        ⟨none, v, BB [] fw (encodeCode rc) r1 r2 (u (pp.val + 1)) (u a) [] []
          (decide (a = (js pp).1.val) :: acc) ctr [] sU⟩ := by
  intro C oc rc fw
  -- 1. fetch
  obtain ⟨t1, ht1, v1, h1⟩ := OuterTokenFetch.fixed_outer_fetch (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k js pp O r1 r2
  have l1 := lift fI FetchIndexed.colProgram
    (BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] acc ctr [] sU) _ _ (fun _ => rfl)
    _ _ _ _ h1
  have e1 : bank fI (BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] acc ctr [] sU)
      (FetchIndexed.FB [] [] [] (oc.encode (js pp)) fw (encodeCode rc) r1 r2
        (List.replicate pp.val true)) =
      BB (oc.encode (js pp)) fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] acc ctr [] sU :=
    bank_fI _ _ _
  rw [e1] at l1
  -- 2. token split
  have htok := OuterTokenFetch.outer_word_token (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) k (js pp)
  set body' := (piCodec C.2 (q₁ + s + 1)).encode (js pp).2 with hbody'
  have hne2 : lblB ≠ tC := by simp [lblB, tC]
  have l2 := RawRowSplit.readU_run lblB tC hne2 (js pp).1.val body' []
    (BB (oc.encode (js pp)) fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] acc ctr [] sU)
    none (by rw [BB_lbl]; exact htok) rfl
  rw [upd_lbl, upd_t, List.append_nil] at l2
  -- 3. clear the rest of the fetched word
  have l3 := OTOps.clr_run lblB body'
    (BB body' fw (encodeCode rc) r1 r2 (u pp.val) (u a) (List.replicate (js pp).1.val true) []
      acc ctr [] sU) ob rfl
  rw [upd_lbl] at l3
  -- 4. copy the stored token
  have l4 := MatrixStage4ScalarPreparationOps.copy_run cpSlots
    (BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) (List.replicate (js pp).1.val true) []
      acc ctr [] sU) rfl
  have hc0 : cpSlots 0 = aC := rfl
  have hc1 : cpSlots 1 = xC := rfl
  rw [hc0, hc1, BB_a, BB_x, List.append_nil, upd_x] at l4
  -- 5. compare and clear
  have hxt : xC ≠ tC := by simp [xC, tC]
  have hxa : xC ≠ accC := by simp [xC, accC]
  have hta : tC ≠ accC := by simp [tC, accC]
  obtain ⟨t5, ht5, v5, l5⟩ := OTOps.cmp_run xC tC accC hxt hxa hta a (js pp).1.val
    (BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) (List.replicate (js pp).1.val true) (u a)
      acc ctr [] sU) (ob, ob) rfl rfl
  simp only [OTOps.F] at l5
  rw [upd_x, upd_t, BB_acc, upd_acc] at l5
  -- 6. increment the index
  have l6 := OTOps.inc_run idxB
    (BB [] fw (encodeCode rc) r1 r2 (u pp.val) (u a) [] [] (decide (a = (js pp).1.val) :: acc)
      ctr [] sU) ob
  rw [BB_idx, upd_idx] at l6
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs P1 P2 FetchIndexed.colStart ()
    FetchIndexed.colControl v1 ob (some false) _ _ _ _ _ l1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs b1 P3 (leftLabel FetchIndexed.colStart) ()
    (FetchIndexed.colControl, ob) (FetchIndexed.colControl, some false) ob ob _ _ _ _ _ q1 l3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs b2 P4
    (leftLabel (leftLabel FetchIndexed.colStart)) BitMachineCopy.Label.scan
    ((FetchIndexed.colControl, ob), ob) ((FetchIndexed.colControl, ob), ob) ob ob
    _ _ _ _ _ q2 l4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs b3 P5
    (leftLabel (leftLabel (leftLabel FetchIndexed.colStart))) OTOps.CL.cmp
    (((FetchIndexed.colControl, ob), ob), ob) (((FetchIndexed.colControl, ob), ob), ob)
    ((ob, ob) : OTOps.CCtl) v5 _ _ _ _ _ q3 l5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs b4 P6
    (leftLabel (leftLabel (leftLabel (leftLabel FetchIndexed.colStart)))) ()
    ((((FetchIndexed.colControl, ob), ob), ob), ((ob, ob) : OTOps.CCtl))
    ((((FetchIndexed.colControl, ob), ob), ob), v5) ob ob _ _ _ _ _ q4 l6
  refine ⟨u5, ?_, _, q5⟩
  have ht1' : t1 ≤ FetchIndexed.colBound (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
      (List.ofFn fun a =>
        (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode (js a))
      pp.val O := ht1
  have hb : body'.length =
      ((piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (q₁ + s + 1)).encode (js pp).2).length :=
    rfl
  have hl : (u a).length = a := by simp [u]
  simp only [bodyBound]
  rw [hl] at hu3
  omega

#print axioms cpFun_injective
#print axioms lift
#print axioms bank_fI
#print axioms upd_lbl
#print axioms upd_idx
#print axioms body_run

end

end Paper2.OTBody
