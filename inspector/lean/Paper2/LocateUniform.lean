import Paper2.TagDispatch
import Paper2.FullSupport

/-! ONE fixed program locating the outer column `(forgetTag ξ₀ z).2 p` of an
encoded level-`k` tagged column `z`, with a tag-independent bank
precondition: work cell `fw` = the tagged word, `cc` = `copies (s+1) col_k`,
`rc` = `outerCode col_k`, `my` blank, `idx` = unary `p`, fetch scratch blank.
The fixed-tail branch reads its code through the embedding with `cc ↔ rc`
exchanged; the diagonal branch additionally reads its index from the blank
`my` cell (unary `0`) and captures the single remaining outer word. Exit
bank: the label cell holds the encoded outer column; only the named cells
`fw`, `my` and the label cell may change. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.LocateUniform

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries
open OutputSkipper (Shape)
open TagDispatch (ifProgram if_false if_true)

variable {J : Type*} [DecidableEq J]

def swapE (e : FetchIndexed.Stack ↪ J) : FetchIndexed.Stack ↪ J :=
  (Equiv.swap FetchIndexed.ccC FetchIndexed.rcC).toEmbedding.trans e

def diagE (e : FetchIndexed.Stack ↪ J) : FetchIndexed.Stack ↪ J :=
  (Equiv.swap FetchIndexed.idxC FetchIndexed.myC).toEmbedding.trans (swapE e)

theorem swapE_apply (e : FetchIndexed.Stack ↪ J) (x : FetchIndexed.Stack) :
    swapE e x = e (Equiv.swap FetchIndexed.ccC FetchIndexed.rcC x) := rfl
theorem diagE_apply (e : FetchIndexed.Stack ↪ J) (x : FetchIndexed.Stack) :
    diagE e x = e (Equiv.swap FetchIndexed.ccC FetchIndexed.rcC
      (Equiv.swap FetchIndexed.idxC FetchIndexed.myC x)) := rfl

def fixedBody (e : FetchIndexed.Stack ↪ J) :=
  fun l => stackStmt (swapE e) (FetchIndexed.colProgram l)
def diagBody (e : FetchIndexed.Stack ↪ J) :=
  fun l => stackStmt (diagE e) (FetchIndexed.colProgram l)
def inner (e : FetchIndexed.Stack ↪ J) :=
  ifProgram (e FetchIndexed.fwC) (fixedBody e) (diagBody e) FetchIndexed.colStart
    FetchIndexed.colStart FetchIndexed.colControl FetchIndexed.colControl
def program (e : FetchIndexed.Stack ↪ J) :=
  ifProgram (e FetchIndexed.fwC) (TagDispatch.unresBody e) (inner e)
    (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
    ((none : Option Bool), (FetchIndexed.colControl, FetchIndexed.colControl))

def startControl := ((none : Option Bool), (((), FetchIndexed.rowControl),
  ((none : Option Bool), (FetchIndexed.colControl, FetchIndexed.colControl))))

/-- Only the named cells may change. -/
def Frame (e : FetchIndexed.Stack ↪ J) (W F : J → List Bool) : Prop :=
  ∀ x, x ≠ e FetchIndexed.fwC → x ≠ e FetchIndexed.myC →
    x ≠ e SuccessFetchJoin.lblF → F x = W x

/-- Explicit per-tag clock. -/
def locBound {Y : Type} (q₁ q₂ s : ℕ) (cy : PrefixCodec Y) (col : Code) (pp : ℕ) :
    SourceMatrix.TaggedColumn q₁ q₂ s Y → ℕ
  | .fixedTail js => FetchIndexed.colBound (outerCode q₁ q₂ s col)
      (List.ofFn (fun a => (outerColumnCodec q₁ q₂ s cy).encode (js a))) pp [] + 2
  | .diagonal j => FetchIndexed.colBound (outerCode q₁ q₂ s col)
      [(outerColumnCodec q₁ q₂ s cy).encode j] 0 [] + 2
  | .unrestricted Z => 1 + FetchIndexed.rowBound (copies (s + 1) col) (outerCode q₁ q₂ s col)
      [(piCodec cy (s + 1)).encode Z.1]
      (List.ofFn (fun a => (outerColumnCodec q₁ q₂ s cy).encode (Z.2 a))) pp [] + 3

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem locate_run (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (z : SourceMatrix.TaggedColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (ξ₀ : SourceMatrix.Tail s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (pp : Fin s) (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = (taggedColumnCodec q₁ q₂ s
      (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode z)
    (hcc : W (e FetchIndexed.ccC) =
      encodeCode (copies (s + 1) (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
    (hrc : W (e FetchIndexed.rcC) =
      encodeCode (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
    (hmy : W (e FetchIndexed.myC) = [])
    (hidx : W (e FetchIndexed.idxC) = List.replicate pp.val true) :
    ∃ t ≤ locBound q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2
        (seedRecursiveCodes n p s q₁ q₂ w Q k).2 pp.val z,
      ∃ v, ∃ F : J → List Bool,
      ((advance (program e))^[t])
        (⟨some (.inl ()), startControl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (e SuccessFetchJoin.lblF) =
        (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode
          ((SourceMatrix.forgetTag ξ₀ z).2 pp) ∧
      Frame e W F := by
  obtain ⟨-, -, -, hout, -, -⟩ := FullSupport.subcodes_full (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k
  obtain ⟨-, fc⟩ := FullSupport.seed_programs_full (n := n) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k
  have hcolex := FullSupport.col_exact (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k
  have hshape := OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)
  have hK1 := OutputSkipper.shape_copies (s + 1) _ hshape.2
  have hK2 := OutputSkipper.shape_outer q₁ q₂ s _ hshape.2
  have hne : ∀ x y : FetchIndexed.Stack, x ≠ y → e x ≠ e y := fun x y hx h => hx (e.injective h)
  have hlS : swapE e SuccessFetchJoin.lblF = e SuccessFetchJoin.lblF := by
    rw [swapE_apply, Equiv.swap_apply_of_ne_of_ne
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.ccC])
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.rcC])]
  have hlD : diagE e SuccessFetchJoin.lblF = e SuccessFetchJoin.lblF := by
    rw [diagE_apply, Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.idxC) (b := FetchIndexed.myC)
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.idxC])
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.myC]),
      Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.ccC) (b := FetchIndexed.rcC)
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.ccC])
      (by simp [SuccessFetchJoin.lblF, FetchIndexed.rcC])]
  cases z with
  | fixedTail js =>
    let oc := outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2
    let cs := List.ofFn (fun a => oc.encode (js a))
    have hcs : ∀ u ∈ cs, Produces (meaning (outerCode q₁ q₂ s
        (seedRecursiveCodes n p s q₁ q₂ w Q k).2)) u := by
      intro u hu; obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu; exact hout _
    have hflat : (piCodec oc s).encode js = cs.flatten := by
      rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
    have hp' : pp.val < cs.length := by simp [cs]
    let W1 := Function.update W (e FetchIndexed.fwC) (false :: cs.flatten)
    let W2 := Function.update W (e FetchIndexed.fwC) cs.flatten
    have hW12 : Function.update W1 (e FetchIndexed.fwC) cs.flatten = W2 := by
      simp only [W1, W2, Function.update_idem]
    obtain ⟨t2, ht2, v2, p2⟩ := SuccessFetchJoin.lift_col (swapE e) W2 _ hK2 cs hcs [] pp.val hp'
      (fun j => by
        rw [swapE_apply, Equiv.swap_apply_of_ne_of_ne (by simp [FetchIndexed.ccC])
          (by simp [FetchIndexed.rcC])]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.fwC]))]; exact hin j)
      (by
        rw [swapE_apply, Equiv.swap_apply_of_ne_of_ne
          (by simp [FetchIndexed.fwC, FetchIndexed.ccC])
          (by simp [FetchIndexed.fwC, FetchIndexed.rcC])]
        simp [W2])
      (by
        rw [swapE_apply, Equiv.swap_apply_left]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.rcC, FetchIndexed.fwC]))]
        exact hrc)
      (by
        rw [swapE_apply, Equiv.swap_apply_of_ne_of_ne
          (by simp [FetchIndexed.idxC, FetchIndexed.ccC])
          (by simp [FetchIndexed.idxC, FetchIndexed.rcC])]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.idxC, FetchIndexed.fwC]))]
        exact hidx)
    rw [← hW12] at p2
    obtain ⟨t1, ht1, q1⟩ := if_false (e FetchIndexed.fwC) (fixedBody e) (diagBody e)
      FetchIndexed.colStart FetchIndexed.colStart FetchIndexed.colControl
      FetchIndexed.colControl W1 cs.flatten (by simp [W1]) t2 v2 _ p2
    obtain ⟨t0, ht0, q0⟩ := if_true (e FetchIndexed.fwC) (TagDispatch.unresBody e) (inner e)
      (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
      ((none : Option Bool), (FetchIndexed.colControl, FetchIndexed.colControl)) W
      (false :: cs.flatten) (by rw [hfw, ← hflat]; rfl) t1 _ _ q1
    rw [hW12, hlS] at q0
    have ht2' : t2 ≤ FetchIndexed.colBound (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
        (List.ofFn fun a => (outerColumnCodec q₁ q₂ s
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode (js a)) pp.val [] := ht2
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · simp only [locBound]; omega
    · rw [Function.update_self]
      simp [cs, List.getD_eq_getElem?_getD, oc, SourceMatrix.forgetTag]
    · intro x h1 _ h3
      rw [Function.update_of_ne h3]
      simp only [W2]
      rw [Function.update_of_ne h1]
  | diagonal j =>
    let oc := outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2
    let O := oc.encode j
    have hO : Produces (meaning (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)) O :=
      hout _
    let W1 := Function.update W (e FetchIndexed.fwC) (true :: O)
    let W2 := Function.update W (e FetchIndexed.fwC) O
    have hW12 : Function.update W1 (e FetchIndexed.fwC) O = W2 := by
      simp only [W1, W2, Function.update_idem]
    obtain ⟨t2, ht2, v2, p2⟩ := SuccessFetchJoin.lift_col (diagE e) W2 _ hK2 [O]
      (by intro u hu; simp at hu; subst hu; exact hO) [] 0 (by simp)
      (fun i => by
        rw [diagE_apply, Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.idxC) (b := FetchIndexed.myC) (by simp [FetchIndexed.idxC])
          (by simp [FetchIndexed.myC]), Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.ccC) (b := FetchIndexed.rcC)
          (by simp [FetchIndexed.ccC]) (by simp [FetchIndexed.rcC])]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.fwC]))]; exact hin i)
      (by
        rw [diagE_apply, Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.idxC) (b := FetchIndexed.myC)
          (by simp [FetchIndexed.fwC, FetchIndexed.idxC])
          (by simp [FetchIndexed.fwC, FetchIndexed.myC]), Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.ccC) (b := FetchIndexed.rcC)
          (by simp [FetchIndexed.fwC, FetchIndexed.ccC])
          (by simp [FetchIndexed.fwC, FetchIndexed.rcC])]
        simp [W2])
      (by
        rw [diagE_apply, Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.idxC) (b := FetchIndexed.myC)
          (by simp [FetchIndexed.ccC, FetchIndexed.idxC])
          (by simp [FetchIndexed.ccC, FetchIndexed.myC]), Equiv.swap_apply_left]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.rcC, FetchIndexed.fwC]))]
        exact hrc)
      (by
        rw [diagE_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (a := FetchIndexed.ccC) (b := FetchIndexed.rcC)
          (by simp [FetchIndexed.myC, FetchIndexed.ccC])
          (by simp [FetchIndexed.myC, FetchIndexed.rcC])]
        simp only [W2]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.myC, FetchIndexed.fwC]))]
        simpa using hmy)
    rw [← hW12] at p2
    obtain ⟨t1, ht1, q1⟩ := if_true (e FetchIndexed.fwC) (fixedBody e) (diagBody e)
      FetchIndexed.colStart FetchIndexed.colStart FetchIndexed.colControl
      FetchIndexed.colControl W1 O (by simp [W1]) t2 v2 _ p2
    obtain ⟨t0, ht0, q0⟩ := if_true (e FetchIndexed.fwC) (TagDispatch.unresBody e) (inner e)
      (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
      ((none : Option Bool), (FetchIndexed.colControl, FetchIndexed.colControl)) W
      (true :: O) (by rw [hfw]; rfl) t1 _ _ q1
    rw [hW12, hlD] at q0
    have ht2' : t2 ≤ FetchIndexed.colBound (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
        [(outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode j] 0 [] := ht2
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · simp only [locBound]; omega
    · rw [Function.update_self]
      simp [O, oc, SourceMatrix.forgetTag]
    · intro x h1 _ h3
      rw [Function.update_of_ne h3]
      simp only [W2]
      rw [Function.update_of_ne h1]
  | unrestricted Z =>
    let oc := outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2
    let z1 := (piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (s + 1)).encode Z.1
    let rs := List.ofFn (fun a => oc.encode (Z.2 a))
    have hz1 : Produces (meaning (copies (s + 1) (seedRecursiveCodes n p s q₁ q₂ w Q k).2)) z1 :=
      FullSupport.code_full (copies_exact (s + 1) _ _ _ hcolex) (FullSupport.full_iid fc _) Z.1
    have hrs : ∀ u ∈ rs, Produces (meaning (outerCode q₁ q₂ s
        (seedRecursiveCodes n p s q₁ q₂ w Q k).2)) u := by
      intro u hu; obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu; exact hout _
    have hflat : (piCodec oc s).encode Z.2 = rs.flatten := by
      rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
    have hp' : pp.val < rs.length := by simp [rs]
    let W1 := Function.update W (e FetchIndexed.fwC) (z1 ++ rs.flatten)
    have p1 := OuterLocate.pushOne_run (e FetchIndexed.myC) W1
      (by simp only [W1]
          rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.myC, FetchIndexed.fwC]))]
          exact hmy)
    let W2 := Function.update W1 (e FetchIndexed.myC) [true]
    have hW2 : ∀ x : FetchIndexed.Stack, x ≠ FetchIndexed.fwC → x ≠ FetchIndexed.myC →
        W2 (e x) = W (e x) := by
      intro x h1 h2
      simp only [W2, W1]
      rw [Function.update_of_ne (hne _ _ h2), Function.update_of_ne (hne _ _ h1)]
    obtain ⟨t3, ht3, v3, p3⟩ := SuccessFetchJoin.lift_row e W2 _ _ hK1 hK2 [z1] rs
      (by intro c hc; simp at hc; subst hc; exact hz1) hrs [] pp.val hp'
      (fun j => by
        rw [hW2 _ (by simp [FetchIndexed.fwC]) (by simp [FetchIndexed.myC])]
        exact hin j)
      (by
        simp only [W2, W1]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.myC, FetchIndexed.fwC])),
          Function.update_self]
        simp)
      (by rw [hW2 _ (by simp [FetchIndexed.ccC, FetchIndexed.fwC])
          (by simp [FetchIndexed.ccC, FetchIndexed.myC])]; exact hcc)
      (by rw [hW2 _ (by simp [FetchIndexed.rcC, FetchIndexed.fwC])
          (by simp [FetchIndexed.rcC, FetchIndexed.myC])]; exact hrc)
      (by simp [W2])
      (by rw [hW2 _ (by simp [FetchIndexed.idxC, FetchIndexed.fwC])
          (by simp [FetchIndexed.idxC, FetchIndexed.myC])]; exact hidx)
    obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs (OuterLocate.pushOne (e FetchIndexed.myC))
      (fun l => stackStmt e (FetchIndexed.rowProgram l)) () FetchIndexed.rowStart
      () () FetchIndexed.rowControl v3 _ _ _ _ _ p1 p3
    obtain ⟨t0, ht0, q0⟩ := if_false (e FetchIndexed.fwC) (TagDispatch.unresBody e) (inner e)
      (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
      ((none : Option Bool), (FetchIndexed.colControl, FetchIndexed.colControl)) W
      (z1 ++ rs.flatten) (by rw [hfw, ← hflat]; rfl) r1 _ _ q1
    have ht3' : t3 ≤ FetchIndexed.rowBound (copies (s + 1) (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
        (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
        [(piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (s + 1)).encode Z.1]
        (List.ofFn fun a => (outerColumnCodec q₁ q₂ s
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode (Z.2 a)) pp.val [] := ht3
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · simp only [locBound]; omega
    · rw [Function.update_self]
      simp [rs, List.getD_eq_getElem?_getD, oc, SourceMatrix.forgetTag]
    · intro x h1 h2 h3
      rw [Function.update_of_ne h3]
      simp only [W2, W1]
      rw [Function.update_of_ne h2, Function.update_of_ne h1]

end

#print axioms locate_run

end Paper2.LocateUniform
