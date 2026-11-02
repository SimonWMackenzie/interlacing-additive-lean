import Paper2.SuccessFetchJoin
import Paper2.FullSupport

/-! Segment 2, item (2), first half of one physical `RecursiveEntries.request`
step (level `k+1 → k`): the *selection* half.

`request activity ξ k x y = baseRequest activity (y.2 (x y.1).1) (forgetTag (ξ k) (x y.1).2)`.
From the encoded level-`k+1` row word `X = C₁.encode x`, column word
`Y = C₂.encode y`, and the serialized sub-codes `E_k = append (ticket w)
(taggedCode col_k)` (row entry) and `G_k = graphRowsCode row_k` (raw row),
one fixed program
1. copies `Y` to a work cell (source-preserving),
2. reads the unary outer index `j = y.1` off the work cell,
3. fetches the `j`-th row entry of `X` (code-driven skip/capture with `E_k`),
4. reads the unary inner index `i = (x j).1` off that entry, leaving the
   tagged column word of `(x j).2`,
5. fetches the `i`-th raw row of `y.2` (code-driven skip/capture with `G_k`).
It halts with the literal words `taggedColumnCodec.encode (x y.1).2` and
`rawRowCodec.encode (y.2 (x y.1).1)` and every input cell retained.

The code-driven skipping of *arbitrary* (requested, not sampled) labels uses
`FullSupport.subcodes_full`. `forgetTag` / `baseRequest` (the second half)
are NOT in this file. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RequestSelect

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries
open OutputSkipper (Shape)

abbrev Inner := FetchLabel.Stack
abbrev Stack := Inner ⊕ (Inner ⊕ Fin 8)

def Xc : Stack := .inr (.inr 0)
def Yc : Stack := .inr (.inr 1)
def Ec : Stack := .inr (.inr 2)
def Gc : Stack := .inr (.inr 3)
def jc : Stack := .inr (.inr 4)
def remc : Stack := .inr (.inr 5)
def ic : Stack := .inr (.inr 6)
def sc : Stack := .inr (.inr 7)
def tagC : Stack := .inl FetchLabel.lblC
def rowC : Stack := .inr (.inl FetchLabel.lblC)

/-! ### Reading one terminated unary field -/

def readProg (src cnt : Stack) : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  fun _ => pop src (fun _ b => b)
    (branch (fun v => v.getD false) (push cnt (fun _ => true) (goto (fun _ => ()))) halt)

theorem read_true (src cnt : Stack) (hne : src ≠ cnt) (S : Stack → List Bool)
    (v : Option Bool) (tl : List Bool) (hS : S src = true :: tl) :
    advance (readProg src cnt) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨some (), some true, Function.update (Function.update S src tl) cnt (true :: S cnt)⟩ := by
  have h1 : Function.update S src tl cnt = S cnt := Function.update_of_ne (Ne.symm hne) _ _
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, readProg, hS, h1]

theorem read_false (src cnt : Stack) (S : Stack → List Bool)
    (v : Option Bool) (tl : List Bool) (hS : S src = false :: tl) :
    advance (readProg src cnt) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, some false, Function.update S src tl⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, readProg, hS]

theorem read_run (src cnt : Stack) (hne : src ≠ cnt) :
    ∀ (j : ℕ) (rest C : List Bool) (S : Stack → List Bool) (v : Option Bool),
      S src = List.replicate j true ++ false :: rest → S cnt = C →
      ((advance (readProg src cnt))^[j + 1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
        ⟨none, some false,
          Function.update (Function.update S src rest) cnt (List.replicate j true ++ C)⟩
  | 0, rest, C, S, v, hS, hC => by
      rw [Function.iterate_one, read_false src cnt S v rest (by simpa using hS)]
      have hc : Function.update S src rest cnt = C := by
        rw [Function.update_of_ne (Ne.symm hne), hC]
      simp only [List.replicate_zero, List.nil_append]
      rw [← hc, Function.update_eq_self]
  | j + 1, rest, C, S, v, hS, hC => by
      rw [Function.iterate_succ_apply,
        read_true src cnt hne S v (List.replicate j true ++ false :: rest)
          (by rw [hS, List.replicate_succ, List.cons_append])]
      rw [read_run src cnt hne j rest (true :: C) _ (some true)
        (by rw [Function.update_of_ne hne, Function.update_self])
        (by rw [Function.update_self, hC])]
      congr 1
      funext k
      by_cases h1 : k = cnt
      · subst h1
        simp only [Function.update_self]
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h2 : k = src
        · subst h2
          simp only [Function.update_self]
        · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h2]

/-! ### Explicit banks -/

def inner (a : List Bool) : Inner → List Bool := FetchLabel.fb (FetchLabel.eb []) [] [] [] a

def mk (a b : List Bool) (v : Fin 8 → List Bool) : Stack → List Bool :=
  Sum.elim (inner a) (Sum.elim (inner b) v)

def vec (X Y E G jw R iw : List Bool) : Fin 8 → List Bool := ![X, Y, E, G, jw, R, iw, []]

theorem inner_blank (j : Inner) (h : j ≠ FetchLabel.lblC) (a : List Bool) : inner a j = [] := by
  rcases j with ((j | j) | j) <;> fin_cases j <;> first | rfl | exact absurd rfl h

theorem inner_nil (j : Inner) : inner [] j = [] := by
  rcases j with ((j | j) | j) <;> fin_cases j <;> rfl

theorem inner_update (a x : List Bool) :
    Function.update (inner a) FetchLabel.lblC x = inner x := by
  funext j; rcases j with ((j | j) | j) <;> fin_cases j <;> rfl

theorem upd_A (a b : List Bool) (v : Fin 8 → List Bool) (x : List Bool) :
    Function.update (mk a b v) (.inl FetchLabel.lblC) x = mk x b v := by
  rw [mk, Sum.update_elim_inl, inner_update]; rfl

theorem upd_B (a b : List Bool) (v : Fin 8 → List Bool) (x : List Bool) :
    Function.update (mk a b v) (.inr (.inl FetchLabel.lblC)) x = mk a x v := by
  rw [mk, Sum.update_elim_inr, Sum.update_elim_inl, inner_update]; rfl

theorem upd_vec (a b : List Bool) (v : Fin 8 → List Bool) (q : Fin 8) (x : List Bool) :
    Function.update (mk a b v) (.inr (.inr q)) x = mk a b (Function.update v q x) := by
  rw [mk, Sum.update_elim_inr, Sum.update_elim_inr]; rfl

/-! ### The two fetch embeddings -/

def embAFun : FetchIndexed.Stack → Stack
  | .inl j => .inl j
  | .inr j => (![Xc, Ec, Gc, Yc, jc] : Fin 5 → Stack) j

theorem embAFun_injective : Function.Injective embAFun := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [embAFun] using h
  · fin_cases b <;> simp [embAFun, Xc, Ec, Gc, Yc, jc] at h
  · fin_cases a <;> simp [embAFun, Xc, Ec, Gc, Yc, jc] at h
  · fin_cases a <;> fin_cases b <;> simp_all [embAFun, Xc, Ec, Gc, Yc, jc]

def embA : FetchIndexed.Stack ↪ Stack := ⟨embAFun, embAFun_injective⟩

def embBFun : FetchIndexed.Stack → Stack
  | .inl j => .inr (.inl j)
  | .inr j => (![remc, Gc, Xc, Yc, ic] : Fin 5 → Stack) j

theorem embBFun_injective : Function.Injective embBFun := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [embBFun] using h
  · fin_cases b <;> simp [embBFun, remc, Gc, Xc, Yc, ic] at h
  · fin_cases a <;> simp [embBFun, remc, Gc, Xc, Yc, ic] at h
  · fin_cases a <;> fin_cases b <;> simp_all [embBFun, remc, Gc, Xc, Yc, ic]

def embB : FetchIndexed.Stack ↪ Stack := ⟨embBFun, embBFun_injective⟩

/-! ### The fixed program -/

def ySlots : Fin 3 ↪ Stack := ⟨![Yc, remc, sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Yc, remc, sc]⟩

def copyY := MatrixStage4ScalarPreparationOps.copyProgram ySlots
def readJ := readProg remc jc
def fetchA := fun l => stackStmt embA (FetchIndexed.colProgram l)
def readI := readProg tagC ic
def fetchB := fun l => stackStmt embB (FetchIndexed.colProgram l)

abbrev oc := (none : Option Bool)

def s1 := BitMachineRawSequence.program copyY readJ () oc oc
def s2 := BitMachineRawSequence.program s1 fetchA FetchIndexed.colStart (oc, oc)
  FetchIndexed.colControl
def s3 := BitMachineRawSequence.program s2 readI () ((oc, oc), FetchIndexed.colControl) oc
def program := BitMachineRawSequence.program s3 fetchB FetchIndexed.colStart
  (((oc, oc), FetchIndexed.colControl), oc) FetchIndexed.colControl

def startLabel := FetchIndexed.labelOf program
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      BitMachineCopy.Label.scan))))
def startControl := ((((oc, oc), FetchIndexed.colControl), oc), FetchIndexed.colControl)

def clock (Y : List Bool) (j i : ℕ) (E G : Code) (cs rs : List (List Bool)) : ℕ :=
  (2 * Y.length + 2) + (j + 1) + FetchIndexed.colBound E cs j [] + (i + 1) +
    FetchIndexed.colBound G rs i [] + 4

/-- Generic run: arbitrary shaped codes and produced label lists. -/
theorem select_generic (E G : Code) (hE : Shape E) (hG : Shape G)
    (cs rs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning E) c) (hrs : ∀ r ∈ rs, Produces (meaning G) r)
    (j i : ℕ) (hj : j < cs.length) (hi : i < rs.length) (T : List Bool)
    (hentry : cs.getD j [] = List.replicate i true ++ false :: T) :
    let X := cs.flatten
    let Y := List.replicate j true ++ false :: rs.flatten
    ∃ t ≤ clock Y j i E G cs rs, ∃ v,
      ((advance program)^[t])
        (⟨some startLabel, startControl,
          mk [] [] (vec X Y (encodeCode E) (encodeCode G) [] [] [])⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v, mk T (rs.getD i [])
          (vec X Y (encodeCode E) (encodeCode G) (List.replicate j true) rs.flatten
            (List.replicate i true))⟩ := by
  intro X Y
  let eE := encodeCode E
  let eG := encodeCode G
  let B0 := mk [] [] (vec X Y eE eG [] [] [])
  let B1 := mk [] [] (vec X Y eE eG [] Y [])
  let B2 := mk [] [] (vec X Y eE eG (List.replicate j true) rs.flatten [])
  let B3 := mk (cs.getD j []) [] (vec X Y eE eG (List.replicate j true) rs.flatten [])
  let B4 := mk T [] (vec X Y eE eG (List.replicate j true) rs.flatten (List.replicate i true))
  let B5 := mk T (rs.getD i [])
    (vec X Y eE eG (List.replicate j true) rs.flatten (List.replicate i true))
  -- phase 1: copy Y to the work cell
  have p1 := MatrixStage4ScalarPreparationOps.copy_run ySlots B0 rfl
  have p1' : ((advance copyY)^[2 * Y.length + 2])
      (⟨some .scan, none, B0⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, B1⟩ := by
    have e0 : B0 (ySlots 0) = Y := rfl
    have e1 : B0 (ySlots 1) = [] := rfl
    rw [e0, e1, List.append_nil] at p1
    refine Eq.trans p1 ?_
    have hb : Function.update B0 (ySlots 1) Y = B1 := by
      change Function.update (mk [] [] _) (.inr (.inr 5)) Y = _
      rw [upd_vec]
      congr 1
      funext q; fin_cases q <;> rfl
    rw [hb]
  -- phase 2: read j
  have p2 := read_run remc jc (by simp [remc, jc]) j rs.flatten [] B1 none rfl rfl
  have p2' : ((advance readJ)^[j + 1])
      (⟨some (), none, B1⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, some false, B2⟩ := by
    refine Eq.trans p2 ?_
    have hb : Function.update (Function.update B1 remc rs.flatten) jc
        (List.replicate j true ++ []) = B2 := by
      change Function.update (Function.update (mk [] [] _) (.inr (.inr 5)) _)
        (.inr (.inr 4)) _ = _
      rw [upd_vec, upd_vec, List.append_nil]
      congr 1
      funext q; fin_cases q <;> rfl
    rw [hb]
  -- phase 3: fetch the j-th row entry
  obtain ⟨t3, ht3, v3, p3⟩ := SuccessFetchJoin.lift_col embA B2 E hE cs hcs [] j hj
    (fun k => inner_nil k) (by change X = cs.flatten ++ []; rw [List.append_nil])
    rfl rfl
  have p3' : ((advance fetchA)^[t3])
      (⟨some FetchIndexed.colStart, FetchIndexed.colControl, B2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, v3, B3⟩ := by
    refine Eq.trans p3 ?_
    have hb : Function.update B2 (embA SuccessFetchJoin.lblF) (cs.getD j []) = B3 := by
      change Function.update (mk [] [] _) (.inl FetchLabel.lblC) _ = _
      rw [upd_A]
    rw [hb]
  -- phase 4: read i off the entry
  have p4 := read_run tagC ic (by simp [tagC, ic]) i T [] B3 none
    (by change cs.getD j [] = _; exact hentry) rfl
  have p4' : ((advance readI)^[i + 1])
      (⟨some (), none, B3⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit (Option Bool)) =
      ⟨none, some false, B4⟩ := by
    refine Eq.trans p4 ?_
    have hb : Function.update (Function.update B3 tagC T) ic
        (List.replicate i true ++ []) = B4 := by
      change Function.update (Function.update (mk _ [] _) (.inl FetchLabel.lblC) _)
        (.inr (.inr 6)) _ = _
      rw [upd_A, upd_vec, List.append_nil]
      congr 1
      funext q; fin_cases q <;> rfl
    rw [hb]
  -- phase 5: fetch the i-th raw row
  obtain ⟨t5, ht5, v5, p5⟩ := SuccessFetchJoin.lift_col embB B4 G hG rs hrs [] i hi
    (fun k => inner_nil k) (by change rs.flatten = rs.flatten ++ []; rw [List.append_nil])
    rfl rfl
  have p5' : ((advance fetchB)^[t5])
      (⟨some FetchIndexed.colStart, FetchIndexed.colControl, B4⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, v5, B5⟩ := by
    refine Eq.trans p5 ?_
    have hb : Function.update B4 (embB SuccessFetchJoin.lblF) (rs.getD i []) = B5 := by
      change Function.update (mk _ [] _) (.inr (.inl FetchLabel.lblC)) _ = _
      rw [upd_B]
    rw [hb]
  -- sequencing
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs copyY readJ .scan ()
    oc oc oc (some false) _ _ _ _ _ p1' p2'
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs s1 fetchA
    (BitMachineRawSequence.leftLabel .scan) FetchIndexed.colStart
    (oc, oc) (oc, some false) FetchIndexed.colControl v3 _ _ _ _ _ q1 p3'
  obtain ⟨r3, hr3, q3⟩ := BitMachineRawSequence.runs s2 readI
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) ()
    ((oc, oc), FetchIndexed.colControl) ((oc, oc), v3) oc (some false) _ _ _ _ _ q2 p4'
  obtain ⟨r4, hr4, q4⟩ := BitMachineRawSequence.runs s3 fetchB
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))) FetchIndexed.colStart
    (((oc, oc), FetchIndexed.colControl), oc) (((oc, oc), FetchIndexed.colControl), some false)
    FetchIndexed.colControl v5 _ _ _ _ _ q3 p5'
  refine ⟨r4, ?_, _, q4⟩
  simp only [clock]
  omega

end

#print axioms read_run
#print axioms select_generic

end Paper2.RequestSelect
