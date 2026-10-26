import EthInapproximability.CurrentPaper.U4PostExponent
import EthInapproximability.CurrentPaper.U4PostPadWriter

/-!
# Unit 4 (Paper B), segment B4-S4 (join): ONE local post program on the six H-B2 fields

Lane owner:b-unit4-shell-3 (private, 26 September 2026).

One fixed Boolean-stack program on 25 stacks, sequenced by the admitted
`BitMachineRawSequence.runs`, each stage inlined by the admitted stack embedding
(`embed_run` of `U4PostExponent`):

1. the exponent program (`U4PostExponent`): unary `2^p` into the writer's row and column
   counters, `p = n / (2 max 1 k)`, `n` consumed, `k` restored;
2. the padded-table writer (`U4PostPadWriter.padded_table`) with persistent bank
   `(m, r, rowMajor R)` = H-B2 fields 2, 3, 4 and its output stack = the table output stack;
3. five charged clears (`m`, `r`, `rowMajor R`, both counters);
4. two charged unary moves (`k` and `y` to their output stacks).

Layout: `0 n, 1 k, 2 m, 3 r, 4 R, 5 y` (H-B2 fields 0-5 in order), `6 table, 7 y-out,
8 k-out` (outputs), `9 rows, 10 cols`, `11-24 scratch`. At halt only the three outputs are
nonempty.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post

open Turing Turing.TM2.Stmt BitMachineEncoding

namespace Move

/-- Unary move: pop stack 0, push `true` on stack 1. -/
def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Bool
  | () => pop 0 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => ()))) halt)

theorem move_run (a b : ℕ) (s : Bool) :
    ((advance program)^[a + 1])
      (⟨some (), s, ![List.replicate a true, List.replicate b true]⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) Unit Bool) =
      ⟨none, false, ![[], List.replicate (a + b) true]⟩ := by
  induction a generalizing b s with
  | zero =>
      simp only [Nat.zero_add, Function.iterate_one, List.replicate_zero]
      apply congrArg (fun S => (⟨none, false, S⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Bool))
      funext k
      fin_cases k <;> rfl
  | succ a ih =>
      have hs : advance program
          (⟨some (), s, ![List.replicate (a + 1) true, List.replicate b true]⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) Unit Bool) =
          ⟨some (), true, ![List.replicate a true, List.replicate (b + 1) true]⟩ := by
        apply congrArg
          (fun S => (⟨some (), true, S⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Bool))
        funext k
        fin_cases k <;> rfl
      rw [Function.iterate_succ_apply, hs, ih (b + 1) true]
      rw [show a + (b + 1) = a + 1 + b by ring]

theorem move_run0 (a : ℕ) (s : Bool) :
    ((advance program)^[a + 1])
      (⟨some (), s, ![List.replicate a true, []]⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) Unit Bool) =
      ⟨none, false, ![[], List.replicate a true]⟩ := by
  simpa using move_run a 0 s

end Move

namespace Local

abbrev Stack := Fin 25

/-- Structural list lookup (linear definitional unfolding at a literal index). -/
def nth : List (List Bool) → ℕ → List Bool
  | [], _ => []
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n

def amb (L : List (List Bool)) (j : Stack) : List Bool := nth L j.val

def E14 : List (List Bool) := [[], [], [], [], [], [], [], [], [], [], [], [], [], []]

def ιExp : Fin 13 ↪ Stack := ⟨![0, 1, 11, 12, 13, 14, 15, 16, 9, 17, 18, 10, 19], by decide⟩

def extraSlot : MatrixTableWriter.Extra → Stack
  | .rows => 9 | .cols => 10 | .rowsLeft => 21 | .colsLeft => 22 | .temp => 23
  | .buffer => 24 | .output => 6

def ιW : MatrixTableWriter.Stack 10 ↪ Stack :=
  ⟨Sum.elim (Sum.elim ![2, 3, 4, 11, 12, 13, 14, 15, 16, 17] ![18, 19, 20]) extraSlot,
    by decide⟩

def ι1 (i : Stack) : Fin 1 ↪ Stack := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
def ι2 (i j : Stack) (h : i ≠ j) : Fin 2 ↪ Stack :=
  ⟨![i, j], by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab h
    · exact absurd hab.symm h
    · rfl⟩

def sExp := fun l => BitMachineStackEmbedding.stackStmt ιExp (Exponent.program l)
def sW := fun l => BitMachineStackEmbedding.stackStmt ιW
  (MatrixTableWriter.program PadWriter.entryProgram PadWriter.start PadWriter.initial l)
def sClr (i : Stack) := fun l => BitMachineStackEmbedding.stackStmt (ι1 i) (ClearOne.program l)
def sMk := fun l => BitMachineStackEmbedding.stackStmt (ι2 1 8 (by decide)) (Move.program l)
def sMy := fun l => BitMachineStackEmbedding.stackStmt (ι2 5 7 (by decide)) (Move.program l)

def i8 : Bool × Bool := (false, false)
def i7 : Bool × (Bool × Bool) := (false, i8)
def i6 : Bool × (Bool × (Bool × Bool)) := (false, i7)
def i5 : Bool × (Bool × (Bool × (Bool × Bool))) := (false, i6)
def i4 : Bool × (Bool × (Bool × (Bool × (Bool × Bool)))) := (false, i5)
def i3 : Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))) := (false, i4)
def i2 : (PadWriter.Control × Option Bool) ×
    (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool)))))) := ((PadWriter.initial, none), i3)

def t8 := BitMachineRawSequence.program sMk sMy () false false
def t7 := BitMachineRawSequence.program (sClr 10) t8 (BitMachineRawSequence.leftLabel ()) false i8
def t6 := BitMachineRawSequence.program (sClr 9) t7 (BitMachineRawSequence.leftLabel ()) false i7
def t5 := BitMachineRawSequence.program (sClr 4) t6 (BitMachineRawSequence.leftLabel ()) false i6
def t4 := BitMachineRawSequence.program (sClr 3) t5 (BitMachineRawSequence.leftLabel ()) false i5
def t3 := BitMachineRawSequence.program (sClr 2) t4 (BitMachineRawSequence.leftLabel ()) false i4
def t2 := BitMachineRawSequence.program sW t3 (BitMachineRawSequence.leftLabel ())
  (PadWriter.initial, none) i3
def program := BitMachineRawSequence.program sExp t2
  (BitMachineRawSequence.leftLabel (.inr (.copy .rows))) Exponent.initial i2
def initial := (Exponent.initial, i2)

abbrev rp (n : ℕ) : List Bool := List.replicate n true

/-- Ambient banks between the stages. -/
def B0 (n k m r y : ℕ) (R : List Bool) : Stack → List Bool :=
  amb ([rp n, rp k, rp m, rp r, R, rp y, [], [], [], [], []] ++ E14)
def B1 (k m r y P : ℕ) (R : List Bool) : Stack → List Bool :=
  amb ([[], rp k, rp m, rp r, R, rp y, [], [], [], rp P, rp P] ++ E14)
def B2 (k m r y P : ℕ) (R T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, rp m, rp r, R, rp y, T, [], [], rp P, rp P] ++ E14)
def B3 (k r y P : ℕ) (R T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, [], rp r, R, rp y, T, [], [], rp P, rp P] ++ E14)
def B4 (k y P : ℕ) (R T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, [], [], R, rp y, T, [], [], rp P, rp P] ++ E14)
def B5 (k y P : ℕ) (T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, [], [], [], rp y, T, [], [], rp P, rp P] ++ E14)
def B6 (k y P : ℕ) (T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, [], [], [], rp y, T, [], [], [], rp P] ++ E14)
def B7 (k y : ℕ) (T : List Bool) : Stack → List Bool :=
  amb ([[], rp k, [], [], [], rp y, T, [], [], [], []] ++ E14)
def B8 (k y : ℕ) (T : List Bool) : Stack → List Bool :=
  amb ([[], [], [], [], [], rp y, T, [], rp k, [], []] ++ E14)
def B9 (k y : ℕ) (T : List Bool) : Stack → List Bool :=
  amb ([[], [], [], [], [], [], T, rp y, rp k, [], []] ++ E14)

macro "out13" : tactic => `(tactic| (
  intro j hj
  fin_cases j <;> first
    | rfl
    | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
    | exact absurd rfl (hj 3) | exact absurd rfl (hj 4) | exact absurd rfl (hj 5)
    | exact absurd rfl (hj 6) | exact absurd rfl (hj 7) | exact absurd rfl (hj 8)
    | exact absurd rfl (hj 9) | exact absurd rfl (hj 10) | exact absurd rfl (hj 11)
    | exact absurd rfl (hj 12)))

theorem stageExp (n k m r y : ℕ) (R : List Bool) :
    ∃ t ≤ Exponent.bound n k, ∃ v,
      ((advance sExp)^[t]) ⟨some Exponent.start, Exponent.initial, B0 n k m r y R⟩ =
        ⟨none, v, B1 k m r y (2 ^ Exponent.pexp n k) R⟩ := by
  obtain ⟨t, ht, v, h⟩ := Exponent.exponent_run n k
  exact ⟨t, ht, v, embed_run ιExp Exponent.program Exponent.start Exponent.initial v _ _ _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) (by out13)⟩

theorem stageW {m r : ℕ} (k y : ℕ) (Rf : Fin m → Fin r → Bool) (p : ℕ) (hm : 0 < m)
    (hr : 0 < r) :
    ∃ t ≤ MatrixTableWriter.writerBound (2 ^ p) (2 ^ p)
        (PadWriter.callbackBound (2 ^ p) (2 ^ p) m r (m * r)), ∃ v,
      ((advance sW)^[t]) ⟨some (.inr (.copy .rows)), (PadWriter.initial, none),
          B1 k m r y (2 ^ p) (MatrixMaterialization.rowMajor Rf)⟩ =
        ⟨none, v, B2 k m r y (2 ^ p) (MatrixMaterialization.rowMajor Rf)
          (FinalPadding.table Rf p hm hr)⟩ := by
  obtain ⟨t, ht, v, h⟩ := PadWriter.padded_table Rf p hm hr []
  simp only [List.append_nil] at h
  refine ⟨t, ht, v, embed_run ιW _ _ _ v _ _ _ _ t h ?_ ?_ ?_⟩
  · intro i
    rcases i with (i | i) | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · cases i <;> rfl
  · intro i
    rcases i with (i | i) | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · cases i <;> rfl
  · intro j hj
    fin_cases j <;> first
      | rfl
      | exact absurd rfl (hj (.inr .output))

theorem stageClr (i : Stack) (w : List Bool) (T₀ T₁ : Stack → List Bool)
    (h₀ : T₀ i = w) (h₁ : T₁ i = [])
    (hout : ∀ j, j ≠ i → T₀ j = T₁ j) :
    ((advance (sClr i))^[w.length + 1]) ⟨some (), false, T₀⟩ = ⟨none, false, T₁⟩ := by
  refine embed_run (ι1 i) ClearOne.program () false false _ _ T₀ T₁ (w.length + 1)
    (ClearOne.clear_run w false) ?_ ?_ ?_
  · intro a; fin_cases a; exact h₀.symm
  · intro a; fin_cases a; exact h₁.symm
  · intro j hj
    exact hout j (fun he => hj 0 he.symm)

theorem stageMove (i j : Stack) (hij : i ≠ j) (a : ℕ) (T₀ T₁ : Stack → List Bool)
    (hi₀ : T₀ i = List.replicate a true) (hj₀ : T₀ j = [])
    (hi₁ : T₁ i = []) (hj₁ : T₁ j = List.replicate a true)
    (hout : ∀ l, l ≠ i → l ≠ j → T₀ l = T₁ l) :
    ((advance (fun l => BitMachineStackEmbedding.stackStmt (ι2 i j hij) (Move.program l)))^[a + 1])
      ⟨some (), false, T₀⟩ = ⟨none, false, T₁⟩ := by
  refine embed_run (ι2 i j hij) Move.program () false false _ _ T₀ T₁ (a + 1)
    (Move.move_run0 a false) ?_ ?_ ?_
  · intro b; fin_cases b
    · exact hi₀.symm
    · exact hj₀.symm
  · intro b; fin_cases b
    · exact hi₁.symm
    · exact hj₁.symm
  · intro l hl
    exact hout l (fun he => hl 0 he.symm) (fun he => hl 1 he.symm)

/-- The local clock. -/
def localBound (n k m r y : ℕ) : ℕ :=
  Exponent.bound n k +
    MatrixTableWriter.writerBound (2 ^ Exponent.pexp n k) (2 ^ Exponent.pexp n k)
      (PadWriter.callbackBound (2 ^ Exponent.pexp n k) (2 ^ Exponent.pexp n k) m r (m * r)) +
    (m + r + m * r + 2 * 2 ^ Exponent.pexp n k + k + y + 20)

/-- **B4-S4 join.** The ONE fixed local post program, from the six H-B2 fields
(`n, k, m, r, rowMajor R, y`) on stacks 0-5, halts with exactly
`FinalPadding.table R (n / (2 max 1 k)) hm hr` on stack 6, unary `y` on stack 7, unary `k` on
stack 8 and every other stack empty, within `localBound n k m r y`. -/
theorem local_run {m r : ℕ} (n k y : ℕ) (Rf : Fin m → Fin r → Bool) (hm : 0 < m) (hr : 0 < r) :
    ∃ t ≤ localBound n k m r y, ∃ v,
      ((advance program)^[t])
        ⟨some (BitMachineRawSequence.leftLabel Exponent.start), initial,
          B0 n k m r y (MatrixMaterialization.rowMajor Rf)⟩ =
        ⟨none, v, B9 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr)⟩ := by
  have hRlen : (MatrixMaterialization.rowMajor Rf).length = m * r :=
    MatrixMaterialization.rowMajor_length Rf
  obtain ⟨u1, hu1, v1, h1⟩ := stageExp n k m r y (MatrixMaterialization.rowMajor Rf)
  obtain ⟨u2, hu2, v2, h2⟩ := stageW k y Rf (Exponent.pexp n k) hm hr
  have h3 := stageClr 2 (rp m)
    (B2 k m r y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B3 k r y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd rfl hj)
  have h4 := stageClr 3 (rp r)
    (B3 k r y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B4 k y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd rfl hj)
  have h5 := stageClr 4 (MatrixMaterialization.rowMajor Rf)
    (B4 k y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)
      (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B5 k y (2 ^ Exponent.pexp n k) (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd rfl hj)
  have h6 := stageClr 9 (rp (2 ^ Exponent.pexp n k))
    (B5 k y (2 ^ Exponent.pexp n k) (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B6 k y (2 ^ Exponent.pexp n k) (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd rfl hj)
  have h7 := stageClr 10 (rp (2 ^ Exponent.pexp n k))
    (B6 k y (2 ^ Exponent.pexp n k) (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B7 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd rfl hj)
  have h8 := stageMove 1 8 (by decide) k
    (B7 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B8 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl rfl rfl
    (by intro l h1 h2; fin_cases l <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
  have h9 := stageMove 5 7 (by decide) y
    (B8 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr))
    (B9 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr)) rfl rfl rfl rfl
    (by intro l h1 h2; fin_cases l <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
  obtain ⟨a8, ha8, e8⟩ := BitMachineRawSequence.runs sMk sMy () () false false false false
    _ _ _ _ _ h8 h9
  obtain ⟨a7, ha7, e7⟩ := BitMachineRawSequence.runs (sClr 10) t8 () (BitMachineRawSequence.leftLabel ())
    false false i8 _ _ _ _ _ _ h7 e8
  obtain ⟨a6, ha6, e6⟩ := BitMachineRawSequence.runs (sClr 9) t7 () (BitMachineRawSequence.leftLabel ())
    false false i7 _ _ _ _ _ _ h6 e7
  obtain ⟨a5, ha5, e5⟩ := BitMachineRawSequence.runs (sClr 4) t6 () (BitMachineRawSequence.leftLabel ())
    false false i6 _ _ _ _ _ _ h5 e6
  obtain ⟨a4, ha4, e4⟩ := BitMachineRawSequence.runs (sClr 3) t5 () (BitMachineRawSequence.leftLabel ())
    false false i5 _ _ _ _ _ _ h4 e5
  obtain ⟨a3, ha3, e3⟩ := BitMachineRawSequence.runs (sClr 2) t4 () (BitMachineRawSequence.leftLabel ())
    false false i4 _ _ _ _ _ _ h3 e4
  obtain ⟨a2, ha2, e2⟩ := BitMachineRawSequence.runs sW t3
    (Sum.inr (MatrixTableWriter.Admin.copy .rows) : MatrixTableWriter.Label PadWriter.Label)
    (BitMachineRawSequence.leftLabel ()) (PadWriter.initial, none) v2 i3 _ _ _ _ _ _ h2 e3
  have e2' : ((advance t2)^[a2])
      ⟨some (BitMachineRawSequence.leftLabel
        (Sum.inr (MatrixTableWriter.Admin.copy .rows) : MatrixTableWriter.Label PadWriter.Label)),
        i2, B1 k m r y (2 ^ Exponent.pexp n k) (MatrixMaterialization.rowMajor Rf)⟩ =
      ⟨none, ((PadWriter.initial, none), (false, (false, (false, (false, (false,
        (false, false))))))), B9 k y (FinalPadding.table Rf (Exponent.pexp n k) hm hr)⟩ := e2
  obtain ⟨a1, ha1, e1⟩ := BitMachineRawSequence.runs sExp t2 Exponent.start
    (BitMachineRawSequence.leftLabel
      (Sum.inr (MatrixTableWriter.Admin.copy .rows) : MatrixTableWriter.Label PadWriter.Label))
    Exponent.initial v1 i2 _ _ _ _ _ _
    h1 e2'
  refine ⟨a1, ?_, _, e1⟩
  have hl1 : (rp m).length = m := List.length_replicate
  have hl2 : (rp r).length = r := List.length_replicate
  have hl3 : (rp (2 ^ Exponent.pexp n k)).length = 2 ^ Exponent.pexp n k := List.length_replicate
  unfold localBound
  omega

end Local

end EthInapproximability.CurrentPaper.Unit4Post
