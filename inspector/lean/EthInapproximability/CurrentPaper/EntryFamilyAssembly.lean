import EthInapproximability.CurrentPaper.FamilyTableLoop
import EthInapproximability.CurrentPaper.PrimeFromWords
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.Iteration

/-!
# Segment-1 assembly: both one-hot family tables from unary `a, q, t, rx, L`

Lane owner:b-stage4-entry-program-2, segment 1.

ONE fixed controller `program` (a right-nested `BitMachineRawSequence` of six
literal phases, every handoff charged) on the bank
`ACell = FamilyRowBody.Cell ⊕ (PrimeFromWords.Stack ⊕ X)`:

1. the admitted `MatrixStage4ScalarPreparationOps.unary_power_run`:
   `2^a` into the width cell `w` (input `a` at `X.a`, scratch `X.s0/s1`);
2. two literal pops on `w`: `qOne a = 2^a - 2`;
3. the admitted `multiply_run`: `m = qOne a * rx` into `m`;
4. the checked `PrimeFromWords.program` embedded with its `q, t, m` cells ON
   the family cells `q, order, m` and its prime target ON the `prime` cell
   (every other cell in the fresh region `PrimeFromWords.Stack`);
5. the admitted `multiply_run`: `L * q` into the row counter `cnt`
   (input `L` at `X.L`, the level's chosen-size word);
6. the checked `FamilyTableLoop.program` (both one-hot tables).

Inputs: unary `a, q, t, rx, L` only (every other cell blank). Exit: the
family bank `rowBank 0 p t q rx (qOne a) m T₁ T₂` with the two literal tables,
`a` and `L` retained, every scratch cell and the whole prime region blank.
No table word, entry value, prime or product is supplied.
-/

namespace EthInapproximability.CurrentPaper.EntryFamilyAssembly

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open Construction MatrixStage4FamilyData

noncomputable section

inductive X where
  | a | L | s0 | s1 | s2
  deriving DecidableEq

abbrev Cell := FamilyRowBody.Cell
abbrev ACell := Cell ⊕ (PrimeFromWords.Stack ⊕ X)

def cell (c : Cell) : ACell := .inl c
def pf (k : PrimeFromWords.Stack) : ACell := .inr (.inl k)
def xc (x : X) : ACell := .inr (.inr x)

def xBank (a L : ℕ) : X → List Bool
  | .a => List.replicate a true
  | .L => List.replicate L true
  | _ => []

/-- The whole bank: family cells `C`, blank prime region, `a` and `L`. -/
def full (C : Cell → List Bool) (a L : ℕ) : ACell → List Bool :=
  Sum.elim C (Sum.elim (fun _ => []) (xBank a L))

theorem full_update (C : Cell → List Bool) (c : Cell) (v : List Bool) (a L : ℕ) :
    Function.update (full C a L) (cell c) v = full (Function.update C c v) a L := by
  funext j
  rcases j with j | j
  · by_cases h : j = c
    · subst h; simp [full, cell]
    · have h' : (Sum.inl j : ACell) ≠ cell c := fun e => h (Sum.inl_injective e)
      rw [Function.update_of_ne h']
      simp [full, Function.update_of_ne h]
  · have h' : (Sum.inr j : ACell) ≠ cell c := fun e => by cases e
    rw [Function.update_of_ne h']
    rfl

theorem bank_exact {K J : Type*} [DecidableEq K] [DecidableEq J] (ι : K ↪ J)
    (S S' : J → List Bool) (T : K → List Bool)
    (hT : ∀ k, T k = S' (ι k)) (hout : ∀ j, (¬ ∃ k, ι k = j) → S j = S' j) :
    bank ι S T = S' := by
  funext j
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h
    rw [bank_at, hT]
  · rw [bank_outside _ _ _ _ h, hout j h]

/-! ## Phase 1: `2^a` -/

def powerSlots : MatrixUnaryPower.Stack ↪ ACell where
  toFun
    | .inl 0 => cell .w
    | .inl 1 => xc .s0
    | .inl _ => xc .s1
    | .inr () => xc .a
  inj' := by
    intro u v h
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;> simp [cell, xc] at h ⊢
    · cases v; fin_cases u <;> simp [cell, xc] at h
    · cases u; fin_cases v <;> simp [cell, xc] at h
    · cases u; cases v; rfl

def P1 := unaryPowerProgram powerSlots

theorem phase1 (C : Cell → List Bool) (a L : ℕ) (hw : C .w = []) :
    ∃ n ≤ 4 * 2 ^ a + 5 * a + 7,
      ((advance P1)^[n])
        (⟨some (.inr false), ((false, false), none), full C a L⟩ :
          TM2.Cfg (fun _ : ACell => Bool) MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, ((false, false), none),
          full (Function.update C .w (List.replicate (2 ^ a) true)) a L⟩ := by
  obtain ⟨n, hn, h⟩ := unary_power_run powerSlots (full C a L) a rfl hw rfl rfl
  refine ⟨n, hn, h.trans ?_⟩
  rw [show powerSlots (.inl 0) = cell .w from rfl, full_update]

/-! ## Phase 2: two pops, `qOne a = 2^a - 2` -/

def P2 : Unit → TM2.Stmt (fun _ : ACell => Bool) Unit Unit :=
  fun _ => .pop (cell .w) (fun _ _ => ()) (.pop (cell .w) (fun _ _ => ()) .halt)

theorem phase2 (C : Cell → List Bool) (a L : ℕ)
    (hw : C .w = List.replicate (2 ^ a) true) :
    ((advance P2)^[1])
      (⟨some (), (), full C a L⟩ : TM2.Cfg (fun _ : ACell => Bool) Unit Unit) =
      ⟨none, (), full (Function.update C .w (List.replicate (qOne a) true)) a L⟩ := by
  rw [← full_update]
  have hw' : full C a L (cell .w) = List.replicate (2 ^ a) true := hw
  simp [P2, advance, TM2.step, TM2.stepAux, hw', Construction.qOne, Nat.sub_sub]

/-! ## Phases 3 and 5: the admitted multiplier -/

def mulM : Fin 6 ↪ ACell :=
  ⟨![cell .w, cell .rx, xc .s0, xc .s1, xc .s2, cell .m], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [cell, xc]⟩

def mulN : Fin 6 ↪ ACell :=
  ⟨![xc .L, cell .q, xc .s0, xc .s1, xc .s2, cell .cnt], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [cell, xc]⟩

def P3 := multiplyProgram mulM
def P5 := multiplyProgram mulN

theorem phase3 (C : Cell → List Bool) (a L W R : ℕ)
    (hw : C .w = List.replicate W true) (hr : C .rx = List.replicate R true)
    (hm : C .m = []) :
    ((advance P3)^[MatrixAddressMachine.exactTime W R 0])
      (⟨some .outer, false, full C a L⟩ :
        TM2.Cfg (fun _ : ACell => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, full (Function.update C .m (List.replicate (W * R) true)) a L⟩ := by
  have h := multiply_run mulM (full C a L) W R hw hr rfl rfl rfl
  unfold P3
  rw [h]
  have e5 : mulM 5 = cell .m := rfl
  have hm' : full C a L (cell .m) = [] := hm
  rw [e5, hm', List.append_nil, full_update]

theorem phase5 (C : Cell → List Bool) (a L Q : ℕ)
    (hq : C .q = List.replicate Q true) (hc : C .cnt = []) :
    ((advance P5)^[MatrixAddressMachine.exactTime L Q 0])
      (⟨some .outer, false, full C a L⟩ :
        TM2.Cfg (fun _ : ACell => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, full (Function.update C .cnt (List.replicate (L * Q) true)) a L⟩ := by
  have h := multiply_run mulN (full C a L) L Q rfl hq rfl rfl rfl
  unfold P5
  rw [h]
  have e5 : mulN 5 = cell .cnt := rfl
  have hc' : full C a L (cell .cnt) = [] := hc
  rw [e5, hc', List.append_nil, full_update]

/-! ## Phase 4: the prime word, embedded on the family cells -/

def pfMap (k : PrimeFromWords.Stack) : ACell :=
  if k = .inr 0 then cell .q else
  if k = .inr 1 then cell .order else
  if k = .inr 2 then cell .m else
  if k = .inl (.inr 0) then cell .prime else pf k

def pfSlots : PrimeFromWords.Stack ↪ ACell :=
  ⟨pfMap, by
    intro u v h
    unfold pfMap at h
    split_ifs at h <;> simp_all [cell, pf]⟩

def P4 (l : _) := stackStmt pfSlots (PrimeFromWords.program l)

theorem phase4 (C : Cell → List Bool) (a L q t m : ℕ)
    (hq : C .q = List.replicate q true) (ht : C .order = List.replicate t true)
    (hm : C .m = List.replicate m true) (hp : C .prime = []) :
    ∃ u ≤ PrimeFromWords.fromBound q t m,
      ((advance P4)^[u])
        (⟨some PrimeFromWords.start, (Paper2.WeightedThresholdArithmetic.controlFinal,
            PrimeWordExact.initControl), full C a L⟩ :
          TM2.Cfg (fun _ : ACell => Bool) _ _) =
        ⟨none, (Paper2.WeightedThresholdArithmetic.controlFinal,
            PrimeWordExact.initControl),
          full (Function.update C .prime
            (List.replicate (PrimeSampler.prime q t m) true)) a L⟩ := by
  obtain ⟨u, hu, h⟩ := PrimeFromWords.prime_from_words q t m
  refine ⟨u, hu, ?_⟩
  have hrun := BitMachineStackRun.run pfSlots (full C a L) PrimeFromWords.program
    ⟨some PrimeFromWords.start, (Paper2.WeightedThresholdArithmetic.controlFinal,
      PrimeWordExact.initControl), PrimeFromWords.startBank q t m⟩ u
  rw [h] at hrun
  have hs : bank pfSlots (full C a L) (PrimeFromWords.startBank q t m) = full C a L := by
    apply bank_exact
    · intro k
      rcases k with k | j
      · show ([] : List Bool) = _
        simp only [pfSlots, Function.Embedding.coeFn_mk, pfMap]
        split_ifs <;> simp_all [full, cell, pf]
      · simp only [PrimeFromWords.startBank, Sum.elim_inr,
          Paper2.WeightedThresholdArithmetic.initial, Paper2.WeightedThresholdArithmetic.unary,
          pfSlots, Function.Embedding.coeFn_mk, pfMap]
        split_ifs <;> simp_all [full, cell, pf]
    · intro j _; rfl
  have hf : bank pfSlots (full C a L) (PrimeFromWords.exitBank q t m) =
      full (Function.update C .prime
        (List.replicate (PrimeSampler.prime q t m) true)) a L := by
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := PrimeFromWords.exit_slots q t m
    apply bank_exact
    · intro k
      rcases k with (k | k) | j
      · rw [e4 k]
        simp [pfSlots, pfMap, full, pf]
      · fin_cases k
        · change PrimeFromWords.exitBank q t m (.inl (.inr 0)) = _
          rw [e0]
          simp [pfSlots, pfMap, full, cell]
        · change PrimeFromWords.exitBank q t m (.inl (.inr 1)) = _
          rw [e5]
          simp [pfSlots, pfMap, full, pf]
      · by_cases j0 : j = 0
        · subst j0
          rw [e1]
          simp [pfSlots, pfMap, full, cell, hq]
        · by_cases j1 : j = 1
          · subst j1
            rw [e2]
            simp [pfSlots, pfMap, full, cell, ht]
          · by_cases j2 : j = 2
            · subst j2
              rw [e3]
              simp [pfSlots, pfMap, full, cell, hm]
            · rw [e6 j j0 j1 j2]
              simp [pfSlots, pfMap, full, pf, j0, j1, j2]
    · intro j hj
      have hne : j ≠ cell .prime := by
        intro e
        apply hj
        refine ⟨.inl (.inr 0), ?_⟩
        rw [e]
        simp [pfSlots, pfMap]
      rw [← full_update, Function.update_of_ne hne]
  simp only [stackCfg, hs, hf] at hrun
  exact hrun

/-! ## Phase 6: the family-table loop -/

def famSlots : Cell ↪ ACell := ⟨Sum.inl, Sum.inl_injective⟩

def P6 (l : FamilyTableLoop.Label) := stackStmt famSlots (FamilyTableLoop.program l)

theorem phase6 (a q t rx : ℕ) (hm : 0 < qOne a * rx) (hrx : 0 < rx) :
    let m := qOne a * rx
    let p := PrimeSampler.prime q t m
    let N := PrimeSampler.size q t m * q
    let family := PrimeSamplerFamilyTableCoordinate.actualFamily a q t rx hm
    ∃ n ≤ N * (FamilyTableLoop.bodyBound N p t q rx (qOne a) m + 1) + 1,
      ((advance P6)^[n])
        (⟨some FamilyTableLoop.top, (FamilyRowBody.i1, none),
          full (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) a
            (PrimeSampler.size q t m)⟩ :
          TM2.Cfg (fun _ : ACell => Bool) FamilyTableLoop.Label FamilyTableLoop.Control) =
        ⟨none, (FamilyRowBody.i1, none),
          full (FamilyRowBody.rowBank 0 p t q rx (qOne a) m
            (fieldTable (familyFirst family)) (fieldTable (familyRow family))) a
            (PrimeSampler.size q t m)⟩ := by
  intro m p N family
  obtain ⟨n, hn, h⟩ := FamilyTableLoop.family_tables a q t rx hm hrx
  refine ⟨n, hn, ?_⟩
  have hrun := BitMachineStackRun.run famSlots
    (full (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) a (PrimeSampler.size q t m))
    FamilyTableLoop.program
    ⟨some FamilyTableLoop.top, (FamilyRowBody.i1, none),
      FamilyRowBody.rowBank N p t q rx (qOne a) m [] []⟩ n
  rw [h] at hrun
  have hs : bank famSlots
      (full (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) a (PrimeSampler.size q t m))
      (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) =
      full (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) a (PrimeSampler.size q t m) :=
    bank_exact _ _ _ _ (fun _ => rfl) (fun _ _ => rfl)
  have hf : bank famSlots
      (full (FamilyRowBody.rowBank N p t q rx (qOne a) m [] []) a (PrimeSampler.size q t m))
      (FamilyRowBody.rowBank 0 p t q rx (qOne a) m
        (fieldTable (familyFirst family)) (fieldTable (familyRow family))) =
      full (FamilyRowBody.rowBank 0 p t q rx (qOne a) m
        (fieldTable (familyFirst family)) (fieldTable (familyRow family))) a
        (PrimeSampler.size q t m) := by
    apply bank_exact
    · intro k; rfl
    · intro j hj
      rcases j with j | j
      · exact absurd ⟨j, rfl⟩ hj
      · rfl
  simp only [stackCfg, hs] at hrun
  refine hrun.trans ?_
  congr 1

/-! ## The fixed six-phase controller -/

def v4 := ((Paper2.WeightedThresholdArithmetic.controlFinal,
  PrimeWordExact.initControl))

def seq5 := BitMachineRawSequence.program P5 P6 FamilyTableLoop.top false
  (FamilyRowBody.i1, (none : Option Bool))
def seq4 := BitMachineRawSequence.program P4 seq5
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) v4
  (false, (FamilyRowBody.i1, (none : Option Bool)))
def seq3 := BitMachineRawSequence.program P3 seq4
  (BitMachineRawSequence.leftLabel PrimeFromWords.start) false
  (v4, (false, (FamilyRowBody.i1, (none : Option Bool))))
def seq2 := BitMachineRawSequence.program P2 seq3
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) ()
  (false, (v4, (false, (FamilyRowBody.i1, (none : Option Bool)))))

/-- The single fixed segment-1 controller. -/
def program := BitMachineRawSequence.program P1 seq2
  (BitMachineRawSequence.leftLabel ()) (((false, false), none) : MatrixUnaryPower.Control)
  ((), (false, (v4, (false, (FamilyRowBody.i1, (none : Option Bool))))))

def initialControl :=
  ((((false, false), none) : MatrixUnaryPower.Control),
    ((), (false, (v4, (false, (FamilyRowBody.i1, (none : Option Bool)))))))

/-- Start bank: unary `a, q, t, rx, L`, every other cell blank. -/
def startBank (a q t rx L : ℕ) : ACell → List Bool :=
  full (FamilyRowBody.rowBank 0 0 t q rx 0 0 [] []) a L

/-- Exit bank: the family operand words, the two tables, `a` and `L`. -/
def exitBank (a q t rx : ℕ) (hm : 0 < qOne a * rx) : ACell → List Bool :=
  let m := qOne a * rx
  let family := PrimeSamplerFamilyTableCoordinate.actualFamily a q t rx hm
  full (FamilyRowBody.rowBank 0 (PrimeSampler.prime q t m) t q rx (qOne a) m
    (fieldTable (familyFirst family)) (fieldTable (familyRow family))) a
    (PrimeSampler.size q t m)

def assemblyBound (a q t rx : ℕ) : ℕ :=
  let m := qOne a * rx
  let p := PrimeSampler.prime q t m
  let L := PrimeSampler.size q t m
  let N := L * q
  (4 * 2 ^ a + 5 * a + 7) + 1 + MatrixAddressMachine.exactTime (qOne a) rx 0 +
    PrimeFromWords.fromBound q t m + MatrixAddressMachine.exactTime L q 0 +
    (N * (FamilyTableLoop.bodyBound N p t q rx (qOne a) m + 1) + 1) + 5

/-- Segment 1 main theorem: from unary `a, q, t, rx` and the chosen-size word
`L = size q t (qOne a * rx)`, the fixed controller writes both literal one-hot
family tables of the actual prime family, within `assemblyBound`. -/
theorem family_assembly (a q t rx : ℕ) (hm : 0 < qOne a * rx) (hrx : 0 < rx) :
    ∃ n ≤ assemblyBound a q t rx,
      ((advance program)^[n])
        (⟨some (BitMachineRawSequence.leftLabel (Sum.inr false)), initialControl,
          startBank a q t rx (PrimeSampler.size q t (qOne a * rx))⟩ :
          TM2.Cfg (fun _ : ACell => Bool) _ _) =
        ⟨none, initialControl, exitBank a q t rx hm⟩ := by
  let m := qOne a * rx
  let p := PrimeSampler.prime q t m
  let L := PrimeSampler.size q t m
  let R := FamilyRowBody.rowBank
  -- phase 1
  obtain ⟨n1, hn1, h1⟩ := phase1 (R 0 0 t q rx 0 0 [] []) a L rfl
  have e1 : Function.update (R 0 0 t q rx 0 0 [] []) .w (List.replicate (2 ^ a) true) =
      R 0 0 t q rx (2 ^ a) 0 [] [] := by funext c; cases c <;> rfl
  rw [e1] at h1
  -- phase 2
  have h2 := phase2 (R 0 0 t q rx (2 ^ a) 0 [] []) a L rfl
  have e2 : Function.update (R 0 0 t q rx (2 ^ a) 0 [] []) .w
      (List.replicate (qOne a) true) = R 0 0 t q rx (qOne a) 0 [] [] := by
    funext c; cases c <;> rfl
  rw [e2] at h2
  -- phase 3
  have h3 := phase3 (R 0 0 t q rx (qOne a) 0 [] []) a L (qOne a) rx rfl rfl rfl
  have e3 : Function.update (R 0 0 t q rx (qOne a) 0 [] []) .m
      (List.replicate (qOne a * rx) true) = R 0 0 t q rx (qOne a) m [] [] := by
    funext c; cases c <;> rfl
  rw [e3] at h3
  -- phase 4
  obtain ⟨n4, hn4, h4⟩ := phase4 (R 0 0 t q rx (qOne a) m [] []) a L q t m rfl rfl rfl rfl
  have e4 : Function.update (R 0 0 t q rx (qOne a) m [] []) .prime
      (List.replicate p true) = R 0 p t q rx (qOne a) m [] [] := by
    funext c; cases c <;> rfl
  rw [e4] at h4
  -- phase 5
  have h5 := phase5 (R 0 p t q rx (qOne a) m [] []) a L q rfl rfl
  have e5 : Function.update (R 0 p t q rx (qOne a) m [] []) .cnt
      (List.replicate (L * q) true) = R (L * q) p t q rx (qOne a) m [] [] := by
    funext c; cases c <;> rfl
  rw [e5] at h5
  -- phase 6
  obtain ⟨n6, hn6, h6⟩ := phase6 a q t rx hm hrx
  -- compose, innermost first
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs P5 P6 _ _ _ _ _ _ _ _ _ _ _ h5 h6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs P4 seq5 _ _ _ _ _ _ _ _ _ _ _ h4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs P3 seq4 _ _ _ _ _ _ _ _ _ _ _ h3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs P2 seq3 _ _ _ _ _ _ _ _ _ _ _ h2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs P1 seq2 _ _ _ _ _ _ _ _ _ _ _ h1 r2
  refine ⟨u1, ?_, r1⟩
  have hn6' : n6 ≤ L * q * (FamilyTableLoop.bodyBound (L * q) p t q rx (qOne a) m + 1) + 1 :=
    hn6
  have hb : assemblyBound a q t rx = (4 * 2 ^ a + 5 * a + 7) + 1 +
      MatrixAddressMachine.exactTime (qOne a) rx 0 + PrimeFromWords.fromBound q t m +
      MatrixAddressMachine.exactTime L q 0 +
      (L * q * (FamilyTableLoop.bodyBound (L * q) p t q rx (qOne a) m + 1) + 1) + 5 := rfl
  rw [hb]
  omega

#print axioms full_update
#print axioms bank_exact
#print axioms phase1
#print axioms phase2
#print axioms phase3
#print axioms phase4
#print axioms phase5
#print axioms phase6
#print axioms family_assembly

end

end EthInapproximability.CurrentPaper.EntryFamilyAssembly
