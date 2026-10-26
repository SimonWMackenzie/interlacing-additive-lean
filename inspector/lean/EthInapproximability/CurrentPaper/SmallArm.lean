import EthInapproximability.CurrentPaper.EncodedETHTail
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# The small-input arm of the ETH SAT machine (unit 4, B4-S2)

Source: frozen v8 `06-eth.tex:238-240`: "For the finitely many excluded
variable counts, enumerate all assignments and scan the input; this is
polynomial in its actual length."

For a fixed threshold `N`, this is ONE fixed one-pass scanner whose finite
control holds, for every assignment `a : Fin N → Bool` of the `N` possible
variables, whether `a` still satisfies every completed clause (design (a) of
the unit-4 map). The canonical binary index field of each literal is
accumulated in saturating finite control (`Fin (N+1)`). The declared clause
count is skipped: after validation the clause fields are exactly the rest of
the word. No machine register is unbounded; the control is a finite type fixed
by `N` alone. The arm is only claimed on canonical words of valid formulas
with fewer than `N` variables (the dispatcher routes only those here).
-/

namespace EthInapproximability.CurrentPaper.SmallArm

open Turing BitMachineEncoding EncodedCNF

inductive Phase where
  | unary | cnt | cntPay | sign | idx | idxPay | done
  deriving DecidableEq, Fintype

variable (N : ℕ)

/-- The finite control of the scanner. -/
structure St where
  ph : Phase
  v : Fin (N + 1)
  w : Fin (N + 1)
  s : Bool
  li : Fin 3
  cs : (Fin N → Bool) → Bool
  al : (Fin N → Bool) → Bool

def St.toProd {N : ℕ} (x : St N) :
    Phase × Fin (N + 1) × Fin (N + 1) × Bool × Fin 3 ×
      ((Fin N → Bool) → Bool) × ((Fin N → Bool) → Bool) :=
  (x.ph, x.v, x.w, x.s, x.li, x.cs, x.al)

def St.ofProd {N : ℕ} (p : Phase × Fin (N + 1) × Fin (N + 1) × Bool × Fin 3 ×
      ((Fin N → Bool) → Bool) × ((Fin N → Bool) → Bool)) : St N :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩

instance : Fintype (St N) :=
  Fintype.ofEquiv _ ⟨St.ofProd, St.toProd, fun _ => rfl, fun _ => rfl⟩

variable {N}

def capN (x : ℕ) : Fin (N + 1) := ⟨min x N, by omega⟩

def cF : (Fin N → Bool) → Bool := fun _ => false

/-- The value of a literal with index `val` and sign `s` under `a`. -/
def litVal (val : ℕ) (s : Bool) (a : Fin N → Bool) : Bool :=
  if h : val < N then a ⟨val, h⟩ == s else false

def nextLi : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- Completion of a literal whose saturated index is `val`. -/
def litDone (x : St N) (val : Fin (N + 1)) : St N :=
  let cs' : (Fin N → Bool) → Bool := fun a => x.cs a || litVal val.val x.s a
  if x.li = 2 then
    ⟨.sign, capN 0, capN 1, false, 0, cF, fun a => x.al a && cs' a⟩
  else
    ⟨.sign, capN 0, capN 1, false, nextLi x.li, cs', x.al⟩

/-- One payload bit of an index field, weight doubled, both saturated. -/
def payStep (x : St N) (b : Bool) : St N :=
  { x with ph := .idx, v := capN (x.v.val + (if b then x.w.val else 0)), w := capN (2 * x.w.val) }

/-- One transition of the scanner on a popped cell (`none` = end of input). -/
def delta (x : St N) : Option Bool → St N
  | none => {x with ph := .done}
  | some b =>
    match x.ph with
    | .unary => if b then x else {x with ph := .cnt}
    | .cnt => if b then {x with ph := .cntPay} else {x with ph := .sign}
    | .cntPay => {x with ph := .cnt}
    | .sign => {x with ph := .idx, s := b}
    | .idx => if b then {x with ph := .idxPay} else litDone x x.v
    | .idxPay => payStep x b
    | .done => x

def init : St N := ⟨.unary, capN 0, capN 1, false, 0, cF, fun _ => true⟩

/-- The scanner's answer: some assignment survived every clause. -/
def answer (x : St N) : Bool := decide (∃ a, x.al a = true)

abbrev Stack := Fin 2

def isDone (x : St N) : Bool := decide (x.ph = .done)

theorem litDone_ph (x : St N) (val : Fin (N + 1)) : (litDone x val).ph = .sign := by
  unfold litDone; split <;> rfl

def program : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (St N)
  | () => .pop 0 (fun x b => delta x b)
      (.branch (fun x => isDone x)
        (.push 1 (fun x => answer x) .halt) (.goto (fun _ => ())))

noncomputable def machine (N : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Stack) 1 () (init (N := N)) program

abbrev Config (N : ℕ) := TM2.Cfg (fun _ : Stack => Bool) Unit (St N)

theorem delta_some_not_done (x : St N) (hx : isDone x = false) (b : Bool) :
    isDone (delta x (some b)) = false := by
  rcases x with ⟨ph, v, w, s, li, cs, al⟩
  simp only [isDone, decide_eq_false_iff_not] at hx ⊢
  cases ph <;> cases b <;> simp_all [delta, litDone_ph, payStep]

theorem step_cons (x : St N) (hx : isDone x = false) (b : Bool) (xs : List Bool)
    (S : Stack → List Bool) (hS : S 0 = b :: xs) :
    advance program (⟨some (), x, S⟩ : Config N) =
      ⟨some (), delta x (some b), Function.update S 0 xs⟩ := by
  have hd := delta_some_not_done x hx b
  simp [advance, TM2.step, TM2.stepAux, program, hS, hd]

theorem step_nil (x : St N) (S : Stack → List Bool) (hS : S 0 = []) :
    advance program (⟨some (), x, S⟩ : Config N) =
      ⟨none, delta x none, Function.update (Function.update S 0 []) 1
        (answer (delta x none) :: S 1)⟩ := by
  have hd : isDone (delta x none) = true := by simp [delta, isDone]
  simp [advance, TM2.step, TM2.stepAux, program, hS, hd]

def dstep (y : St N) (b : Bool) : St N := delta y (some b)

/-- The literal loop: one transition per input cell plus the final one. -/
theorem loop_run (bits : List Bool) (x : St N) (hx : isDone x = false)
    (S : Stack → List Bool) (hS : S 0 = bits) :
    ((advance program)^[bits.length + 1]) (⟨some (), x, S⟩ : Config N) =
      ⟨none, delta (bits.foldl dstep x) none,
        Function.update (Function.update S 0 [])
          1 (answer (delta (bits.foldl dstep x) none) :: S 1)⟩ := by
  induction bits generalizing x S with
  | nil => exact step_nil x S hS
  | cons b xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply, step_cons x hx b xs S hS]
      have hS2 : (Function.update S 0 xs) 0 = xs := by simp
      rw [ih (delta x (some b)) (delta_some_not_done x hx b) (Function.update S 0 xs) hS2]
      simp only [List.foldl_cons, dstep, Function.update_idem]
      rw [Function.update_of_ne (show (1 : Stack) ≠ 0 by decide)]

/-! ## The scanner on canonical encodings -/

theorem unary_fold (n : ℕ) (x : St N) (hx : x.ph = .unary) :
    (EncodedGraph.unary n).foldl dstep x = {x with ph := .cnt} := by
  unfold EncodedGraph.unary
  induction n with
  | zero => simp [dstep, delta, hx]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.foldl_cons]
      have : dstep x true = x := by simp [dstep, delta, hx]
      rw [this, ih]

theorem count_fold (bs : List Bool) (x : St N) (hx : x.ph = .cnt) :
    (EncodedCommunication.field bs).foldl dstep x = {x with ph := .sign} := by
  induction bs generalizing x with
  | nil => simp [EncodedCommunication.field, dstep, delta, hx]
  | cons b bs ih =>
      simp only [EncodedCommunication.field, List.foldl_cons]
      have h1 : dstep x true = {x with ph := .cntPay} := by simp [dstep, delta, hx]
      have h2 : dstep {x with ph := .cntPay} b = x := by
        simp [dstep, delta, hx]
        cases x; simp_all
      rw [h1, h2, ih x hx]

theorem capN_add (V W : ℕ) (b : Bool) :
    (capN (N := N) ((capN (N := N) V).val + if b then (capN (N := N) W).val else 0)) =
      capN (V + if b then W else 0) := by
  cases b <;> simp only [capN, Fin.mk.injEq, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem capN_double (W : ℕ) :
    capN (N := N) (2 * (capN (N := N) W).val) = capN (2 * W) := by
  simp only [capN, Fin.mk.injEq]; omega

theorem litDone_congr (x y : St N) (val : Fin (N + 1)) (hs : x.s = y.s)
    (hli : x.li = y.li) (hcs : x.cs = y.cs) (hal : x.al = y.al) :
    litDone x val = litDone y val := by
  simp [litDone, hs, hli, hcs, hal]

/-- Index accumulation in saturating finite control. -/
theorem field_fold (bs : List Bool) (V W : ℕ) (x : St N) (hx : x.ph = .idx)
    (hv : x.v = capN V) (hw : x.w = capN W) :
    (EncodedCommunication.field bs).foldl dstep x =
      litDone x (capN (V + W * EncodedCommunication.bitsValue bs)) := by
  induction bs generalizing V W x with
  | nil =>
      simp [EncodedCommunication.field, dstep, delta, hx, hv, EncodedCommunication.bitsValue]
  | cons b bs ih =>
      simp only [EncodedCommunication.field, List.foldl_cons]
      set y : St N := payStep x b with hy
      have h1 : dstep (dstep x true) b = y := by
        simp [dstep, delta, hx, hy, payStep]
      rw [h1, ih (V + if b then W else 0) (2 * W) y (by rw [hy]; rfl)
        (by rw [hy]; simp only [payStep]; rw [hv, hw, capN_add])
        (by rw [hy]; simp only [payStep]; rw [hw, capN_double])]
      rw [litDone_congr y x _ (by rw [hy]; rfl) (by rw [hy]; rfl) (by rw [hy]; rfl)
        (by rw [hy]; rfl)]
      congr 2
      cases b <;> simp [EncodedCommunication.bitsValue, Nat.bit] <;> ring

/-- A canonical sign-phase state. -/
def Ready (x : St N) : Prop :=
  x.ph = .sign ∧ x.v = capN 0 ∧ x.w = capN 1 ∧ x.s = false

theorem literal_fold (l : Literal) (x : St N) (hx : Ready x) (hl : l.variable < N) :
    (encodeLiteral l).foldl dstep x =
      let cs' : (Fin N → Bool) → Bool := fun a => x.cs a || litVal l.variable l.positive a
      if x.li = 2 then
        ⟨.sign, capN 0, capN 1, false, 0, cF, fun a => x.al a && cs' a⟩
      else ⟨.sign, capN 0, capN 1, false, nextLi x.li, cs', x.al⟩ := by
  obtain ⟨hph, hv, hw, hs⟩ := hx
  simp only [encodeLiteral, EncodedCommunication.natField, List.foldl_cons]
  set y : St N := {x with ph := .idx, s := l.positive} with hy
  have h1 : dstep x l.positive = y := by simp [dstep, delta, hph, hy]
  rw [h1, field_fold l.variable.bits 0 1 y rfl (by rw [hy]; exact hv) (by rw [hy]; exact hw)]
  have hval : (capN (N := N) (0 + 1 * EncodedCommunication.bitsValue l.variable.bits)).val =
      l.variable := by
    simp [capN, EncodedCommunication.bitsValue_bits]; omega
  simp only [litDone, hval, hy]

def clauseVal (c : Clause) (a : Fin N → Bool) : Bool :=
  litVal c.first.variable c.first.positive a || litVal c.second.variable c.second.positive a ||
    litVal c.third.variable c.third.positive a

theorem clause_fold (c : Clause) (x : St N) (hx : Ready x) (hli : x.li = 0) (hcs : x.cs = cF)
    (hc : c.Valid N) :
    (encodeClause c).foldl dstep x = {x with al := fun a => x.al a && clauseVal c a} := by
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨hph, hv, hw, hs⟩ := hx
  simp only [encodeClause, List.foldl_append]
  rw [literal_fold c.first x ⟨hph, hv, hw, hs⟩ h1]
  simp only [hli, show (0 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  rw [literal_fold c.second _ ⟨rfl, rfl, rfl, rfl⟩ h2]
  simp only [nextLi, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  rw [literal_fold c.third _ ⟨rfl, rfl, rfl, rfl⟩ h3]
  simp only [nextLi, ↓reduceIte]
  rcases x with ⟨ph, v, w, s, li, cs, al⟩
  simp only at hph hv hw hs hli hcs
  subst hph hv hw hs hli hcs
  simp [clauseVal, cF, Bool.or_assoc]

def allVal (cs : List Clause) (a : Fin N → Bool) : Bool := cs.all (fun c => clauseVal c a)

theorem clauses_fold (cs : List Clause) (x : St N) (hx : Ready x) (hli : x.li = 0)
    (hcs : x.cs = cF) (hc : ∀ c ∈ cs, c.Valid N) :
    (clauseFields cs).foldl dstep x = {x with al := fun a => x.al a && allVal cs a} := by
  induction cs generalizing x with
  | nil =>
      rcases x with ⟨ph, v, w, s, li, cs, al⟩
      simp [clauseFields, allVal]
  | cons c cs ih =>
      simp only [clauseFields, List.foldl_append]
      rw [clause_fold c x hx hli hcs (hc c (by simp))]
      obtain ⟨hph, hv, hw, hs⟩ := hx
      rw [ih {x with al := fun a => x.al a && clauseVal c a} ⟨hph, hv, hw, hs⟩ hli hcs
        (fun d hd => hc d (by simp [hd]))]
      simp [allVal, Bool.and_assoc]

theorem encode_fold (f : Formula) (hf : f.Valid) (hn : f.variables ≤ N) :
    (encode f).foldl dstep (init (N := N)) =
      {init (N := N) with ph := .sign, al := fun a => allVal f.clauses a} := by
  have hc : ∀ c ∈ f.clauses, c.Valid N := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hf c hc
    exact ⟨by omega, by omega, by omega⟩
  simp only [encode, List.foldl_append]
  rw [unary_fold f.variables init rfl]
  rw [show EncodedCommunication.natField f.clauses.length =
    EncodedCommunication.field f.clauses.length.bits from rfl]
  rw [count_fold _ _ rfl]
  rw [clauses_fold f.clauses _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl hc]
  simp [init]

/-! ## Semantics: surviving assignments are exactly satisfying assignments -/

theorem litVal_eval (l : Literal) (a : Fin N → Bool) (σ : List Bool)
    (hl : l.variable < N) (hσ : σ.getD l.variable false = a ⟨l.variable, hl⟩) :
    litVal l.variable l.positive a = l.eval σ := by
  unfold litVal Literal.eval
  rw [dif_pos hl, hσ]
  cases l.positive <;> cases a ⟨l.variable, hl⟩ <;> rfl

theorem allVal_iff (f : Formula) (hf : f.Valid) (hn : f.variables ≤ N) :
    (∃ a : Fin N → Bool, allVal f.clauses a = true) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨List.ofFn (fun i : Fin f.variables => a ⟨i, by omega⟩), by simp, ?_⟩
    unfold Formula.eval
    rw [List.all_eq_true]
    intro c hc
    have hv := hf c hc
    have hcv : clauseVal c a = true := by
      unfold allVal at ha; rw [List.all_eq_true] at ha; exact ha c hc
    have key (l : Literal) (hl : l.variable < f.variables) :
        litVal l.variable l.positive a =
          l.eval (List.ofFn (fun i : Fin f.variables => a ⟨i, by omega⟩)) := by
      apply litVal_eval l a _ (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hl]
    unfold clauseVal at hcv
    unfold Clause.eval
    rw [← key _ hv.1, ← key _ hv.2.1, ← key _ hv.2.2]
    exact hcv
  · rintro ⟨σ, hσ, hsat⟩
    refine ⟨fun i => σ.getD i.val false, ?_⟩
    unfold allVal
    rw [List.all_eq_true]
    intro c hc
    unfold Formula.eval at hsat
    rw [List.all_eq_true] at hsat
    have hce := hsat c hc
    have hv := hf c hc
    unfold clauseVal
    unfold Clause.eval at hce
    have h1 := hv.1
    have h2 := hv.2.1
    have h3 := hv.2.2
    rw [litVal_eval c.first _ σ (by omega) rfl, litVal_eval c.second _ σ (by omega) rfl,
      litVal_eval c.third _ σ (by omega) rfl]
    exact hce

theorem answer_eq (f : Formula) (hf : f.Valid) (hn : f.variables ≤ N) :
    answer (delta ((encode f).foldl dstep (init (N := N))) none) =
      EncodedETHTail.satAnswer (encode f) := by
  rw [encode_fold f hf hn]
  unfold answer EncodedETHTail.satAnswer
  have h1 := allVal_iff f hf hn
  have h2 := encode_mem_iff f hf
  simp only [delta]
  rw [decide_eq_decide]
  exact h1.trans h2.symm

/-- **B4-S2.** For every fixed threshold `N`, one fixed finite machine
decides the exact encoded SAT answer on the canonical word of every valid
formula with at most `N` variables, within `|input| + 1` transitions. -/
theorem outputs (f : Formula) (hf : f.Valid) (hn : f.variables ≤ N) :
    (machine N).OutputsWithin (encode f) [EncodedETHTail.satAnswer (encode f)]
      ((encode f).length + 1) := by
  have hrun := loop_run (encode f) (init (N := N)) rfl
    (fun k => if k = (0 : Stack) then encode f else []) (by simp)
  apply outputsWithin_of_raw_run (0 : Stack) 1 () (init (N := N)) program
    (encode f) [EncodedETHTail.satAnswer (encode f)] ((encode f).length + 1)
    ((encode f).length + 1) le_rfl
  · change ((((advance program)^[(encode f).length + 1])
      (⟨some (), init, fun k => if k = (0 : Stack) then encode f else []⟩ : Config N)).l = none)
    rw [hrun]
  · change ((((advance program)^[(encode f).length + 1])
      (⟨some (), init, fun k => if k = (0 : Stack) then encode f else []⟩ : Config N)).stk 1 = _)
    rw [hrun]
    have ha := answer_eq f hf hn
    simp [ha]

theorem outputs_poly (f : Formula) (hf : f.Valid) (hn : f.variables ≤ N) :
    (machine N).OutputsWithin (encode f) [EncodedETHTail.satAnswer (encode f)]
      (1 * ((encode f).length + 1) ^ 1) := by
  simpa using outputs f hf hn

end EthInapproximability.CurrentPaper.SmallArm
