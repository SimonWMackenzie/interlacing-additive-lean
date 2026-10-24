import Paper2.FallbackColourSearch

/-! U16 literal ternary counter (private, lane owner:a-uniform-clock-2): a fixed
first-success controller whose counter is a v-digit TERNARY word (two bits per
digit, `encC`), incremented with carry (digit 2 -> 0 and carry; overflow when every
digit is 2), enumerating exactly the `3^v` colourings from the all-zero colouring,
invoking the fixed predicate program `FallbackColourSearch.P` on each. Every step
charged. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.TernaryColourSearch

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.FallbackColourSearch

/-! ### Ternary semantics -/

def tnext : List (Fin 3) → List (Fin 3)
  | [] => []
  | x :: r => if x = 2 then 0 :: tnext r else (x + 1) :: r

def val : List (Fin 3) → Nat
  | [] => 0
  | x :: r => x.val + 3 * val r

theorem tnext_length (L : List (Fin 3)) : (tnext L).length = L.length := by
  induction L with
  | nil => rfl
  | cons x r ih => by_cases h : x = 2 <;> simp [tnext, h, ih]

theorem val_lt (L : List (Fin 3)) : val L < 3 ^ L.length := by
  induction L with
  | nil => simp [val]
  | cons x r ih =>
    simp only [val, List.length_cons, pow_succ]
    have := x.isLt
    omega

theorem val_tnext (L : List (Fin 3)) (h : val L + 1 < 3 ^ L.length) :
    val (tnext L) = val L + 1 := by
  induction L with
  | nil => simp [val] at h
  | cons x r ih =>
    by_cases hx : x = 2
    · subst hx
      simp only [val, List.length_cons, pow_succ] at h
      have hr : val r + 1 < 3 ^ r.length := by
        have := val_lt r
        by_contra hc
        have : val r + 1 = 3 ^ r.length := by omega
        omega
      simp only [tnext, if_true, val, ih hr]
      simp
      omega
    · simp only [tnext, hx, if_false, val]
      have hv : (x + 1).val = x.val + 1 := by
        fin_cases x
        · rfl
        · rfl
        · exact absurd rfl hx
      rw [hv]; omega

theorem val_inj : ∀ (L M : List (Fin 3)), L.length = M.length → val L = val M → L = M
  | [], [], _, _ => rfl
  | x :: r, y :: s, hl, hv => by
    simp only [val] at hv
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hx : x.val = y.val := by have := x.isLt; have := y.isLt; omega
    have hr : val r = val s := by have := x.isLt; have := y.isLt; omega
    rw [Fin.ext hx, val_inj r s hl hr]

theorem val_replicate_zero (v : Nat) : val (List.replicate v 0) = 0 := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, val, ih]

theorem iterate_val (v : Nat) : ∀ n, n < 3 ^ v →
    val ((tnext^[n]) (List.replicate v 0)) = n ∧
      ((tnext^[n]) (List.replicate v 0)).length = v := by
  intro n
  induction n with
  | zero => intro _; exact ⟨val_replicate_zero v, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨hv, hl⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨?_, by rw [tnext_length, hl]⟩
    rw [val_tnext _ (by rw [hv, hl]; omega), hv]

theorem mem_enumeration (L : List (Fin 3)) :
    (tnext^[val L]) (List.replicate L.length 0) = L := by
  have h := iterate_val L.length (val L) (val_lt L)
  exact val_inj _ _ h.2 h.1

theorem colWord_replicate_zero (j : Nat) (R : List (Fin 3)) :
    colWord (List.replicate j 0 ++ R) = List.replicate (2 * j) false ++ colWord R := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    show [false, false] ++ colWord (List.replicate j 0 ++ R) = _
    rw [ih, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, List.nil_append]

/-! ### The ternary controller -/

abbrev TK := K ⊕ Unit

inductive TAdm where
  | check | inc | restore

abbrev TLab := Lab ⊕ TAdm
abbrev TCtl := Ctl × (Bool × Option Bool × Option Bool)

def tprog : TLab → TM2.Stmt (fun _ : TK => Bool) TLab TCtl
  | .inl l => BitMachineComposition.liftStmt (some TAdm.check) (P l)
  | .inr .check => branch (fun s => s.1.acc) halt
      (load (fun s => (s.1, false, none, none)) (goto (fun _ => .inr .inc)))
  | .inr .inc => pop (.inl 0) (fun s b => (s.1, s.2.1, b, none))
      (pop (.inl 0) (fun s b => (s.1, s.2.1, s.2.2.1, b))
        (branch (fun s => s.2.2.1.isSome)
          (branch (fun s => s.2.2.2.getD false)
            (push (.inr ()) (fun _ => false) (push (.inr ()) (fun _ => false)
              (load (fun s => (s.1, false, none, none)) (goto (fun _ => .inr .inc)))))
            (branch (fun s => s.2.2.1.getD false)
              (push (.inl 0) (fun _ => true) (push (.inl 0) (fun _ => false)
                (load (fun s => (s.1, false, none, none)) (goto (fun _ => .inr .restore)))))
              (push (.inl 0) (fun _ => false) (push (.inl 0) (fun _ => true)
                (load (fun s => (s.1, false, none, none)) (goto (fun _ => .inr .restore)))))))
          (load (fun s => (s.1, true, none, none)) (goto (fun _ => .inr .restore)))))
  | .inr .restore => pop (.inr ()) (fun s b => (s.1, s.2.1, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (push (.inl 0) (fun s => s.2.2.1.getD false)
          (load (fun s => (s.1, s.2.1, none, none)) (goto (fun _ => .inr .restore))))
        (branch (fun s => s.2.1)
          (load (fun s => (s.1, true, none, none)) halt)
          (load (fun _ => (v0, false, none, none)) (goto (fun _ => .inl Lab.readA)))))

/-- Bank: the predicate's own stacks with the counter word `q`, and the carry scratch `w`. -/
def tb (es : List (Nat × Nat)) (q w : List Bool) : TK → List Bool :=
  Sum.elim (Function.update (Sbank es) 0 q) (fun _ => w)

abbrev tstep := advance tprog

theorem tcfg_ext {x : TM2.Cfg (fun _ : TK => Bool) TLab TCtl} {l : Option TLab} {v : TCtl}
    {S : TK → List Bool} (hl : x.l = l) (hv : x.var = v) (hs : ∀ j, x.stk j = S j) :
    x = ⟨l, v, S⟩ := by
  cases x with
  | mk l' v' S' =>
    simp only at hl hv
    subst hl hv
    have : S' = S := funext hs
    subst this
    rfl

variable (es : List (Nat × Nat))

theorem check_reject (vf : Ctl) (fl : Bool) (a b : Option Bool) (q w : List Bool)
    (hv : vf.acc = false) :
    tstep ⟨some (.inr .check), (vf, fl, a, b), tb es q w⟩ =
      ⟨some (.inr .inc), (vf, false, none, none), tb es q w⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vf
  simp only at hv
  subst hv
  rfl

theorem check_accept (vf : Ctl) (fl : Bool) (a b : Option Bool) (q w : List Bool)
    (hv : vf.acc = true) :
    tstep ⟨some (.inr .check), (vf, fl, a, b), tb es q w⟩ =
      ⟨none, (vf, fl, a, b), tb es q w⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vf
  simp only at hv
  subst hv
  rfl

theorem inc_carry (vf : Ctl) (q w : List Bool) :
    tstep ⟨some (.inr .inc), (vf, false, none, none), tb es (false :: true :: q) w⟩ =
      ⟨some (.inr .inc), (vf, false, none, none), tb es q (false :: false :: w)⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem inc_zero (vf : Ctl) (q w : List Bool) :
    tstep ⟨some (.inr .inc), (vf, false, none, none), tb es (false :: false :: q) w⟩ =
      ⟨some (.inr .restore), (vf, false, none, none), tb es (true :: false :: q) w⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem inc_one (vf : Ctl) (q w : List Bool) :
    tstep ⟨some (.inr .inc), (vf, false, none, none), tb es (true :: false :: q) w⟩ =
      ⟨some (.inr .restore), (vf, false, none, none), tb es (false :: true :: q) w⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem inc_empty (vf : Ctl) (w : List Bool) :
    tstep ⟨some (.inr .inc), (vf, false, none, none), tb es [] w⟩ =
      ⟨some (.inr .restore), (vf, true, none, none), tb es [] w⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem restore_cons (vf : Ctl) (fl b : Bool) (q w : List Bool) :
    tstep ⟨some (.inr .restore), (vf, fl, none, none), tb es q (b :: w)⟩ =
      ⟨some (.inr .restore), (vf, fl, none, none), tb es (b :: q) w⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem restore_false (vf : Ctl) (q : List Bool) :
    tstep ⟨some (.inr .restore), (vf, false, none, none), tb es q []⟩ =
      ⟨some (.inl Lab.readA), (v0, false, none, none), tb es q []⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem restore_true (vf : Ctl) (q : List Bool) :
    tstep ⟨some (.inr .restore), (vf, true, none, none), tb es q []⟩ =
      ⟨none, (vf, true, none, none), tb es q []⟩ := by
  apply tcfg_ext rfl rfl
  intro j; rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

theorem carry_loop (vf : Ctl) (j : Nat) : ∀ (R : List (Fin 3)) (w : List Bool),
    (tstep^[j]) ⟨some (.inr .inc), (vf, false, none, none),
        tb es (colWord (List.replicate j 2 ++ R)) w⟩ =
      ⟨some (.inr .inc), (vf, false, none, none),
        tb es (colWord R) (List.replicate (2 * j) false ++ w)⟩ := by
  induction j with
  | zero => intro R w; rfl
  | succ j ih =>
    intro R w
    rw [Function.iterate_succ_apply, List.replicate_succ, List.cons_append]
    rw [show colWord (2 :: (List.replicate j 2 ++ R)) =
      false :: true :: colWord (List.replicate j 2 ++ R) from rfl, inc_carry, ih]
    have e : List.replicate (2 * j) false ++ false :: false :: w =
        List.replicate (2 * (j + 1)) false ++ w := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ', List.replicate_succ',
        List.append_assoc, List.append_assoc]
      rfl
    rw [e]

theorem restore_loop (vf : Ctl) (fl : Bool) : ∀ (w q : List Bool),
    (tstep^[w.length]) ⟨some (.inr .restore), (vf, fl, none, none), tb es q w⟩ =
      ⟨some (.inr .restore), (vf, fl, none, none), tb es (w.reverse ++ q) []⟩ := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons b w ih =>
    intro q
    rw [List.length_cons, Function.iterate_succ_apply, restore_cons, ih]
    simp

/-! ### Rounds -/

theorem tone {x y : TM2.Cfg (fun _ : TK => Bool) TLab TCtl} (h : tstep x = y) :
    tstep^[1] x = y := by
  rw [Function.iterate_one, h]

theorem decomp : ∀ L : List (Fin 3), (∃ x ∈ L, x ≠ 2) →
    ∃ j d R, L = List.replicate j 2 ++ d :: R ∧ d ≠ 2 ∧
      tnext L = List.replicate j 0 ++ (d + 1) :: R
  | [], h => by simp at h
  | x :: r, h => by
    by_cases hx : x = 2
    · subst hx
      have h' : ∃ y ∈ r, y ≠ 2 := by
        obtain ⟨y, hy, hy2⟩ := h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd rfl hy2
        · exact ⟨y, hy, hy2⟩
      obtain ⟨j, d, R, hL, hd, ht⟩ := decomp r h'
      refine ⟨j + 1, d, R, by rw [hL]; rfl, hd, ?_⟩
      simp only [tnext, if_true, ht]
      rfl
    · exact ⟨0, x, r, rfl, hx, by simp [tnext, hx]⟩

theorem val_replicate_two (n : Nat) : val (List.replicate n 2) + 1 = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, val, pow_succ]
    have : (2 : Fin 3).val = 2 := rfl
    rw [this]; omega

theorem exists_ne_two (L : List (Fin 3)) (h : val L + 1 < 3 ^ L.length) : ∃ x ∈ L, x ≠ 2 := by
  by_contra hc
  push Not at hc
  have hL : L = List.replicate L.length 2 := List.eq_replicate_iff.2 ⟨rfl, hc⟩
  have := val_replicate_two L.length
  rw [← hL] at this
  omega

theorem all_two (L : List (Fin 3)) (h : val L + 1 = 3 ^ L.length) :
    L = List.replicate L.length 2 := by
  apply val_inj _ _ (by simp)
  have := val_replicate_two L.length
  omega

/-- Non-accepting, non-overflow round: one charged increment with carry. -/
theorem round_next (vf : Ctl) (L : List (Fin 3)) (hL : val L + 1 < 3 ^ L.length)
    (hv : vf.acc = false) (fl : Bool) (a b : Option Bool) :
    ∃ t ≤ 3 * L.length + 3,
      (tstep^[t]) ⟨some (.inr .check), (vf, fl, a, b), tb es (colWord L) []⟩ =
        ⟨some (.inl Lab.readA), (v0, false, none, none), tb es (colWord (tnext L)) []⟩ := by
  obtain ⟨j, d, R, hLd, hd, ht⟩ := decomp L (exists_ne_two L hL)
  have hj : j ≤ L.length := by rw [hLd]; simp
  have h1 := check_reject es vf fl a b (colWord L) [] hv
  have h2 := carry_loop es vf j (d :: R) []
  simp only [List.append_nil] at h2
  rw [← hLd] at h2
  have h4 := restore_loop es vf false (List.replicate (2 * j) false) (colWord ((d + 1) :: R))
  simp only [List.length_replicate, List.reverse_replicate] at h4
  have h5 := restore_false es vf (List.replicate (2 * j) false ++ colWord ((d + 1) :: R))
  have hcw : List.replicate (2 * j) false ++ colWord ((d + 1) :: R) = colWord (tnext L) := by
    rw [ht, colWord_replicate_zero]
  rw [hcw] at h5 h4
  have h3 : tstep ⟨some (.inr .inc), (vf, false, none, none),
      tb es (colWord (d :: R)) (List.replicate (2 * j) false)⟩ =
      ⟨some (.inr .restore), (vf, false, none, none),
        tb es (colWord ((d + 1) :: R)) (List.replicate (2 * j) false)⟩ := by
    fin_cases d
    · exact inc_zero es vf (colWord R) _
    · exact inc_one es vf (colWord R) _
    · exact absurd rfl hd
  refine ⟨1 + (2 * j + (1 + (j + 1))), by omega, ?_⟩
  exact chain (chain (chain (chain (tone h1) h2) (tone h3)) h4) (tone h5)

/-- Overflow round: every digit is 2; the carry runs out and the controller halts. -/
theorem round_overflow (vf : Ctl) (n : Nat) (hv : vf.acc = false) (fl : Bool)
    (a b : Option Bool) :
    (tstep^[3 * n + 3]) ⟨some (.inr .check), (vf, fl, a, b),
        tb es (colWord (List.replicate n 2)) []⟩ =
      ⟨none, (vf, true, none, none), tb es (List.replicate (2 * n) false) []⟩ := by
  have h1 := check_reject es vf fl a b (colWord (List.replicate n 2)) [] hv
  have h2 := carry_loop es vf n [] []
  simp only [List.append_nil] at h2
  have h3 := inc_empty es vf (List.replicate (2 * n) false)
  have h4 := restore_loop es vf true (List.replicate (2 * n) false) []
  simp only [List.length_replicate, List.reverse_replicate, List.append_nil] at h4
  have h5 := restore_true es vf (List.replicate (2 * n) false)
  rw [show 3 * n + 3 = 1 + (2 * n + (1 + (n + 1))) by ring]
  exact chain (chain (chain (chain (tone h1) h2) (tone h3)) h4) (tone h5)

/-- The predicate call, lifted with no surcharge (admitted `lift_outputs`). -/
theorem pred_call (v : Nat) (hes : ∀ p ∈ es, p.1 < v ∧ p.2 < v) (L : List (Fin 3))
    (hl : L.length = v) :
    ∃ t ≤ es.length * (8 * v) + (edgesWord es).length + 2, ∃ vf : Ctl,
      vf.acc = edgesOK (colWord L) es ∧
      (tstep^[t]) ⟨some (.inl Lab.readA), (v0, false, none, none), tb es (colWord L) []⟩ =
        ⟨some (.inr .check), (vf, false, none, none), tb es (colWord L) []⟩ := by
  obtain ⟨tp, vf, htp, hrun, hacc⟩ := pred_run v es hes (colWord L)
    (by rw [colWord_length, hl])
  obtain ⟨n, hn, hl'⟩ := BitMachineSubroutine.lift_outputs P tprog (some TAdm.check)
    (fun _ => rfl) ((false, none, none) : Bool × Option Bool × Option Bool)
    (fun _ : Unit => ([] : List Bool))
    ⟨some Lab.readA, v0, Function.update (Sbank es) 0 (colWord L)⟩ tp (by rw [hrun])
  rw [hrun] at hl'
  exact ⟨n, hn.trans htp, vf, hacc, hl'⟩

def Lm (v m : Nat) : List (Fin 3) := (tnext^[m]) (List.replicate v 0)

theorem search_from (v : Nat) (hes : ∀ p ∈ es, p.1 < v ∧ p.2 < v) (r : Nat) :
    ∀ m, m + r + 1 = 3 ^ v →
      ∃ t ≤ (r + 1) * (es.length * (8 * v) + (edgesWord es).length + 2 + 3 * v + 4),
        ∃ (vf : Ctl) (fl : Bool) (q : List Bool),
          (tstep^[t]) ⟨some (.inl Lab.readA), (v0, false, none, none),
              tb es (colWord (Lm v m)) []⟩ = ⟨none, (vf, fl, none, none), tb es q []⟩ ∧
          (vf.acc = true ↔ ∃ i ≤ r, edgesOK (colWord (Lm v (m + i))) es = true) := by
  induction r with
  | zero =>
    intro m hm
    obtain ⟨hval, hlen⟩ := iterate_val v m (by omega)
    change val (Lm v m) = m at hval
    change (Lm v m).length = v at hlen
    obtain ⟨tp, htp, vf, hacc, hcall⟩ := pred_call es v hes (Lm v m) hlen
    cases hvf : vf.acc
    · have hall : Lm v m = List.replicate v 2 := by
        have h := all_two (Lm v m) (by rw [hval, hlen]; omega)
        rwa [hlen] at h
      have ho := round_overflow es vf v hvf false none none
      rw [← hall] at ho
      refine ⟨3 * v + 3 + tp, by nlinarith, vf, true, List.replicate (2 * v) false, ?_, ?_⟩
      · rw [Function.iterate_add_apply, hcall, ho]
      · rw [hvf]
        constructor
        · intro h; cases h
        · rintro ⟨i, hi, hp⟩
          have : i = 0 := by omega
          subst this
          rw [Nat.add_zero, ← hacc, hvf] at hp; cases hp
    · refine ⟨1 + tp, by nlinarith, vf, false, colWord (Lm v m), ?_, ?_⟩
      · rw [Function.iterate_add_apply, hcall, Function.iterate_one,
          check_accept es vf false none none _ _ hvf]
      · rw [hvf]
        exact ⟨fun _ => ⟨0, le_rfl, by rw [Nat.add_zero, ← hacc, hvf]⟩, fun _ => rfl⟩
  | succ r ih =>
    intro m hm
    obtain ⟨hval, hlen⟩ := iterate_val v m (by omega)
    change val (Lm v m) = m at hval
    change (Lm v m).length = v at hlen
    obtain ⟨tp, htp, vf, hacc, hcall⟩ := pred_call es v hes (Lm v m) hlen
    cases hvf : vf.acc
    · obtain ⟨tr, htr, hround⟩ := round_next es vf (Lm v m) (by rw [hval, hlen]; omega)
        hvf false none none
      have hnext : tnext (Lm v m) = Lm v (m + 1) := by
        simp only [Lm, Function.iterate_succ_apply']
      rw [hnext] at hround
      obtain ⟨t', ht', vf', fl', q', hrun', hiff⟩ := ih (m + 1) (by omega)
      rw [hlen] at htr
      refine ⟨t' + tr + tp, by nlinarith, vf', fl', q', ?_, ?_⟩
      · rw [Function.iterate_add_apply, Function.iterate_add_apply, hcall, hround, hrun']
      · rw [hiff]
        constructor
        · rintro ⟨i, hi, hp⟩
          exact ⟨i + 1, by omega, by rwa [show m + (i + 1) = m + 1 + i by ring]⟩
        · rintro ⟨i, hi, hp⟩
          rcases i with _ | i
          · rw [Nat.add_zero, ← hacc, hvf] at hp; cases hp
          · exact ⟨i, by omega, by rwa [show m + 1 + i = m + (i + 1) by ring]⟩
    · refine ⟨1 + tp, by nlinarith, vf, false, colWord (Lm v m), ?_, ?_⟩
      · rw [Function.iterate_add_apply, hcall, Function.iterate_one,
          check_accept es vf false none none _ _ hvf]
      · rw [hvf]
        exact ⟨fun _ => ⟨0, by omega, by rw [Nat.add_zero, ← hacc, hvf]⟩, fun _ => rfl⟩

theorem colourable_iff_ternary {v e : Nat} (edge : Fin e → Bool → Fin v) :
    FiniteFallbackOutput.ThreeColourable edge ↔
      ∃ L : List (Fin 3), L.length = v ∧ edgesOK (colWord L) (edgeList edge) = true := by
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨List.ofFn col, by simp, ?_⟩
    rw [edgesOK_iff]
    intro p hp
    obtain ⟨z, rfl⟩ := (mem_edgeList edge p).1 hp
    rw [decode2_colWord _ _ (by simp), decode2_colWord _ _ (by simp)]
    simpa using hcol z
  · rintro ⟨L, hL, h⟩
    exact (colourable_iff_exists edge).2 ⟨colWord L, by rw [colWord_length, hL], h⟩

/-- Literal ternary exhaustive search: from the all-zero `v`-digit ternary counter the
fixed controller enumerates the `3^v` colourings with carry, charging every step, and
halts with the physical accept bit equal to the three-colourability decision. -/
theorem ternary_search_decides {v e : Nat} (edge : Fin e → Bool → Fin v) :
    ∃ t ≤ 3 ^ v * (T edge + 3 * v + 4),
      ∃ (vf : Ctl) (fl : Bool) (q : List Bool),
        (tstep^[t]) ⟨some (.inl Lab.readA), (v0, false, none, none),
            tb (edgeList edge) (colWord (List.replicate v 0)) []⟩ =
          ⟨none, (vf, fl, none, none), tb (edgeList edge) q []⟩ ∧
        vf.acc = decide (FiniteFallbackOutput.ThreeColourable edge) := by
  have hpos : 0 < 3 ^ v := by positivity
  obtain ⟨t, ht, vf, fl, q, hrun, hiff⟩ := search_from (edgeList edge) v (edgeList_bound edge)
    (3 ^ v - 1) 0 (by omega)
  refine ⟨t, ?_, vf, fl, q, ?_, ?_⟩
  · have e1 : 3 ^ v - 1 + 1 = 3 ^ v := by omega
    rw [e1] at ht
    unfold T
    linarith
  · simpa [Lm] using hrun
  · have key : (vf.acc = true) ↔ FiniteFallbackOutput.ThreeColourable edge := by
      rw [hiff, colourable_iff_ternary]
      constructor
      · rintro ⟨i, hi, hp⟩
        exact ⟨Lm v (0 + i), (iterate_val v (0 + i) (by omega)).2, hp⟩
      · rintro ⟨L, hL, hp⟩
        refine ⟨val L, ?_, ?_⟩
        · have := val_lt L; rw [hL] at this; omega
        · have hm := mem_enumeration L
          rw [hL] at hm
          simp only [Lm, Nat.zero_add, hm]
          exact hp
    cases h : vf.acc
    · rw [h] at key
      have hn : ¬ FiniteFallbackOutput.ThreeColourable edge := fun hc => by
        have := key.2 hc
        cases this
      simp [hn]
    · rw [h] at key
      simp [key.1 rfl]

theorem ternary_clock_le {v e : Nat} (edge : Fin e → Bool → Fin v) :
    3 ^ v * (T edge + 3 * v + 4) ≤ 3 ^ v * (10 * (e + 1) * (v + 1)) := by
  apply Nat.mul_le_mul_left
  have h1 := edgesWord_length_le edge
  have h2 : (edgeList edge).length = e := by simp [edgeList]
  unfold T
  rw [h2]
  nlinarith

#print axioms val_tnext
#print axioms mem_enumeration
#print axioms round_next
#print axioms round_overflow
#print axioms pred_call
#print axioms search_from
#print axioms colourable_iff_ternary
#print axioms ternary_search_decides
#print axioms ternary_clock_le

end Paper2.TernaryColourSearch
