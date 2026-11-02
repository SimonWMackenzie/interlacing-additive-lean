import Paper2.MedAlgebra
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# WP-U18a (ii), machine half, part 3: the bank layout and ONE round of the median machine

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117-125
("Amplify the estimator's success probability to 99/100 by a constant number of independent calls
and a median. Accept the source exactly when its estimate is below B+k/2.").

Bank of the fixed machine for an estimator machine `E` and a comparator machine `C`:
`E`'s stacks with its fuel/save pair, `C`'s stacks with its fuel/save pair, and ten named work
stacks `Ax`. One round (13 literal phases, 12 charged handoffs):
take the next length-`s` tape segment `g` (unary-counted), put `field w` in front of it (the input
word `w` is COPIED from the saved reversed field, charged), run `E` cleanly on `pair w g`, move its
output `out` to `C`'s input, put `field w` in front, run `C` cleanly on `pair w out`, and tally its
one-bit answer in unary. The exit bank is stated EXACTLY (every stack of the bank).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.MedianOwner.Med

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.MedianOwner.Phases Paper2.MedianOwner.Phases.Phase
open EthInapproximability.CurrentPaper.EncodedCommunication (field)
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)

/-- The ten named work stacks. -/
inductive Ax | inp | fwr | tr | sc | sc2 | fw2 | tmp | cnt | rc | outp
  deriving DecidableEq, Fintype

variable (E C : Machine)

/-- The stack bank. -/
abbrev K := (Fin E.stackCount ⊕ Fin 2) ⊕ ((Fin C.stackCount ⊕ Fin 2) ⊕ Ax)

def ax (a : Ax) : K E C := .inr (.inr a)
def eIn : K E C := .inl (.inl E.input)
def eFuel : K E C := .inl (.inr 0)
def cIn : K E C := .inr (.inl (.inl C.input))
def cFuel : K E C := .inr (.inl (.inr 0))

def ιE : (Fin E.stackCount ⊕ Fin 2) ↪ K E C := ⟨Sum.inl, Sum.inl_injective⟩
def ιC : (Fin C.stackCount ⊕ Fin 2) ↪ K E C :=
  ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩

/-- A bank from its three parts. -/
def G (e : Fin E.stackCount ⊕ Fin 2 → List Bool) (c : Fin C.stackCount ⊕ Fin 2 → List Bool)
    (a : Ax → List Bool) : K E C → List Bool := Sum.elim e (Sum.elim c a)

/-- The ten work stacks, listed. -/
def A10 (inp fwr tr sc sc2 fw2 tmp cnt rc outp : List Bool) : Ax → List Bool
  | .inp => inp | .fwr => fwr | .tr => tr | .sc => sc | .sc2 => sc2 | .fw2 => fw2
  | .tmp => tmp | .cnt => cnt | .rc => rc | .outp => outp

section Norm

variable {E C}

@[simp] theorem G_upd_ax (e c a) (x : Ax) (q : List Bool) :
    Function.update (G E C e c a) (Sum.inr (Sum.inr x)) q = G E C e c (Function.update a x q) := by
  unfold G; rw [Sum.update_elim_inr, Sum.update_elim_inr]

@[simp] theorem G_upd_e (e c a) (j : Fin E.stackCount ⊕ Fin 2) (q : List Bool) :
    Function.update (G E C e c a) (Sum.inl j) q = G E C (Function.update e j q) c a := by
  unfold G; rw [Sum.update_elim_inl]

@[simp] theorem G_upd_c (e c a) (j : Fin C.stackCount ⊕ Fin 2) (q : List Bool) :
    Function.update (G E C e c a) (Sum.inr (Sum.inl j)) q = G E C e (Function.update c j q) a := by
  unfold G; rw [Sum.update_elim_inr, Sum.update_elim_inl]

@[simp] theorem G_ax (e c a) (x : Ax) : G E C e c a (Sum.inr (Sum.inr x)) = a x := rfl
@[simp] theorem G_e (e c a) (j) : G E C e c a (Sum.inl j) = e j := rfl
@[simp] theorem G_c (e c a) (j) : G E C e c a (Sum.inr (Sum.inl j)) = c j := rfl

@[simp] theorem eb_upd_in (M : Machine) (x f q : List Bool) :
    Function.update (eb M x f) (Sum.inl M.input) q = eb M q f := by
  funext k
  rcases k with k | k
  · by_cases hk : k = M.input
    · subst hk; simp [eb, Machine.init]
    · simp [eb, Machine.init, Function.update_apply, hk]
  · simp [eb, Function.update_apply]

@[simp] theorem eb_upd_fuel (M : Machine) (x f q : List Bool) :
    Function.update (eb M x f) (Sum.inr 0) q = eb M x q := by
  funext k
  rcases k with k | k
  · simp [eb, Function.update_apply]
  · fin_cases k <;> simp [eb, Function.update_apply, BitMachineIteration.foreign]

@[simp] theorem eb_in (M : Machine) (x f : List Bool) : eb M x f (Sum.inl M.input) = x := by
  simp [eb, Machine.init]

@[simp] theorem eb_fuel (M : Machine) (x f : List Bool) : eb M x f (Sum.inr 0) = f := by
  simp [eb, BitMachineIteration.foreign]

theorem A10_upd (inp fwr tr sc sc2 fw2 tmp cnt rc outp : List Bool) (x : Ax) (q : List Bool) :
    Function.update (A10 inp fwr tr sc sc2 fw2 tmp cnt rc outp) x q =
      match x with
      | .inp => A10 q fwr tr sc sc2 fw2 tmp cnt rc outp
      | .fwr => A10 inp q tr sc sc2 fw2 tmp cnt rc outp
      | .tr => A10 inp fwr q sc sc2 fw2 tmp cnt rc outp
      | .sc => A10 inp fwr tr q sc2 fw2 tmp cnt rc outp
      | .sc2 => A10 inp fwr tr sc q fw2 tmp cnt rc outp
      | .fw2 => A10 inp fwr tr sc sc2 q tmp cnt rc outp
      | .tmp => A10 inp fwr tr sc sc2 fw2 q cnt rc outp
      | .cnt => A10 inp fwr tr sc sc2 fw2 tmp q rc outp
      | .rc => A10 inp fwr tr sc sc2 fw2 tmp cnt q outp
      | .outp => A10 inp fwr tr sc sc2 fw2 tmp cnt rc q := by
  funext y
  cases x <;> cases y <;> rfl

theorem bank_E (e c a) (S : Fin E.stackCount ⊕ Fin 2 → List Bool) :
    BitMachineStackEmbedding.bank (ιE E C) (G E C e c a) S = G E C S c a := by
  funext k
  rcases k with k | k
  · exact BitMachineStackEmbedding.bank_at (ιE E C) _ S k
  · refine BitMachineStackEmbedding.bank_outside (ιE E C) _ S _ ?_
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

theorem bank_C (e c a) (S : Fin C.stackCount ⊕ Fin 2 → List Bool) :
    BitMachineStackEmbedding.bank (ιC E C) (G E C e c a) S = G E C e S a := by
  funext k
  rcases k with k | k | k
  · refine BitMachineStackEmbedding.bank_outside (ιC E C) _ S _ ?_
    rintro ⟨j, hj⟩
    exact Sum.inr_ne_inl hj
  · exact BitMachineStackEmbedding.bank_at (ιC E C) _ S k
  · refine BitMachineStackEmbedding.bank_outside (ιC E C) _ S _ ?_
    rintro ⟨j, hj⟩
    simp [ιC] at hj

end Norm

/-! ## The thirteen phases of one round -/

def p1 : Phase (K E C) := ofProg (takeS (ax E C .sc) (ax E C .sc2) (ax E C .tr) (eIn E C)) () none
def p2 : Phase (K E C) := ofProg (mv (ax E C .sc2) (ax E C .sc)) () none
def p3 : Phase (K E C) := ofProg (cp2 (ax E C .fwr) (eIn E C) (ax E C .fw2)) () none
def p4 : Phase (K E C) := ofProg (mv (ax E C .fw2) (ax E C .fwr)) () none
def p5 : Phase (K E C) := ofProg (pushN (eFuel E C) 1) () none
def p6 : Phase (K E C) := call E (ιE E C)
def p7 : Phase (K E C) := ofProg (mv (eIn E C) (ax E C .tmp)) () none
def p8 : Phase (K E C) := ofProg (mv (ax E C .tmp) (cIn E C)) () none
def p9 : Phase (K E C) := ofProg (cp2 (ax E C .fwr) (cIn E C) (ax E C .fw2)) () none
def p10 : Phase (K E C) := ofProg (mv (ax E C .fw2) (ax E C .fwr)) () none
def p11 : Phase (K E C) := ofProg (pushN (cFuel E C) 1) () none
def p12 : Phase (K E C) := call C (ιC E C)
def p13 : Phase (K E C) := ofProg (tally (cIn E C) (ax E C .cnt)) () none

/-- One round: the thirteen phases in sequence. -/
def round : Phase (K E C) :=
  seq (p1 E C) (seq (p2 E C) (seq (p3 E C) (seq (p4 E C) (seq (p5 E C) (seq (p6 E C)
    (seq (p7 E C) (seq (p8 E C) (seq (p9 E C) (seq (p10 E C) (seq (p11 E C)
      (seq (p12 E C) (p13 E C))))))))))))

/-- The per-round clock: `2s + 8|w| + 2·LO + roundBound E LE TE + roundBound C LC TC + 29`. -/
def roundClock (s wl LO RBE RBC : ℕ) : ℕ := 2 * s + 8 * wl + 2 * LO + RBE + RBC + 29

theorem runs_start {A : Phase (K E C)} {S S' T : K E C → List Bool} {b : ℕ} (h : A.Runs S T b)
    (hS : S = S') : A.Runs S' T b := hS ▸ h

/-- **One round, exact.** Start bank: `E`, `C` clean and empty; work stacks
`fwr = reverse (field w)`, `tr = reverse g ++ TR`, `sc = 1^s`, `cnt = CNT`, `rc = RC`, all others
empty. End bank: the same with `tr = TR` and `cnt = 1^[b] ++ CNT`, where `E` outputs `out` on
`pair w g` within `TE` and `C` outputs `[b]` on `pair w out` within `TC`. -/
theorem round_runs (w g out : List Bool) (b : Bool) (s TE TC LO : ℕ) (TR CNT RC : List Bool)
    (hg : g.length = s) (hE : E.OutputsWithin (pair w g) out TE)
    (hC : C.OutputsWithin (pair w out) [b] TC) (hLO : out.length ≤ LO) :
    (round E C).Runs
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse (g.reverse ++ TR) (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] []
          (List.replicate (if b then 1 else 0) true ++ CNT) RC []))
      (roundClock s w.length LO
        (BitMachineIteration.roundBound E (2 * w.length + 1 + s) TE)
        (BitMachineIteration.roundBound C (2 * w.length + 1 + LO) TC)) := by
  have hfl : (field w).length = 2 * w.length + 1 := EncodedCommunication.field_length w
  have hpg : (pair w g).length = 2 * w.length + 1 + s := by
    rw [EncodedComplexity.pair_length, hg]
  have hpo : (pair w out).length ≤ 2 * w.length + 1 + LO := by
    rw [EncodedComplexity.pair_length]; omega
  -- phase 1: take the segment
  have h1 : (p1 E C).Runs
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse (g.reverse ++ TR) (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR [] (List.replicate s true) [] [] CNT RC [])) (s + 1) := by
    have h := takeS_run (ax E C .sc) (ax E C .sc2) (ax E C .tr) (eIn E C)
      (by simp [ax]) (by simp [ax]) (by simp [ax, eIn]) (by simp [ax]) (by simp [ax, eIn])
      (by simp [ax, eIn]) TR g.reverse
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse (g.reverse ++ TR) (List.replicate s true) [] [] [] CNT RC []))
      none (by simp [ax, A10, hg]) (by simp [ax, A10])
    rw [List.length_reverse, hg] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, eIn, G_upd_ax, G_upd_e, G_ax, G_e, eb_upd_in, eb_in, A10_upd, A10,
      List.reverse_reverse, List.append_nil]
  -- phase 2: restore the unary length
  have h2 : (p2 E C).Runs
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR [] (List.replicate s true) [] [] CNT RC []))
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC [])) (s + 1) := by
    have h := mv_run (ax E C .sc2) (ax E C .sc) (by simp [ax]) (List.replicate s true)
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR [] (List.replicate s true) [] [] CNT RC []))
      none (by simp [ax, A10])
    rw [List.length_replicate] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.reverse_replicate, List.append_nil]
  -- phase 3: put `field w` in front of the segment, keeping a copy
  have h3 : (p3 E C).Runs
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E (field w ++ g) []) (eb C [] [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      (2 * w.length + 2) := by
    have h := cp2_run (ax E C .fwr) (eIn E C) (ax E C .fw2) (by simp [ax, eIn]) (by simp [ax])
      (by simp [ax, eIn]) (field w).reverse
      (G E C (eb E g []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      none (by simp [ax, A10])
    rw [List.length_reverse, hfl] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, eIn, G_upd_ax, G_upd_e, G_ax, G_e, eb_upd_in, eb_in, A10_upd, A10,
      List.reverse_reverse, List.append_nil]
  -- phase 4: restore the saved field
  have h4 : (p4 E C).Runs
      (G E C (eb E (field w ++ g) []) (eb C [] [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      (G E C (eb E (field w ++ g) []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (2 * w.length + 2) := by
    have h := mv_run (ax E C .fw2) (ax E C .fwr) (by simp [ax]) (field w)
      (G E C (eb E (field w ++ g) []) (eb C [] [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      none (by simp [ax, A10])
    rw [hfl] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.append_nil]
  -- phase 5: one unit of fuel for `E`
  have h5 : (p5 E C).Runs
      (G E C (eb E (field w ++ g) []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E (field w ++ g) [true]) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC [])) 1 := by
    refine ofProg_runs _ _ _ _ none ((pushN_run _ 1 _ none).trans ?_)
    simp only [eFuel, G_upd_e, G_e, eb_upd_fuel, eb_fuel, List.replicate_one, List.singleton_append]
  -- phase 6: run `E` on `pair w g`
  have h6 : (p6 E C).Runs
      (G E C (eb E (field w ++ g) [true]) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E out []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (BitMachineIteration.roundBound E (2 * w.length + 1 + s) TE + 1) := by
    have h := call_runs E (ιE E C)
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      hE hpg.le
    rw [bank_E, bank_E] at h
    exact h
  -- phase 7: move the output off `E`
  have h7 : (p7 E C).Runs
      (G E C (eb E out []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] out.reverse CNT RC []))
      (LO + 1) := by
    have h := mv_run (eIn E C) (ax E C .tmp) (by simp [ax, eIn]) out
      (G E C (eb E out []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      none (by simp [eIn])
    refine (ofProg_runs _ _ _ _ none (h.trans ?_)).mono (by omega)
    simp only [ax, eIn, G_upd_ax, G_upd_e, G_ax, G_e, eb_upd_in, eb_in, A10_upd, A10,
      List.append_nil]
  -- phase 8: move it onto `C`'s input
  have h8 : (p8 E C).Runs
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] out.reverse CNT RC []))
      (G E C (eb E [] []) (eb C out [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (LO + 1) := by
    have h := mv_run (ax E C .tmp) (cIn E C) (by simp [ax, cIn]) out.reverse
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] out.reverse CNT RC []))
      none (by simp [ax, A10])
    rw [List.length_reverse] at h
    refine (ofProg_runs _ _ _ _ none (h.trans ?_)).mono (by omega)
    simp only [ax, cIn, G_upd_ax, G_upd_c, G_ax, G_c, eb_upd_in, eb_in, A10_upd, A10,
      List.reverse_reverse, List.append_nil]
  -- phase 9: put `field w` in front of the output
  have h9 : (p9 E C).Runs
      (G E C (eb E [] []) (eb C out [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C (field w ++ out) [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      (2 * w.length + 2) := by
    have h := cp2_run (ax E C .fwr) (cIn E C) (ax E C .fw2) (by simp [ax, cIn]) (by simp [ax])
      (by simp [ax, cIn]) (field w).reverse
      (G E C (eb E [] []) (eb C out [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      none (by simp [ax, A10])
    rw [List.length_reverse, hfl] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, cIn, G_upd_ax, G_upd_c, G_ax, G_c, eb_upd_in, eb_in, A10_upd, A10,
      List.reverse_reverse, List.append_nil]
  -- phase 10: restore the saved field
  have h10 : (p10 E C).Runs
      (G E C (eb E [] []) (eb C (field w ++ out) [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      (G E C (eb E [] []) (eb C (field w ++ out) [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (2 * w.length + 2) := by
    have h := mv_run (ax E C .fw2) (ax E C .fwr) (by simp [ax]) (field w)
      (G E C (eb E [] []) (eb C (field w ++ out) [])
        (A10 [] [] TR (List.replicate s true) [] (field w) [] CNT RC []))
      none (by simp [ax, A10])
    rw [hfl] at h
    refine ofProg_runs _ _ _ _ none (h.trans ?_)
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.append_nil]
  -- phase 11: one unit of fuel for `C`
  have h11 : (p11 E C).Runs
      (G E C (eb E [] []) (eb C (field w ++ out) [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C (field w ++ out) [true])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC [])) 1 := by
    refine ofProg_runs _ _ _ _ none ((pushN_run _ 1 _ none).trans ?_)
    simp only [cFuel, G_upd_c, G_c, eb_upd_fuel, eb_fuel, List.replicate_one, List.singleton_append]
  -- phase 12: run `C` on `pair w out`
  have h12 : (p12 E C).Runs
      (G E C (eb E [] []) (eb C (field w ++ out) [true])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C [b] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (BitMachineIteration.roundBound C (2 * w.length + 1 + LO) TC + 1) := by
    have h := call_runs C (ιC E C)
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      hC hpo
    rw [bank_C, bank_C] at h
    exact h
  -- phase 13: tally the answer bit
  have h13 : (p13 E C).Runs
      (G E C (eb E [] []) (eb C [b] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] []
          (List.replicate (if b then 1 else 0) true ++ CNT) RC [])) 1 := by
    have h := tally_run (cIn E C) (ax E C .cnt) (by simp [ax, cIn]) b
      (G E C (eb E [] []) (eb C [b] [])
        (A10 [] (field w).reverse TR (List.replicate s true) [] [] [] CNT RC []))
      none (by simp [cIn])
    refine ofProg_runs _ _ _ _ (some b) (h.trans ?_)
    simp only [ax, cIn, G_upd_ax, G_upd_c, G_ax, G_c, eb_upd_in, eb_in, A10_upd, A10]
  have hall := seq_runs h1 (seq_runs h2 (seq_runs h3 (seq_runs h4 (seq_runs h5 (seq_runs h6
    (seq_runs h7 (seq_runs h8 (seq_runs h9 (seq_runs h10 (seq_runs h11 (seq_runs h12 h13)))))))))))
  refine hall.mono ?_
  unfold roundClock
  omega

end Paper2.MedianOwner.Med
