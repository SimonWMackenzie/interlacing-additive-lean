import Paper2.SuccessFetchJoin

/-! Segment 2, item (2), template case: locating the outer column `Z.2 p`
inside the tagged column word (`Z = forgetTag ξ z`), one fixed program per
tag (the finite-control dispatch on the two tag bits is NOT in this file).

* fixed tail `[true, false] ++ (piCodec outer s).encode js`: pop the two tag
  bits, then the code-driven fetch of the `p`-th outer word (`K = outerCode col_k`);
* unrestricted `[false] ++ rawEnc Z`: pop one bit, write the constant unary
  count `1`, skip the single word of the code `copies (s+1) col_k` (the whole
  `Z.1` tuple), then fetch the `p`-th outer word;
* diagonal `[true, true] ++ outerEnc j`: after popping two bits the cell holds
  the outer word itself (`popBits_run`).

Generic in the ambient bank (any embedding of `FetchIndexed.Stack`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.OuterLocate

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open OutputSkipper (Shape)

variable {J : Type*} [DecidableEq J]

def popBits (src : J) (k : ℕ) : Fin (k + 1) → TM2.Stmt (fun _ : J => Bool) (Fin (k + 1)) Unit :=
  fun i => if h : i.val < k then pop src (fun _ _ => ()) (goto (fun _ => ⟨i.val + 1, by omega⟩))
    else halt

theorem popBits_run (src : J) (k : ℕ) : ∀ (m : ℕ) (hm : m ≤ k) (pre : List Bool),
    pre.length = k - m → ∀ (w : List Bool) (S : J → List Bool), S src = pre ++ w →
    ((advance (popBits src k))^[(k - m) + 1]) (⟨some ⟨m, by omega⟩, (), S⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, (), Function.update S src w⟩ := by
  intro m hm
  induction h : k - m generalizing m with
  | zero =>
    intro pre hpre w S hS
    have hmk : m = k := by omega
    subst hmk
    have hp : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    have hS' : Function.update S src w = S := by
      rw [show w = S src by simpa using hS.symm]
      exact Function.update_eq_self _ _
    rw [hS']
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, popBits]
  | succ d ih =>
    intro pre hpre w S hS
    obtain ⟨b, pre', rfl⟩ : ∃ b pre', pre = b :: pre' := by
      cases pre with
      | nil => simp at hpre
      | cons b pre' => exact ⟨b, pre', rfl⟩
    have hlt : m < k := by omega
    rw [Function.iterate_succ_apply]
    have e : advance (popBits src k) (⟨some ⟨m, by omega⟩, (), S⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨some ⟨m + 1, by omega⟩, (), Function.update S src (pre' ++ w)⟩ := by
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, popBits, hlt, hS]
    rw [e, ih (m + 1) (by omega) (by omega) pre' (by simp at hpre; omega) w _
      (by rw [Function.update_self]), Function.update_idem]

def pushOne (k : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit Unit :=
  fun _ => push k (fun _ => true) halt

theorem pushOne_run (k : J) (S : J → List Bool) (hS : S k = []) :
    ((advance (pushOne k))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, (), Function.update S k [true]⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, pushOne, hS]

/-! ### Fixed tail -/

def fixedProgram (e : FetchIndexed.Stack ↪ J) :=
  BitMachineRawSequence.program (popBits (e FetchIndexed.fwC) 2)
    (fun l => stackStmt e (FetchIndexed.colProgram l)) FetchIndexed.colStart ()
    FetchIndexed.colControl

theorem fixed_locate (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (K : Code) (hK : Shape K) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning K) c) (p : ℕ) (hp : p < cs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = [true, false] ++ cs.flatten)
    (hcc : W (e FetchIndexed.ccC) = encodeCode K)
    (hidx : W (e FetchIndexed.idxC) = List.replicate p true) :
    ∃ t ≤ 3 + FetchIndexed.colBound K cs p [] + 1, ∃ v,
      ((advance (fixedProgram e))^[t])
        (⟨some (BitMachineRawSequence.leftLabel ⟨0, by omega⟩), ((), FetchIndexed.colControl),
          W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update W (e FetchIndexed.fwC) cs.flatten)
          (e SuccessFetchJoin.lblF) (cs.getD p [])⟩ := by
  have p1 := popBits_run (e FetchIndexed.fwC) 2 0 (by omega) [true, false] rfl cs.flatten W hfw
  have hne : ∀ x : FetchIndexed.Stack, x ≠ FetchIndexed.fwC →
      e x ≠ e FetchIndexed.fwC := fun x hx h => hx (e.injective h)
  let W' := Function.update W (e FetchIndexed.fwC) cs.flatten
  obtain ⟨t2, ht2, v2, p2⟩ := SuccessFetchJoin.lift_col e W' K hK cs hcs [] p hp
    (fun j => by
      simp only [W']
      rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.fwC]))]
      exact hin j)
    (by simp [W'])
    (by simp only [W']
        rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.ccC, FetchIndexed.fwC]))]
        exact hcc)
    (by simp only [W']
        rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.idxC, FetchIndexed.fwC]))]
        exact hidx)
  obtain ⟨r, hr, q⟩ := BitMachineRawSequence.runs (popBits (e FetchIndexed.fwC) 2)
    (fun l => stackStmt e (FetchIndexed.colProgram l)) ⟨0, by omega⟩ FetchIndexed.colStart
    () () FetchIndexed.colControl v2 _ _ _ _ _ p1 p2
  exact ⟨r, by omega, _, q⟩

/-! ### Unrestricted -/

def u1 (e : FetchIndexed.Stack ↪ J) :=
  BitMachineRawSequence.program (popBits (e FetchIndexed.fwC) 1) (pushOne (e FetchIndexed.myC))
    () () ()
def unresProgram (e : FetchIndexed.Stack ↪ J) :=
  BitMachineRawSequence.program (u1 e) (fun l => stackStmt e (FetchIndexed.rowProgram l))
    FetchIndexed.rowStart ((), ()) FetchIndexed.rowControl

theorem unres_locate (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (K1 K2 : Code) (hK1 : Shape K1) (hK2 : Shape K2) (z1 : List Bool)
    (hz1 : Produces (meaning K1) z1) (rs : List (List Bool))
    (hrs : ∀ r ∈ rs, Produces (meaning K2) r) (p : ℕ) (hp : p < rs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = [false] ++ (z1 ++ rs.flatten))
    (hcc : W (e FetchIndexed.ccC) = encodeCode K1)
    (hrc : W (e FetchIndexed.rcC) = encodeCode K2)
    (hmy : W (e FetchIndexed.myC) = [])
    (hidx : W (e FetchIndexed.idxC) = List.replicate p true) :
    ∃ t ≤ 2 + 1 + 1 + FetchIndexed.rowBound K1 K2 [z1] rs p [] + 1, ∃ v,
      ((advance (unresProgram e))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ⟨0, by omega⟩)),
          (((), ()), FetchIndexed.rowControl), W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update (Function.update W (e FetchIndexed.fwC)
          (z1 ++ rs.flatten)) (e FetchIndexed.myC) [true]) (e SuccessFetchJoin.lblF)
          (rs.getD p [])⟩ := by
  have hne : ∀ x y : FetchIndexed.Stack, x ≠ y → e x ≠ e y := fun x y hx h => hx (e.injective h)
  have p1 := popBits_run (e FetchIndexed.fwC) 1 0 (by omega) [false] rfl (z1 ++ rs.flatten) W hfw
  let W1 := Function.update W (e FetchIndexed.fwC) (z1 ++ rs.flatten)
  have p2 := pushOne_run (e FetchIndexed.myC) W1
    (by simp only [W1]
        rw [Function.update_of_ne (hne _ _ (by simp [FetchIndexed.myC, FetchIndexed.fwC]))]
        exact hmy)
  let W2 := Function.update W1 (e FetchIndexed.myC) [true]
  have hW2 : ∀ x : FetchIndexed.Stack, x ≠ FetchIndexed.fwC → x ≠ FetchIndexed.myC →
      W2 (e x) = W (e x) := by
    intro x h1 h2
    simp only [W2, W1]
    rw [Function.update_of_ne (hne _ _ h2), Function.update_of_ne (hne _ _ h1)]
  obtain ⟨t3, ht3, v3, p3⟩ := SuccessFetchJoin.lift_row e W2 K1 K2 hK1 hK2 [z1] rs
    (by intro c hc; simp at hc; subst hc; exact hz1) hrs [] p hp
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
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs (popBits (e FetchIndexed.fwC) 1)
    (pushOne (e FetchIndexed.myC)) ⟨0, by omega⟩ () () () () () _ _ _ _ _ p1 p2
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs (u1 e)
    (fun l => stackStmt e (FetchIndexed.rowProgram l))
    (BitMachineRawSequence.leftLabel ⟨0, by omega⟩) FetchIndexed.rowStart
    ((), ()) ((), ()) FetchIndexed.rowControl v3 _ _ _ _ _ q1 p3
  exact ⟨r2, by omega, _, q2⟩

end

#print axioms popBits_run
#print axioms fixed_locate
#print axioms unres_locate

end Paper2.OuterLocate
