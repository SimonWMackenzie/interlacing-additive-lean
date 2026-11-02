import Paper2.OuterLocate

/-! A checked two-way branch on one popped bit (`ifProgram`), and the ONE
fixed outer-column location program for all three tags of a tagged column
word (unrestricted `0…`, fixed tail `10…`, diagonal `11…`), built from it and
the checked `OuterLocate` pieces. Generic in the ambient bank. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TagDispatch

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open OutputSkipper (Shape)

section If

variable {K LP LQ VP VQ : Type*} [DecidableEq K]

abbrev ILabel (LP LQ : Type*) := Unit ⊕ (LP ⊕ LQ)
abbrev IControl (VP VQ : Type*) := Option Bool × (VP × VQ)

def ifProgram (src : K) (P : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Q : LQ → TM2.Stmt (fun _ : K => Bool) LQ VQ) (p₀ : LP) (q₀ : LQ) (vp₀ : VP) (vq₀ : VQ) :
    ILabel LP LQ → TM2.Stmt (fun _ : K => Bool) (ILabel LP LQ) (IControl VP VQ)
  | .inl _ => pop src (fun v b => (b, v.2))
      (branch (fun v => v.1.getD false) (goto (fun _ => .inr (.inr q₀)))
        (goto (fun _ => .inr (.inl p₀))))
  | .inr (.inl l) => BitMachineInline.stmt (fun l => (.inr (.inl l) : ILabel LP LQ))
      (fun v => ((some false, (v, vq₀)) : IControl VP VQ)) (fun w => w.2.1) none (P l)
  | .inr (.inr l) => BitMachineInline.stmt (fun l => (.inr (.inr l) : ILabel LP LQ))
      (fun v => ((some true, (vp₀, v)) : IControl VP VQ)) (fun w => w.2.2) none (Q l)

theorem if_false (src : K) (P : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Q : LQ → TM2.Stmt (fun _ : K => Bool) LQ VQ) (p₀ : LP) (q₀ : LQ) (vp₀ : VP) (vq₀ : VQ)
    (S : K → List Bool) (w : List Bool) (hS : S src = false :: w)
    (tP : ℕ) (vp₁ : VP) (T : K → List Bool)
    (hP : ((advance P)^[tP]) (⟨some p₀, vp₀, Function.update S src w⟩ :
      TM2.Cfg (fun _ : K => Bool) LP VP) = ⟨none, vp₁, T⟩) :
    ∃ t ≤ tP + 1,
      ((advance (ifProgram src P Q p₀ q₀ vp₀ vq₀))^[t])
        (⟨some (.inl ()), (none, (vp₀, vq₀)), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (ILabel LP LQ) (IControl VP VQ)) =
        ⟨none, (some false, (vp₁, vq₀)), T⟩ := by
  have hh : (((advance P)^[tP]) (⟨some p₀, vp₀, Function.update S src w⟩ :
      TM2.Cfg (fun _ : K => Bool) LP VP)).l = none := by rw [hP]
  obtain ⟨a, ha, har⟩ := BitMachineInline.outputs (fun l => (.inr (.inl l) : ILabel LP LQ))
    (fun v => ((some false, (v, vq₀)) : IControl VP VQ)) (fun w => w.2.1) (fun _ => rfl) none
    P (ifProgram src P Q p₀ q₀ vp₀ vq₀) (fun _ => rfl)
    (⟨some p₀, vp₀, Function.update S src w⟩ : TM2.Cfg (fun _ : K => Bool) LP VP) tP hh
  rw [hP] at har
  simp only [BitMachineInline.cfg] at har
  have e : advance (ifProgram src P Q p₀ q₀ vp₀ vq₀)
      (⟨some (.inl ()), (none, (vp₀, vq₀)), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (ILabel LP LQ) (IControl VP VQ)) =
      ⟨some (.inr (.inl p₀)), (some false, (vp₀, vq₀)), Function.update S src w⟩ := by
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, ifProgram, hS]
  refine ⟨a + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, e]
  exact har

theorem if_true (src : K) (P : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Q : LQ → TM2.Stmt (fun _ : K => Bool) LQ VQ) (p₀ : LP) (q₀ : LQ) (vp₀ : VP) (vq₀ : VQ)
    (S : K → List Bool) (w : List Bool) (hS : S src = true :: w)
    (tQ : ℕ) (vq₁ : VQ) (T : K → List Bool)
    (hQ : ((advance Q)^[tQ]) (⟨some q₀, vq₀, Function.update S src w⟩ :
      TM2.Cfg (fun _ : K => Bool) LQ VQ) = ⟨none, vq₁, T⟩) :
    ∃ t ≤ tQ + 1,
      ((advance (ifProgram src P Q p₀ q₀ vp₀ vq₀))^[t])
        (⟨some (.inl ()), (none, (vp₀, vq₀)), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (ILabel LP LQ) (IControl VP VQ)) =
        ⟨none, (some true, (vp₀, vq₁)), T⟩ := by
  have hh : (((advance Q)^[tQ]) (⟨some q₀, vq₀, Function.update S src w⟩ :
      TM2.Cfg (fun _ : K => Bool) LQ VQ)).l = none := by rw [hQ]
  obtain ⟨a, ha, har⟩ := BitMachineInline.outputs (fun l => (.inr (.inr l) : ILabel LP LQ))
    (fun v => ((some true, (vp₀, v)) : IControl VP VQ)) (fun w => w.2.2) (fun _ => rfl) none
    Q (ifProgram src P Q p₀ q₀ vp₀ vq₀) (fun _ => rfl)
    (⟨some q₀, vq₀, Function.update S src w⟩ : TM2.Cfg (fun _ : K => Bool) LQ VQ) tQ hh
  rw [hQ] at har
  simp only [BitMachineInline.cfg] at har
  have e : advance (ifProgram src P Q p₀ q₀ vp₀ vq₀)
      (⟨some (.inl ()), (none, (vp₀, vq₀)), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (ILabel LP LQ) (IControl VP VQ)) =
      ⟨some (.inr (.inr q₀)), (some true, (vp₀, vq₀)), Function.update S src w⟩ := by
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, ifProgram, hS]
  refine ⟨a + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, e]
  exact har

end If

/-! ### One program for all three tags -/

variable {J : Type*} [DecidableEq J]

def haltProg : Unit → TM2.Stmt (fun _ : J => Bool) Unit Unit := fun _ => halt

def unresBody (e : FetchIndexed.Stack ↪ J) :=
  BitMachineRawSequence.program (OuterLocate.pushOne (e FetchIndexed.myC))
    (fun l => stackStmt e (FetchIndexed.rowProgram l)) FetchIndexed.rowStart ()
    FetchIndexed.rowControl
def fixedBody (e : FetchIndexed.Stack ↪ J) := fun l => stackStmt e (FetchIndexed.colProgram l)
def inner (e : FetchIndexed.Stack ↪ J) :=
  ifProgram (e FetchIndexed.fwC) (fixedBody e) (haltProg (J := J)) FetchIndexed.colStart ()
    FetchIndexed.colControl ()
def program (e : FetchIndexed.Stack ↪ J) :=
  ifProgram (e FetchIndexed.fwC) (unresBody e) (inner e)
    (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
    ((none : Option Bool), (FetchIndexed.colControl, ()))

def startControl := ((none : Option Bool), (((), FetchIndexed.rowControl),
  ((none : Option Bool), (FetchIndexed.colControl, ()))))

theorem fixed_dispatch (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (K : Code) (hK : Shape K) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning K) c) (p : ℕ) (hp : p < cs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = [true, false] ++ cs.flatten)
    (hcc : W (e FetchIndexed.ccC) = encodeCode K)
    (hidx : W (e FetchIndexed.idxC) = List.replicate p true) :
    ∃ t ≤ FetchIndexed.colBound K cs p [] + 2, ∃ v,
      ((advance (program e))^[t])
        (⟨some (.inl ()), startControl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update W (e FetchIndexed.fwC) cs.flatten)
          (e SuccessFetchJoin.lblF) (cs.getD p [])⟩ := by
  have hne : ∀ x : FetchIndexed.Stack, x ≠ FetchIndexed.fwC →
      e x ≠ e FetchIndexed.fwC := fun x hx h => hx (e.injective h)
  let W1 := Function.update W (e FetchIndexed.fwC) (false :: cs.flatten)
  have hW12 : Function.update W1 (e FetchIndexed.fwC) cs.flatten =
      Function.update W (e FetchIndexed.fwC) cs.flatten := by
    simp only [W1, Function.update_idem]
  obtain ⟨t2, ht2, v2, p2⟩ := SuccessFetchJoin.lift_col e
    (Function.update W (e FetchIndexed.fwC) cs.flatten) K hK cs hcs [] p hp
    (fun j => by
      rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.fwC]))]; exact hin j)
    (by simp)
    (by rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.ccC, FetchIndexed.fwC]))]
        exact hcc)
    (by rw [Function.update_of_ne (hne _ (by simp [FetchIndexed.idxC, FetchIndexed.fwC]))]
        exact hidx)
  rw [← hW12] at p2
  obtain ⟨t1, ht1, q1⟩ := if_false (e FetchIndexed.fwC) (fixedBody e) (haltProg (J := J))
    FetchIndexed.colStart () FetchIndexed.colControl () W1 cs.flatten
    (by simp [W1]) t2 v2 _ p2
  obtain ⟨t0, ht0, q0⟩ := if_true (e FetchIndexed.fwC) (unresBody e) (inner e)
    (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
    ((none : Option Bool), (FetchIndexed.colControl, ())) W (false :: cs.flatten)
    (by rw [hfw]; rfl) t1 _ _ q1
  rw [hW12] at q0
  exact ⟨t0, by omega, _, q0⟩

theorem diagonal_dispatch (e : FetchIndexed.Stack ↪ J) (W : J → List Bool) (O : List Bool)
    (hfw : W (e FetchIndexed.fwC) = [true, true] ++ O) :
    ∃ t ≤ 3, ∃ v,
      ((advance (program e))^[t])
        (⟨some (.inl ()), startControl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update W (e FetchIndexed.fwC) O⟩ := by
  let W1 := Function.update W (e FetchIndexed.fwC) (true :: O)
  have h2 : ((advance (haltProg (J := J)))^[1])
      (⟨some (), (), Function.update W1 (e FetchIndexed.fwC) O⟩ :
        TM2.Cfg (fun _ : J => Bool) Unit Unit) =
      ⟨none, (), Function.update W (e FetchIndexed.fwC) O⟩ := by
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, haltProg, W1]
  obtain ⟨t1, ht1, q1⟩ := if_true (e FetchIndexed.fwC) (fixedBody e) (haltProg (J := J))
    FetchIndexed.colStart () FetchIndexed.colControl () W1 O (by simp [W1]) 1 () _ h2
  obtain ⟨t0, ht0, q0⟩ := if_true (e FetchIndexed.fwC) (unresBody e) (inner e)
    (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
    ((none : Option Bool), (FetchIndexed.colControl, ())) W (true :: O)
    (by rw [hfw]; rfl) t1 _ _ q1
  exact ⟨t0, by omega, _, q0⟩

theorem unres_dispatch (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (K1 K2 : Code) (hK1 : Shape K1) (hK2 : Shape K2) (z1 : List Bool)
    (hz1 : Produces (meaning K1) z1) (rs : List (List Bool))
    (hrs : ∀ r ∈ rs, Produces (meaning K2) r) (p : ℕ) (hp : p < rs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = [false] ++ (z1 ++ rs.flatten))
    (hcc : W (e FetchIndexed.ccC) = encodeCode K1)
    (hrc : W (e FetchIndexed.rcC) = encodeCode K2)
    (hmy : W (e FetchIndexed.myC) = [])
    (hidx : W (e FetchIndexed.idxC) = List.replicate p true) :
    ∃ t ≤ 1 + FetchIndexed.rowBound K1 K2 [z1] rs p [] + 3, ∃ v,
      ((advance (program e))^[t])
        (⟨some (.inl ()), startControl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update (Function.update W (e FetchIndexed.fwC)
          (z1 ++ rs.flatten)) (e FetchIndexed.myC) [true]) (e SuccessFetchJoin.lblF)
          (rs.getD p [])⟩ := by
  have hne : ∀ x y : FetchIndexed.Stack, x ≠ y → e x ≠ e y := fun x y hx h => hx (e.injective h)
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
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs (OuterLocate.pushOne (e FetchIndexed.myC))
    (fun l => stackStmt e (FetchIndexed.rowProgram l)) () FetchIndexed.rowStart
    () () FetchIndexed.rowControl v3 _ _ _ _ _ p1 p3
  obtain ⟨t0, ht0, q0⟩ := if_false (e FetchIndexed.fwC) (unresBody e) (inner e)
    (BitMachineRawSequence.leftLabel ()) (.inl ()) ((), FetchIndexed.rowControl)
    ((none : Option Bool), (FetchIndexed.colControl, ())) W (z1 ++ rs.flatten)
    (by rw [hfw]; rfl) r1 _ _ q1
  exact ⟨t0, by omega, _, q0⟩

end

#print axioms if_false
#print axioms if_true
#print axioms fixed_dispatch
#print axioms diagonal_dispatch
#print axioms unres_dispatch

end Paper2.TagDispatch
