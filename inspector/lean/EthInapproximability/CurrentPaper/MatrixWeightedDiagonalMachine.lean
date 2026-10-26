import EthInapproximability.CurrentPaper.MatrixWeightedDiagonalStages
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Literal diagonal raw-column ordinal machine

The public inputs are unary stacks 0--4: second-row code, first-word base,
column alphabet size, bin count, and bin-word base. Stack 5 is the distinct
raw-column ordinal output. The other seventeen stacks are temporary.

Source: frozen v8 Appendix A's joint-tail diagonal and Appendix B's
`thm:paper-materialization`. Quotient and remainder use the actual copied-
dividend division primitive underlying `MatrixIndexQuotient`; no decoded
ordinal or result-bearing callback is supplied.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedDiagonalMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 23

inductive State where
  | copy (v : Option Bool)
  | division (v : Bool)
  | power (v : MatrixWeightedPower.Control)
  | cut (v : MatrixUnaryCut.Control)
  | address (v : Bool)
  | idle
  deriving Fintype

inductive Label where
  | copyWordInput (l : BitMachineCopy.Label)
  | initDivideWord
  | divideWord (l : MatrixUnaryDivision.Label)
  | clearWordQuotient
  | copyTailExponent (l : BitMachineCopy.Label)
  | tailExponentSuccessor
  | tailPowerOne
  | tailPower (l : MatrixWeightedPower.Label)
  | initCopyTailInput
  | copyTailInput (l : BitMachineCopy.Label)
  | initDivideTail
  | divideTail (l : MatrixUnaryDivision.Label)
  | clearTailQuotient
  | clearTailPower
  | copyBinExponent (l : BitMachineCopy.Label)
  | binPowerOne
  | binPower (l : MatrixWeightedPower.Label)
  | initCopyPower
  | copyPower (l : BitMachineCopy.Label)
  | one
  | cutPower (l : MatrixUnaryCut.Label)
  | initCopyBase
  | copyBase (l : BitMachineCopy.Label)
  | initCutBase
  | cutBase (l : MatrixUnaryCut.Label)
  | initCopyGeomNumerator
  | copyGeomNumerator (l : BitMachineCopy.Label)
  | initDivideGeom
  | divideGeom (l : MatrixUnaryDivision.Label)
  | clearGeomRemainder
  | initMultiplyWord
  | multiplyWord (l : MatrixAddressMachine.Label)
  | multiplyTail (l : MatrixAddressMachine.Label)
  | initClear
  | clear (i : Fin 18)
  | done
  deriving Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label State

def getCopy : State → Option Bool
  | .copy v => v
  | _ => none
def getDivision : State → Bool
  | .division v => v
  | _ => false
def getPower : State → MatrixWeightedPower.Control
  | .power v => v
  | _ => (false,false)
def getCut : State → MatrixUnaryCut.Control
  | .cut v => v
  | _ => (false,true)
def getAddress : State → Bool
  | .address v => v
  | _ => false

def copyWordInputSlots : Fin 3 ↪ Stack := ⟨![0,13,7], by decide⟩
def divideWordSlots : Fin 6 ↪ Stack := ⟨![13,1,9,15,14,12], by decide⟩
def copyTailExponentSlots : Fin 3 ↪ Stack := ⟨![3,6,7], by decide⟩
def tailPowerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨Sum.elim (![8,2,9,10,11,12]) (![6]), by decide⟩
def copyTailInputSlots : Fin 3 ↪ Stack := ⟨![15,13,7], by decide⟩
def divideTailSlots : Fin 6 ↪ Stack := ⟨![13,8,9,16,14,12], by decide⟩
def copyBinExponentSlots : Fin 3 ↪ Stack := ⟨![3,6,7], by decide⟩
def binPowerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨Sum.elim (![8,4,9,10,11,12]) (![6]), by decide⟩
def copyPowerSlots : Fin 3 ↪ Stack := ⟨![8,17,7], by decide⟩
def cutPowerSlots : Fin 4 ↪ Stack := ⟨![17,18,19,20], by decide⟩
def copyBaseSlots : Fin 3 ↪ Stack := ⟨![4,21,7], by decide⟩
def cutBaseSlots : Fin 4 ↪ Stack := ⟨![21,18,19,20], by decide⟩
def copyGeomNumeratorSlots : Fin 3 ↪ Stack := ⟨![17,13,7], by decide⟩
def divideGeomSlots : Fin 6 ↪ Stack := ⟨![13,21,9,14,22,12], by decide⟩
def multiplyWordSlots : Fin 6 ↪ Stack := ⟨![0,22,13,9,10,14], by decide⟩
def multiplyTailSlots : Fin 6 ↪ Stack := ⟨![16,8,14,9,10,5], by decide⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .copyWordInput l => BitMachineStackEmbedding.stmt copyWordInputSlots Label.copyWordInput
      State.copy getCopy (some .initDivideWord) (BitMachineCopy.program l)
  | .initDivideWord => load (fun _ => .division false)
      (goto (fun _ => .divideWord .start))
  | .divideWord l => BitMachineStackEmbedding.stmt divideWordSlots Label.divideWord
      State.division getDivision (some .clearWordQuotient) (MatrixUnaryDivision.program l)
  | .clearWordQuotient => pop 14 (fun _ b => .copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => .clearWordQuotient))
        (goto (fun _ => .copyTailExponent .scan)))
  | .copyTailExponent l => BitMachineStackEmbedding.stmt copyTailExponentSlots
      Label.copyTailExponent State.copy getCopy (some .tailExponentSuccessor)
      (BitMachineCopy.program l)
  | .tailExponentSuccessor => push 6 (fun _ => true)
      (goto (fun _ => .tailPowerOne))
  | .tailPowerOne => push 8 (fun _ => true)
      (load (fun _ => .power (false,false))
        (goto (fun _ => .tailPower (.inr .test))))
  | .tailPower l => BitMachineStackEmbedding.stmt tailPowerSlots Label.tailPower
      State.power getPower (some .initCopyTailInput) (MatrixWeightedPower.program l)
  | .initCopyTailInput => load (fun _ => .copy none)
      (goto (fun _ => .copyTailInput .scan))
  | .copyTailInput l => BitMachineStackEmbedding.stmt copyTailInputSlots
      Label.copyTailInput State.copy getCopy (some .initDivideTail)
      (BitMachineCopy.program l)
  | .initDivideTail => load (fun _ => .division false)
      (goto (fun _ => .divideTail .start))
  | .divideTail l => BitMachineStackEmbedding.stmt divideTailSlots Label.divideTail
      State.division getDivision (some .clearTailQuotient) (MatrixUnaryDivision.program l)
  | .clearTailQuotient => pop 14 (fun _ b => .copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => .clearTailQuotient))
        (goto (fun _ => .clearTailPower)))
  | .clearTailPower => pop 8 (fun _ b => .copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => .clearTailPower))
        (goto (fun _ => .copyBinExponent .scan)))
  | .copyBinExponent l => BitMachineStackEmbedding.stmt copyBinExponentSlots
      Label.copyBinExponent State.copy getCopy (some .binPowerOne) (BitMachineCopy.program l)
  | .binPowerOne => push 8 (fun _ => true)
      (load (fun _ => .power (false,false))
        (goto (fun _ => .binPower (.inr .test))))
  | .binPower l => BitMachineStackEmbedding.stmt binPowerSlots Label.binPower
      State.power getPower (some .initCopyPower) (MatrixWeightedPower.program l)
  | .initCopyPower => load (fun _ => .copy none)
      (goto (fun _ => .copyPower .scan))
  | .copyPower l => BitMachineStackEmbedding.stmt copyPowerSlots Label.copyPower
      State.copy getCopy (some .one) (BitMachineCopy.program l)
  | .one => push 18 (fun _ => true)
      (load (fun _ => .cut (false,true)) (goto (fun _ => .cutPower .scan)))
  | .cutPower l => BitMachineStackEmbedding.stmt cutPowerSlots Label.cutPower
      State.cut getCut (some .initCopyBase) (MatrixUnaryCut.program l)
  | .initCopyBase => load (fun _ => .copy none)
      (goto (fun _ => .copyBase .scan))
  | .copyBase l => BitMachineStackEmbedding.stmt copyBaseSlots Label.copyBase
      State.copy getCopy (some .initCutBase) (BitMachineCopy.program l)
  | .initCutBase => load (fun _ => .cut (false,true))
      (goto (fun _ => .cutBase .scan))
  | .cutBase l => BitMachineStackEmbedding.stmt cutBaseSlots Label.cutBase
      State.cut getCut (some .initCopyGeomNumerator) (MatrixUnaryCut.program l)
  | .initCopyGeomNumerator => load (fun _ => .copy none)
      (goto (fun _ => .copyGeomNumerator .scan))
  | .copyGeomNumerator l => BitMachineStackEmbedding.stmt copyGeomNumeratorSlots
      Label.copyGeomNumerator State.copy getCopy (some .initDivideGeom)
      (BitMachineCopy.program l)
  | .initDivideGeom => load (fun _ => .division false)
      (goto (fun _ => .divideGeom .start))
  | .divideGeom l => BitMachineStackEmbedding.stmt divideGeomSlots Label.divideGeom
      State.division getDivision (some .clearGeomRemainder) (MatrixUnaryDivision.program l)
  | .clearGeomRemainder => pop 14 (fun _ b => .copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => .clearGeomRemainder))
        (goto (fun _ => .initMultiplyWord)))
  | .initMultiplyWord => load (fun _ => .address false)
      (goto (fun _ => .multiplyWord .outer))
  | .multiplyWord l => BitMachineStackEmbedding.stmt multiplyWordSlots Label.multiplyWord
      State.address getAddress (some (.multiplyTail .outer)) (MatrixAddressMachine.program l)
  | .multiplyTail l => BitMachineStackEmbedding.stmt multiplyTailSlots Label.multiplyTail
      State.address getAddress (some .initClear) (MatrixAddressMachine.program l)
  | .initClear => load (fun _ => .copy none) (goto (fun _ => .clear 0))
  | .clear i => if h : i.val < 17 then
      pop (⟨i.val + 6, by omega⟩ : Stack) (fun _ b => .copy b)
        (branch (fun v => (getCopy v).isSome)
          (goto (fun _ => Label.clear i))
          (goto (fun _ => Label.clear ⟨i.val + 1, by omega⟩)))
    else load (fun _ => State.idle) (goto (fun _ => Label.done))
  | .done => halt

def start : Label := .copyWordInput .scan
def initial : State := .copy none
def cfg (l : Option Label) (v : State) (bank : Stack → List Bool) : Config := ⟨l,v,bank⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem copy_stage (slots : Fin 3 ↪ Stack)
    (label : BitMachineCopy.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.copy getCopy (some next)
        (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : Stack) (n : ℕ)
    (hslots : slots 0 = source ∧ slots 1 = target)
    (hs : S source = List.replicate n true)
    (ht : S target = []) (hw : S (slots 2) = []) :
    ∃ t ≤ 2*n+2,
      run t (cfg (some (label .scan)) (.copy none) S) =
        cfg (some next) (.copy none)
          (Function.update S target (List.replicate n true)) := by
  let c := BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] []
  have hrun := BitMachineCopy.run_correct none (List.replicate n true) []
  simp only [List.length_replicate, List.append_nil] at hrun
  have hhalt : (((advance BitMachineCopy.program)^[2*n+2]) c).l = none := by
    change (BitMachineCopy.run (2*n+2) c).l = none
    rw [hrun]
    rfl
  obtain ⟨t, ht', he⟩ := BitMachineStackEmbedding.outputs slots S label
    State.copy getCopy (fun _ => rfl) (some next)
    BitMachineCopy.program program hprogram c (2*n+2) hhalt
  change _ = BitMachineStackEmbedding.cfg slots S label State.copy (some next)
    (BitMachineCopy.run (2*n+2) c) at he
  rw [hrun] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, BitMachineCopy.cfg, BitMachineCopy.stackContents,
      hslots.1, hslots.2, hs, ht, hw]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []).stk =
      Function.update S target (List.replicate n true) := by
    have hu : (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []).stk =
        Function.update c.stk 1 (List.replicate n true) := by
      funext i
      fin_cases i <;> rfl
    rw [hu, BitMachineStackEmbedding.bank_update, hslots.2, hinit]
  exact ⟨t, ht', by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

theorem division_stage (slots : Fin 6 ↪ Stack)
    (label : MatrixUnaryDivision.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.division getDivision (some next)
        (MatrixUnaryDivision.program l))
    (S : Stack → List Bool) (n m : ℕ)
    (h0 : S (slots 0) = List.replicate n true)
    (h1 : S (slots 1) = List.replicate m true)
    (h2 : S (slots 2) = []) (h3 : S (slots 3) = [])
    (h4 : S (slots 4) = []) (h5 : S (slots 5) = []) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n m,
      run t (cfg (some (label .start)) (.division false) S) =
        cfg (some next) (.division false)
          (Function.update
            (Function.update (Function.update S (slots 0) []) (slots 3)
              (List.replicate (n % m) true))
            (slots 4) (List.replicate (n / m) true)) := by
  let c := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate n true) (List.replicate m true) [] [] [] []
  have hrun := MatrixUnaryDivision.division_total_run n m
  have hhalt : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m])
      c).l = none := by
    change (MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime n m) c).l = none
    rw [hrun]
    rfl
  obtain ⟨t, ht', he⟩ := BitMachineStackEmbedding.outputs slots S label
    State.division getDivision (fun _ => rfl) (some next)
    MatrixUnaryDivision.program program hprogram c
    (MatrixUnaryDivision.totalTime n m) hhalt
  change _ = BitMachineStackEmbedding.cfg slots S label State.division (some next)
    (MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime n m) c) at he
  rw [hrun] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, MatrixUnaryDivision.cfg, h0, h1, h2, h3, h4, h5]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n%m) true) (List.replicate (n/m) true) []).stk =
      Function.update
        (Function.update (Function.update S (slots 0) []) (slots 3)
          (List.replicate (n%m) true))
        (slots 4) (List.replicate (n/m) true) := by
    have hu : (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n%m) true) (List.replicate (n/m) true) []).stk =
        Function.update
          (Function.update (Function.update c.stk 0 []) 3
            (List.replicate (n%m) true)) 4 (List.replicate (n/m) true) := by
      funext i
      fin_cases i <;> rfl
    rw [hu, BitMachineStackEmbedding.bank_update,
      BitMachineStackEmbedding.bank_update,
      BitMachineStackEmbedding.bank_update, hinit]
  exact ⟨t, ht', by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

theorem power_stage (slots : MatrixWeightedPower.Stack ↪ Stack)
    (label : MatrixWeightedPower.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.power getPower (some next)
        (MatrixWeightedPower.program l))
    (S : Stack → List Bool) (base exponent : ℕ)
    (hacc : S (slots (.inl 0)) = [true])
    (hbase : S (slots (.inl 1)) = List.replicate base true)
    (h2 : S (slots (.inl 2)) = []) (h3 : S (slots (.inl 3)) = [])
    (h4 : S (slots (.inl 4)) = []) (h5 : S (slots (.inl 5)) = [])
    (hfuel : S (slots (.inr 0)) = List.replicate exponent true) :
    ∃ t ≤ MatrixWeightedPower.powerBound base exponent,
      run t (cfg (some (label (.inr .test))) (.power (false,false)) S) =
        cfg (some next) (.power (false,false))
          (Function.update (Function.update S (slots (.inl 0))
            (List.replicate (base ^ exponent) true)) (slots (.inr 0)) []) := by
  let c := MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
    [true] (List.replicate base true) [] (List.replicate exponent true)
  have hrun := MatrixWeightedPower.power_run base exponent
  obtain ⟨k,hk,hr⟩ := hrun
  have hhalt : (((advance MatrixWeightedPower.program)^[k]) c).l = none := by
    change (MatrixWeightedPower.run k c).l = none
    simpa [c] using congrArg (fun x : MatrixWeightedPower.Config => x.l) hr
  obtain ⟨t, ht', he⟩ := BitMachineStackEmbedding.outputs slots S label
    State.power getPower (fun _ => rfl) (some next)
    MatrixWeightedPower.program program hprogram c k hhalt
  change _ = BitMachineStackEmbedding.cfg slots S label State.power (some next)
    (MatrixWeightedPower.run k c) at he
  change MatrixWeightedPower.run k
    (MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
      (List.replicate 1 true) (List.replicate base true) []
      (List.replicate exponent true)) = _ at hr
  change _ = BitMachineStackEmbedding.cfg slots S label State.power (some next)
    (MatrixWeightedPower.run k
      (MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
        (List.replicate 1 true) (List.replicate base true) []
        (List.replicate exponent true))) at he
  rw [hr] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    rcases i with i | i
    · fin_cases i <;> simp [c, MatrixWeightedPower.cfg,
        MatrixWeightedPower.bank, hacc, hbase, h2, h3, h4, h5]
    · fin_cases i <;> simp [c, MatrixWeightedPower.cfg, hfuel]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (MatrixWeightedPower.cfg none (false,false)
        (List.replicate (base^exponent) true)
        (List.replicate base true) [] []).stk =
      Function.update (Function.update S (slots (.inl 0))
        (List.replicate (base^exponent) true)) (slots (.inr 0)) [] := by
    have hu : (MatrixWeightedPower.cfg none (false,false)
        (List.replicate (base^exponent) true)
        (List.replicate base true) [] []).stk =
        Function.update (Function.update c.stk (.inl 0)
          (List.replicate (base^exponent) true)) (.inr 0) [] := by
      funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    rw [hu, BitMachineStackEmbedding.bank_update,
      BitMachineStackEmbedding.bank_update, hinit]
  exact ⟨t, ht'.trans hk, by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

theorem cut_stage (slots : Fin 4 ↪ Stack)
    (label : MatrixUnaryCut.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.cut getCut (some next)
        (MatrixUnaryCut.program l))
    (S : Stack → List Bool) (x threshold : ℕ)
    (hx : S (slots 0) = List.replicate x true)
    (hthreshold : S (slots 1) = List.replicate threshold true)
    (h2 : S (slots 2) = []) (h3 : S (slots 3) = []) :
    ∃ t ≤ 3 * min x threshold + 4,
      run t (cfg (some (label .scan)) (.cut (false,true)) S) =
        cfg (some next) (.cut (decide (threshold ≤ x),false))
          (Function.update S (slots 0)
            (List.replicate (if x < threshold then x else x-threshold) true)) := by
  let c := MatrixUnaryCut.cfg (some .scan) (false,true)
    (List.replicate x true) (List.replicate threshold true) [] []
  obtain ⟨k,hk,hr⟩ := MatrixUnaryCut.cut_run x threshold
  have hhalt : (((advance MatrixUnaryCut.program)^[k]) c).l = none := by
    change (MatrixUnaryCut.run k c).l = none
    simpa [c] using congrArg (fun x : MatrixUnaryCut.Config => x.l) hr
  obtain ⟨t,ht',he⟩ := BitMachineStackEmbedding.outputs slots S label
    State.cut getCut (fun _ => rfl) (some next)
    MatrixUnaryCut.program program hprogram c k hhalt
  change _ = BitMachineStackEmbedding.cfg slots S label State.cut (some next)
    (MatrixUnaryCut.run k c) at he
  change _ = BitMachineStackEmbedding.cfg slots S label State.cut (some next)
    (MatrixUnaryCut.run k (MatrixUnaryCut.cfg (some .scan) (false,true)
      (List.replicate x true) (List.replicate threshold true) [] [])) at he
  rw [hr] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, MatrixUnaryCut.cfg, hx, hthreshold, h2, h3]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (MatrixUnaryCut.cfg none (decide (threshold ≤ x),false)
        (List.replicate (if x < threshold then x else x-threshold) true)
        (List.replicate threshold true) [] []).stk =
      Function.update S (slots 0)
        (List.replicate (if x < threshold then x else x-threshold) true) := by
    have hu : (MatrixUnaryCut.cfg none (decide (threshold ≤ x),false)
        (List.replicate (if x < threshold then x else x-threshold) true)
        (List.replicate threshold true) [] []).stk =
        Function.update c.stk 0
          (List.replicate (if x < threshold then x else x-threshold) true) := by
      funext i
      fin_cases i <;> rfl
    rw [hu, BitMachineStackEmbedding.bank_update, hinit]
  exact ⟨t,ht'.trans hk, by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

theorem address_stage (slots : Fin 6 ↪ Stack)
    (label : MatrixAddressMachine.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.address getAddress (some next)
        (MatrixAddressMachine.program l))
    (S : Stack → List Bool) (row width column : ℕ)
    (h0 : S (slots 0) = List.replicate row true)
    (h1 : S (slots 1) = List.replicate width true)
    (h2 : S (slots 2) = List.replicate column true)
    (h3 : S (slots 3) = []) (h4 : S (slots 4) = [])
    (h5 : S (slots 5) = []) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width column,
      run t (cfg (some (label .outer)) (.address false) S) =
        cfg (some next) (.address false)
          (Function.update S (slots 5) (List.replicate (row*width+column) true)) := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] [] []
  have hr := MatrixAddressMachine.address_run row width column false []
  simp only [List.append_nil] at hr
  have hh : (((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime row width column])
      c).l = none := by
    change (MatrixAddressMachine.run _ c).l = none
    rw [hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs slots S label
    State.address getAddress (fun _ => rfl) (some next)
    MatrixAddressMachine.program program hprogram c
    (MatrixAddressMachine.exactTime row width column) hh
  change _ = BitMachineStackEmbedding.cfg slots S label State.address (some next)
    (MatrixAddressMachine.run (MatrixAddressMachine.exactTime row width column) c) at he
  rw [hr] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [c, MatrixAddressMachine.cfg, h0, h1, h2, h3, h4, h5]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (MatrixAddressMachine.cfg none false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate (row*width+column) true)).stk =
      Function.update S (slots 5) (List.replicate (row*width+column) true) := by
    have hu : (MatrixAddressMachine.cfg none false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate (row*width+column) true)).stk =
        Function.update c.stk 5 (List.replicate (row*width+column) true) := by
      funext i
      fin_cases i <;> rfl
    rw [hu, BitMachineStackEmbedding.bank_update, hinit]
  exact ⟨t,ht, by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

def unary (W : Stack → ℕ) : Stack → List Bool :=
  fun i => List.replicate (W i) true

@[simp] theorem unary_apply (W : Stack → ℕ) (i : Stack) :
    unary W i = List.replicate (W i) true := rfl

theorem unary_update (W : Stack → ℕ) (i : Stack) (n : ℕ) :
    Function.update (unary W) i (List.replicate n true) =
      unary (Function.update W i n) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [unary]
  · simp [unary, Function.update_of_ne h]

theorem copy_words (slots : Fin 3 ↪ Stack)
    (label : BitMachineCopy.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.copy getCopy (some next)
        (BitMachineCopy.program l))
    (W : Stack → ℕ) (source target : Stack)
    (hslots : slots 0 = source ∧ slots 1 = target)
    (ht : W target = 0) (hw : W (slots 2) = 0) :
    ∃ t ≤ 2*W source+2,
      run t (cfg (some (label .scan)) (.copy none) (unary W)) =
        cfg (some next) (.copy none) (unary (Function.update W target (W source))) := by
  have h := copy_stage slots label next hprogram (unary W)
    source target (W source) hslots rfl (by simpa [unary, ht]) (by simpa [unary, hw])
  simpa only [unary_update] using h

theorem division_words (slots : Fin 6 ↪ Stack)
    (label : MatrixUnaryDivision.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.division getDivision (some next)
        (MatrixUnaryDivision.program l))
    (W : Stack → ℕ)
    (h2 : W (slots 2) = 0) (h3 : W (slots 3) = 0)
    (h4 : W (slots 4) = 0) (h5 : W (slots 5) = 0) :
    ∃ t ≤ MatrixUnaryDivision.totalTime (W (slots 0)) (W (slots 1)),
      run t (cfg (some (label .start)) (.division false) (unary W)) =
        cfg (some next) (.division false)
          (unary (Function.update
            (Function.update (Function.update W (slots 0) 0) (slots 3)
              (W (slots 0) % W (slots 1)))
            (slots 4) (W (slots 0) / W (slots 1)))) := by
  have h := division_stage slots label next hprogram (unary W)
    (W (slots 0)) (W (slots 1)) rfl rfl
    (by simpa [unary, h2]) (by simpa [unary, h3])
    (by simpa [unary, h4]) (by simpa [unary, h5])
  simpa only [show ([] : List Bool) = List.replicate 0 true from rfl,
    unary_update] using h

theorem power_words (slots : MatrixWeightedPower.Stack ↪ Stack)
    (label : MatrixWeightedPower.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.power getPower (some next)
        (MatrixWeightedPower.program l))
    (W : Stack → ℕ)
    (hacc : W (slots (.inl 0)) = 1)
    (h2 : W (slots (.inl 2)) = 0) (h3 : W (slots (.inl 3)) = 0)
    (h4 : W (slots (.inl 4)) = 0) (h5 : W (slots (.inl 5)) = 0) :
    ∃ t ≤ MatrixWeightedPower.powerBound
      (W (slots (.inl 1))) (W (slots (.inr 0))),
      run t (cfg (some (label (.inr .test))) (.power (false,false)) (unary W)) =
        cfg (some next) (.power (false,false))
          (unary (Function.update
            (Function.update W (slots (.inl 0))
              ((W (slots (.inl 1))) ^ (W (slots (.inr 0)))))
            (slots (.inr 0)) 0)) := by
  have h := power_stage slots label next hprogram (unary W)
    (W (slots (.inl 1))) (W (slots (.inr 0)))
    (by simpa [unary, hacc]) rfl
    (by simpa [unary, h2]) (by simpa [unary, h3])
    (by simpa [unary, h4]) (by simpa [unary, h5]) rfl
  simpa only [show ([] : List Bool) = List.replicate 0 true from rfl,
    unary_update] using h

theorem cut_words (slots : Fin 4 ↪ Stack)
    (label : MatrixUnaryCut.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.cut getCut (some next)
        (MatrixUnaryCut.program l))
    (W : Stack → ℕ) (h2 : W (slots 2) = 0) (h3 : W (slots 3) = 0) :
    ∃ t ≤ 3 * min (W (slots 0)) (W (slots 1)) + 4,
      run t (cfg (some (label .scan)) (.cut (false,true)) (unary W)) =
        cfg (some next) (.cut (decide (W (slots 1) ≤ W (slots 0)),false))
          (unary (Function.update W (slots 0)
            (if W (slots 0) < W (slots 1) then W (slots 0)
             else W (slots 0) - W (slots 1)))) := by
  have h := cut_stage slots label next hprogram (unary W)
    (W (slots 0)) (W (slots 1)) rfl rfl
    (by simpa [unary, h2]) (by simpa [unary, h3])
  simpa only [unary_update] using h

theorem address_words (slots : Fin 6 ↪ Stack)
    (label : MatrixAddressMachine.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      BitMachineStackEmbedding.stmt slots label State.address getAddress (some next)
        (MatrixAddressMachine.program l))
    (W : Stack → ℕ)
    (h3 : W (slots 3) = 0) (h4 : W (slots 4) = 0)
    (h5 : W (slots 5) = 0) :
    ∃ t ≤ MatrixAddressMachine.exactTime (W (slots 0)) (W (slots 1)) (W (slots 2)),
      run t (cfg (some (label .outer)) (.address false) (unary W)) =
        cfg (some next) (.address false)
          (unary (Function.update W (slots 5)
            (W (slots 0) * W (slots 1) + W (slots 2)))) := by
  have h := address_stage slots label next hprogram (unary W)
    (W (slots 0)) (W (slots 1)) (W (slots 2)) rfl rfl rfl
    (by simpa [unary, h3]) (by simpa [unary, h4]) (by simpa [unary, h5])
  simpa only [unary_update] using h

def inputWords (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  ![d,wordBase,cy,s,binBase,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem copy_word_input (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ 2*d+2,
      run t (cfg (some start) initial (unary (inputWords d wordBase cy s binBase))) =
        cfg (some .initDivideWord) (.copy none)
          (unary (Function.update (inputWords d wordBase cy s binBase) 13 d)) := by
  have h := copy_stage copyWordInputSlots Label.copyWordInput Label.initDivideWord
    (by intro l; rfl) (unary (inputWords d wordBase cy s binBase))
    0 13 d (by decide) (by rfl) (by rfl) (by rfl)
  simpa only [start, initial, unary_update] using h

def afterWordDivision (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  Function.update
    (Function.update
      (Function.update (Function.update (inputWords d wordBase cy s binBase) 13 d)
        13 0) 15 (d % wordBase)) 14 (d / wordBase)

theorem word_division_run (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ 1 + MatrixUnaryDivision.totalTime d wordBase,
      run t (cfg (some .initDivideWord) (.copy none)
        (unary (Function.update (inputWords d wordBase cy s binBase) 13 d))) =
      cfg (some .clearWordQuotient) (.division false)
        (unary (afterWordDivision d wordBase cy s binBase)) := by
  let W := Function.update (inputWords d wordBase cy s binBase) 13 d
  have hinit : run 1 (cfg (some .initDivideWord) (.copy none) (unary W)) =
      cfg (some (.divideWord .start)) (.division false) (unary W) := rfl
  have h := division_words divideWordSlots Label.divideWord Label.clearWordQuotient
    (by intro l; rfl) W
    (by simp [W, inputWords, divideWordSlots])
    (by simp [W, inputWords, divideWordSlots])
    (by simp [W, inputWords, divideWordSlots])
    (by simp [W, inputWords, divideWordSlots])
  obtain ⟨t,ht,hr⟩ := h
  refine ⟨1+t, by simpa [W, divideWordSlots, inputWords] using Nat.add_le_add_left ht 1,
    ?_⟩
  rw [run_add hinit]
  simpa [W, afterWordDivision, divideWordSlots, inputWords] using hr

theorem clear_step_cons (label next : Label) (slot : Stack)
    (hprogram : program label = pop slot (fun _ b => State.copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => label)) (goto (fun _ => next))))
    (S : Stack → List Bool) (b : Bool) (tail : List Bool) (v : State)
    (hslot : S slot = b :: tail) :
    advance program (cfg (some label) v S) =
      cfg (some label) (.copy (some b)) (Function.update S slot tail) := by
  simp [advance, TM2.step, TM2.stepAux, hprogram, cfg, hslot,
    getCopy, Function.update]

theorem clear_step_nil (label next : Label) (slot : Stack)
    (hprogram : program label = pop slot (fun _ b => State.copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => label)) (goto (fun _ => next))))
    (S : Stack → List Bool) (v : State) (hslot : S slot = []) :
    advance program (cfg (some label) v S) =
      cfg (some next) (.copy none) S := by
  simp [advance, TM2.step, TM2.stepAux, hprogram, cfg, hslot, getCopy,
    Function.update_eq_self_iff]

theorem clear_stack_run (label next : Label) (slot : Stack)
    (hprogram : program label = pop slot (fun _ b => State.copy b)
      (branch (fun v => (getCopy v).isSome)
        (goto (fun _ => label)) (goto (fun _ => next))))
    (S : Stack → List Bool) (bits : List Bool) (v : State)
    (hslot : S slot = bits) :
    run (bits.length + 1) (cfg (some label) v S) =
      cfg (some next) (.copy none) (Function.update S slot []) := by
  induction bits generalizing S v with
  | nil =>
      have hs := clear_step_nil label next slot hprogram S v hslot
      have hu : Function.update S slot [] = S := by
        funext i
        by_cases hi : i = slot
        · subst i; simp [hslot]
        · simp [Function.update_of_ne hi]
      simpa only [List.length_nil, Nat.zero_add, run,
        Function.iterate_one, hu] using hs
  | cons b tail ih =>
      have hs := clear_step_cons label next slot hprogram S b tail v hslot
      have ht : (Function.update S slot tail) slot = tail := by simp
      have hh := ih (Function.update S slot tail) (.copy (some b)) ht
      have hu : Function.update (Function.update S slot tail) slot [] =
          Function.update S slot [] := by simp
      simpa only [List.length_cons, hu, show 1 + (tail.length + 1) =
        tail.length + 1 + 1 by omega] using
        (run_add (show run 1 (cfg (some label) v S) = _ by simpa [run] using hs)
          (tail.length+1)).trans hh

def word (d wordBase : ℕ) : ℕ := d % wordBase
def tailPowerValue (cy s : ℕ) : ℕ := cy ^ (s+1)
def tail (d wordBase cy s : ℕ) : ℕ := word d wordBase % tailPowerValue cy s

def tailWords (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  ![d,wordBase,cy,s,binBase,0,0,0,0,0,0,0,0,0,0,
    word d wordBase,tail d wordBase cy s,0,0,0,0,0,0]

def tailBound (d wordBase cy s : ℕ) : ℕ :=
  (2*d+2) + (1+MatrixUnaryDivision.totalTime d wordBase) +
  (d/wordBase+1) + (2*s+2) + 2 + MatrixWeightedPower.powerBound cy (s+1) +
  1 + (2*word d wordBase+2) + 1 +
  MatrixUnaryDivision.totalTime (word d wordBase) (tailPowerValue cy s) +
  (word d wordBase/tailPowerValue cy s+1) + (tailPowerValue cy s+1)

theorem tail_run (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ tailBound d wordBase cy s,
      run t (cfg (some start) initial (unary (inputWords d wordBase cy s binBase))) =
      cfg (some (.copyBinExponent .scan)) (.copy none)
        (unary (tailWords d wordBase cy s binBase)) := by
  let W0 := inputWords d wordBase cy s binBase
  let W1 := Function.update W0 13 d
  let W2 := afterWordDivision d wordBase cy s binBase
  let W3 := Function.update W2 14 0
  let W4 := Function.update W3 6 s
  let W5 := Function.update W4 6 (s+1)
  let W6 := Function.update W5 8 1
  let W7 := Function.update (Function.update W6 8 (tailPowerValue cy s)) 6 0
  let W8 := Function.update W7 13 (word d wordBase)
  let W9 := Function.update
    (Function.update (Function.update W8 13 0) 16 (tail d wordBase cy s))
    14 (word d wordBase / tailPowerValue cy s)
  let W10 := Function.update W9 14 0
  let W11 := Function.update W10 8 0
  obtain ⟨t0,h0,e0⟩ := copy_word_input d wordBase cy s binBase
  obtain ⟨t1,h1,e1⟩ := word_division_run d wordBase cy s binBase
  have e1' : run t1 (cfg (some .initDivideWord) (.copy none) (unary W1)) =
      cfg (some .clearWordQuotient) (.division false) (unary W2) := by
    simpa [W1,W0,W2] using e1
  have hc0 := clear_stack_run .clearWordQuotient (.copyTailExponent .scan) 14
    (by rfl) (unary W2) (List.replicate (d/wordBase) true) (.division false)
    (by simp [W2,afterWordDivision,inputWords])
  have hc0' : run (d/wordBase+1)
      (cfg (some .clearWordQuotient) (.division false) (unary W2)) =
      cfg (some (.copyTailExponent .scan)) (.copy none) (unary W3) := by
    simpa only [List.length_replicate, W3,
      show ([] : List Bool) = List.replicate 0 true from rfl,
      unary_update] using hc0
  obtain ⟨t2,h2,e2⟩ := copy_words copyTailExponentSlots
    Label.copyTailExponent Label.tailExponentSuccessor (by intro l; rfl)
    W3 3 6 (by decide)
    (by rfl) (by rfl)
  have e2' : run t2 (cfg (some (.copyTailExponent .scan)) (.copy none) (unary W3)) =
      cfg (some .tailExponentSuccessor) (.copy none) (unary W4) := by
    exact e2
  have ea : run 2 (cfg (some .tailExponentSuccessor) (.copy none) (unary W4)) =
      cfg (some (.tailPower (.inr .test))) (.power (false,false)) (unary W6) := by
    simp [run, advance, TM2.step, TM2.stepAux, program, cfg,
      W6,W5,W4,unary]
    funext i
    fin_cases i <;> simp [W6,W5,W4,W3,W2,afterWordDivision,
      inputWords,unary,List.replicate_succ,Function.update]
  obtain ⟨t3,h3,e3⟩ := power_words tailPowerSlots Label.tailPower
    Label.initCopyTailInput (by intro l; rfl) W6
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have e3' : run t3 (cfg (some (.tailPower (.inr .test))) (.power (false,false))
      (unary W6)) = cfg (some .initCopyTailInput) (.power (false,false))
      (unary W7) := by
    exact e3
  have ei : run 1 (cfg (some .initCopyTailInput) (.power (false,false))
      (unary W7)) = cfg (some (.copyTailInput .scan)) (.copy none) (unary W7) := rfl
  obtain ⟨t4,h4,e4⟩ := copy_words copyTailInputSlots
    Label.copyTailInput Label.initDivideTail (by intro l; rfl)
    W7 15 13 (by decide)
    (by rfl) (by rfl)
  have e4' : run t4 (cfg (some (.copyTailInput .scan)) (.copy none) (unary W7)) =
      cfg (some .initDivideTail) (.copy none) (unary W8) := by
    exact e4
  have ei2 : run 1 (cfg (some .initDivideTail) (.copy none) (unary W8)) =
      cfg (some (.divideTail .start)) (.division false) (unary W8) := rfl
  obtain ⟨t5,h5,e5⟩ := division_words divideTailSlots Label.divideTail
    Label.clearTailQuotient (by intro l; rfl) W8
    (by rfl) (by rfl) (by rfl) (by rfl)
  have e5' : run t5 (cfg (some (.divideTail .start)) (.division false) (unary W8)) =
      cfg (some .clearTailQuotient) (.division false) (unary W9) := by
    exact e5
  have hc1 := clear_stack_run .clearTailQuotient .clearTailPower 14
    (by rfl) (unary W9)
    (List.replicate (word d wordBase / tailPowerValue cy s) true)
    (.division false)
    (by simp [W9,W8,W7,W6,W5,W4,W3,W2,afterWordDivision,inputWords,
      word,tailPowerValue])
  have hc1' : run (word d wordBase / tailPowerValue cy s + 1)
      (cfg (some .clearTailQuotient) (.division false) (unary W9)) =
      cfg (some .clearTailPower) (.copy none) (unary W10) := by
    simpa only [List.length_replicate, W10,
      show ([] : List Bool) = List.replicate 0 true from rfl,
      unary_update] using hc1
  have hc2 := clear_stack_run .clearTailPower (.copyBinExponent .scan) 8
    (by rfl) (unary W10) (List.replicate (tailPowerValue cy s) true)
    (.copy none)
    (by simp [W10,W9,W8,W7,W6,W5,W4,W3,W2,afterWordDivision,inputWords,
      tailPowerValue])
  have hc2' : run (tailPowerValue cy s+1)
      (cfg (some .clearTailPower) (.copy none) (unary W10)) =
      cfg (some (.copyBinExponent .scan)) (.copy none) (unary W11) := by
    simpa only [List.length_replicate, W11,
      show ([] : List Bool) = List.replicate 0 true from rfl,
      unary_update] using hc2
  let T := t0 + t1 + (d/wordBase+1) + t2 + 2 + t3 + 1 + t4 + 1 + t5 +
    (word d wordBase / tailPowerValue cy s+1) + (tailPowerValue cy s+1)
  refine ⟨T, ?_, ?_⟩
  · dsimp [T,tailBound]
    have h2' : t2 ≤ 2*s+2 := by
      simpa [W3,W2,afterWordDivision,inputWords] using h2
    have h3' : t3 ≤ MatrixWeightedPower.powerBound cy (s+1) := by
      simpa [W6,W5,W4,W3,W2,afterWordDivision,inputWords] using h3
    have h4' : t4 ≤ 2*word d wordBase+2 := by
      simpa [W7,W6,W5,W4,W3,W2,afterWordDivision,inputWords,word] using h4
    have h5' : t5 ≤ MatrixUnaryDivision.totalTime
        (word d wordBase) (tailPowerValue cy s) := by
      simpa [W8,W7,W6,W5,W4,W3,W2,afterWordDivision,inputWords,
        word,tailPowerValue] using h5
    omega
  · have c01 := (run_add e0 t1).trans e1'
    have c02 := (run_add c01 (d/wordBase+1)).trans hc0'
    have c03 := (run_add c02 t2).trans e2'
    have c04 := (run_add c03 2).trans ea
    have c05 := (run_add c04 t3).trans e3'
    have c06 := (run_add c05 1).trans ei
    have c07 := (run_add c06 t4).trans e4'
    have c08 := (run_add c07 1).trans ei2
    have c09 := (run_add c08 t5).trans e5'
    have c10 := (run_add c09 (word d wordBase / tailPowerValue cy s+1)).trans hc1'
    have c11 := (run_add c10 (tailPowerValue cy s+1)).trans hc2'
    have hW : W11 = tailWords d wordBase cy s binBase := by
      funext i
      fin_cases i <;> simp [W11,W10,W9,W8,W7,W6,W5,W4,W3,W2,W1,W0,
        afterWordDivision,inputWords,tailWords,tail,word,tailPowerValue]
    simpa only [T, hW] using c11

def binPowerValue (binBase s : ℕ) : ℕ := binBase ^ s
def geom (binBase s : ℕ) : ℕ :=
  (binPowerValue binBase s - 1) / (binBase - 1)

def geomWords (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  ![d,wordBase,cy,s,binBase,0,0,0,binPowerValue binBase s,
    0,0,0,0,0,0,word d wordBase,tail d wordBase cy s,
    binPowerValue binBase s-1,1,0,0,binBase-1,geom binBase s]

def geomBound (binBase s : ℕ) : ℕ :=
  (2*s+2) + 1 + MatrixWeightedPower.powerBound binBase s +
  1 + (2*binPowerValue binBase s+2) + 1 +
  (3*min (binPowerValue binBase s) 1+4) + 1 +
  (2*binBase+2) + 1 + (3*min binBase 1+4) + 1 +
  (2*(binPowerValue binBase s-1)+2) + 1 +
  MatrixUnaryDivision.totalTime (binPowerValue binBase s-1) (binBase-1) +
  1 +
  ((binPowerValue binBase s-1)%(binBase-1)+1)

theorem predecessor_by_one (x : ℕ) :
    (if x < 1 then x else x-1) = x-1 := by
  split_ifs <;> omega

theorem geom_run (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ geomBound binBase s,
      run t (cfg (some (.copyBinExponent .scan)) (.copy none)
        (unary (tailWords d wordBase cy s binBase))) =
      cfg (some (.multiplyWord .outer)) (.address false)
        (unary (geomWords d wordBase cy s binBase)) := by
  let W0 := tailWords d wordBase cy s binBase
  let W1 := Function.update W0 6 s
  let W2 := Function.update W1 8 1
  let W3 := Function.update (Function.update W2 8 (binPowerValue binBase s)) 6 0
  let W4 := Function.update W3 17 (binPowerValue binBase s)
  let W5 := Function.update W4 18 1
  let W6 := Function.update W5 17 (binPowerValue binBase s-1)
  let W7 := Function.update W6 21 binBase
  let W8 := Function.update W7 21 (binBase-1)
  let W9 := Function.update W8 13 (binPowerValue binBase s-1)
  let W10 := Function.update
    (Function.update (Function.update W9 13 0) 14
      ((binPowerValue binBase s-1)%(binBase-1))) 22 (geom binBase s)
  let W11 := Function.update W10 14 0
  obtain ⟨t0,h0,e0⟩ := copy_words copyBinExponentSlots Label.copyBinExponent
    Label.binPowerOne (by intro l; rfl) W0 3 6 (by decide) (by rfl) (by rfl)
  have e0' : run t0 (cfg (some (.copyBinExponent .scan)) (.copy none) (unary W0)) =
      cfg (some .binPowerOne) (.copy none) (unary W1) := e0
  have ea : run 1 (cfg (some .binPowerOne) (.copy none) (unary W1)) =
      cfg (some (.binPower (.inr .test))) (.power (false,false)) (unary W2) := by
    simp [run,advance,TM2.step,TM2.stepAux,program,cfg,W2,W1,unary]
    funext i
    fin_cases i <;> simp [W2,W1,W0,tailWords,unary,List.replicate_succ]
  obtain ⟨t1,h1,e1⟩ := power_words binPowerSlots Label.binPower
    Label.initCopyPower (by intro l; rfl) W2
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have e1' : run t1 (cfg (some (.binPower (.inr .test))) (.power (false,false))
      (unary W2)) = cfg (some .initCopyPower) (.power (false,false))
      (unary W3) := e1
  have ei1 : run 1 (cfg (some .initCopyPower) (.power (false,false)) (unary W3)) =
      cfg (some (.copyPower .scan)) (.copy none) (unary W3) := rfl
  obtain ⟨t2,h2,e2⟩ := copy_words copyPowerSlots Label.copyPower Label.one
    (by intro l; rfl) W3 8 17 (by decide) (by rfl) (by rfl)
  have e2' : run t2 (cfg (some (.copyPower .scan)) (.copy none) (unary W3)) =
      cfg (some .one) (.copy none) (unary W4) := e2
  have ea2 : run 1 (cfg (some .one) (.copy none) (unary W4)) =
      cfg (some (.cutPower .scan)) (.cut (false,true)) (unary W5) := by
    simp [run,advance,TM2.step,TM2.stepAux,program,cfg,W5,W4,unary]
    funext i
    fin_cases i <;> simp [W5,W4,W3,W2,W1,W0,tailWords,unary,List.replicate_succ]
  obtain ⟨t3,h3,e3⟩ := cut_words cutPowerSlots Label.cutPower Label.initCopyBase
    (by intro l; rfl) W5 (by rfl) (by rfl)
  have e3' : run t3 (cfg (some (.cutPower .scan)) (.cut (false,true)) (unary W5)) =
      cfg (some .initCopyBase)
        (.cut (decide (1 ≤ binPowerValue binBase s),false)) (unary W6) := by
    simpa only [show cutPowerSlots 0 = (17 : Stack) from rfl,
      show cutPowerSlots 1 = (18 : Stack) from rfl,
      show W5 17 = binPowerValue binBase s from rfl,
      show W5 18 = 1 from rfl, predecessor_by_one, W6] using e3
  have ei2 : run 1 (cfg (some .initCopyBase)
      (.cut (decide (1 ≤ binPowerValue binBase s),false)) (unary W6)) =
      cfg (some (.copyBase .scan)) (.copy none) (unary W6) := rfl
  obtain ⟨t4,h4,e4⟩ := copy_words copyBaseSlots Label.copyBase Label.initCutBase
    (by intro l; rfl) W6 4 21 (by decide) (by rfl) (by rfl)
  have e4' : run t4 (cfg (some (.copyBase .scan)) (.copy none) (unary W6)) =
      cfg (some .initCutBase) (.copy none) (unary W7) := e4
  have ei3 : run 1 (cfg (some .initCutBase) (.copy none) (unary W7)) =
      cfg (some (.cutBase .scan)) (.cut (false,true)) (unary W7) := rfl
  obtain ⟨t5,h5,e5⟩ := cut_words cutBaseSlots Label.cutBase
    Label.initCopyGeomNumerator (by intro l; rfl) W7 (by rfl) (by rfl)
  have e5' : run t5 (cfg (some (.cutBase .scan)) (.cut (false,true)) (unary W7)) =
      cfg (some .initCopyGeomNumerator) (.cut (decide (1 ≤ binBase),false))
        (unary W8) := by
    simpa only [show cutBaseSlots 0 = (21 : Stack) from rfl,
      show cutBaseSlots 1 = (18 : Stack) from rfl,
      show W7 21 = binBase from rfl,
      show W7 18 = 1 from rfl, predecessor_by_one, W8] using e5
  have ei4 : run 1 (cfg (some .initCopyGeomNumerator)
      (.cut (decide (1 ≤ binBase),false)) (unary W8)) =
      cfg (some (.copyGeomNumerator .scan)) (.copy none) (unary W8) := rfl
  obtain ⟨t6,h6,e6⟩ := copy_words copyGeomNumeratorSlots
    Label.copyGeomNumerator Label.initDivideGeom (by intro l; rfl)
    W8 17 13 (by decide) (by rfl) (by rfl)
  have e6' : run t6 (cfg (some (.copyGeomNumerator .scan)) (.copy none)
      (unary W8)) = cfg (some .initDivideGeom) (.copy none) (unary W9) := e6
  have ei5 : run 1 (cfg (some .initDivideGeom) (.copy none) (unary W9)) =
      cfg (some (.divideGeom .start)) (.division false) (unary W9) := rfl
  obtain ⟨t7,h7,e7⟩ := division_words divideGeomSlots Label.divideGeom
    Label.clearGeomRemainder (by intro l; rfl) W9
    (by rfl) (by rfl) (by rfl) (by rfl)
  have e7' : run t7 (cfg (some (.divideGeom .start)) (.division false) (unary W9)) =
      cfg (some .clearGeomRemainder) (.division false) (unary W10) := e7
  have hc := clear_stack_run .clearGeomRemainder .initMultiplyWord 14
    (by rfl) (unary W10)
    (List.replicate ((binPowerValue binBase s-1)%(binBase-1)) true)
    (.division false) (by rfl)
  have hc' : run ((binPowerValue binBase s-1)%(binBase-1)+1)
      (cfg (some .clearGeomRemainder) (.division false) (unary W10)) =
      cfg (some .initMultiplyWord) (.copy none) (unary W11) := by
    simpa only [List.length_replicate,W11,
      show ([] : List Bool) = List.replicate 0 true from rfl,
      unary_update] using hc
  have ei6 : run 1 (cfg (some .initMultiplyWord) (.copy none) (unary W11)) =
      cfg (some (.multiplyWord .outer)) (.address false) (unary W11) := rfl
  let T := t0+1+t1+1+t2+1+t3+1+t4+1+t5+1+t6+1+t7+
    ((binPowerValue binBase s-1)%(binBase-1)+1)+1
  have hT : T ≤ geomBound binBase s := by
    dsimp [T,geomBound]
    have b0 : t0 ≤ 2*s+2 := by simpa [W0,tailWords] using h0
    have b1 : t1 ≤ MatrixWeightedPower.powerBound binBase s := by
      simpa [W2,W1,W0,tailWords] using h1
    have b2 : t2 ≤ 2*binPowerValue binBase s+2 := by
      simpa [W3,W2,W1,W0,tailWords] using h2
    have b3 : t3 ≤ 3*min (binPowerValue binBase s) 1+4 := by
      simpa [W5,W4,W3,W2,W1,W0,tailWords] using h3
    have b4 : t4 ≤ 2*binBase+2 := by
      simpa [W6,W5,W4,W3,W2,W1,W0,tailWords] using h4
    have b5 : t5 ≤ 3*min binBase 1+4 := by
      simpa [W7,W6,W5,W4,W3,W2,W1,W0,tailWords] using h5
    have b6 : t6 ≤ 2*(binPowerValue binBase s-1)+2 := by
      simpa [W8,W7,W6,W5,W4,W3,W2,W1,W0,tailWords] using h6
    have b7 : t7 ≤ MatrixUnaryDivision.totalTime
        (binPowerValue binBase s-1) (binBase-1) := by
      simpa [W9,W8,W7,W6,W5,W4,W3,W2,W1,W0,tailWords] using h7
    omega
  have c0 := (run_add e0' 1).trans ea
  have c1 := (run_add c0 t1).trans e1'
  have c2 := (run_add c1 1).trans ei1
  have c3 := (run_add c2 t2).trans e2'
  have c4 := (run_add c3 1).trans ea2
  have c5 := (run_add c4 t3).trans e3'
  have c6 := (run_add c5 1).trans ei2
  have c7 := (run_add c6 t4).trans e4'
  have c8 := (run_add c7 1).trans ei3
  have c9 := (run_add c8 t5).trans e5'
  have c10 := (run_add c9 1).trans ei4
  have c11 := (run_add c10 t6).trans e6'
  have c12 := (run_add c11 1).trans ei5
  have c13 := (run_add c12 t7).trans e7'
  have c14 := (run_add c13 ((binPowerValue binBase s-1)%(binBase-1)+1)).trans hc'
  have c15 := (run_add c14 1).trans ei6
  have hW : W11 = geomWords d wordBase cy s binBase := by
    funext i
    fin_cases i <;> simp [W11,W10,W9,W8,W7,W6,W5,W4,W3,W2,W1,W0,
      geomWords,tailWords,geom,binPowerValue]
  refine ⟨T,hT,?_⟩
  simpa only [T,hW,W0] using c15

def clearPrefix (W : Stack → ℕ) (n : ℕ) : Stack → ℕ :=
  fun i => if 6 ≤ i.val ∧ i.val < 6+n then 0 else W i

theorem clearPrefix_zero (W : Stack → ℕ) : clearPrefix W 0 = W := by
  funext i
  simp [clearPrefix]

theorem clearPrefix_slot (W : Stack → ℕ) (n : ℕ) (hn : n < 17) :
    clearPrefix W n ⟨n+6, by omega⟩ = W ⟨n+6, by omega⟩ := by
  simp [clearPrefix]
  omega

theorem clearPrefix_succ (W : Stack → ℕ) (n : ℕ) (hn : n < 17) :
    Function.update (clearPrefix W n) ⟨n+6, by omega⟩ 0 =
      clearPrefix W (n+1) := by
  funext i
  by_cases h : i = (⟨n+6, by omega⟩ : Stack)
  · subst i
    simp [clearPrefix]
    omega
  · have hv : i.val ≠ n+6 := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, clearPrefix]
    by_cases h0 : 6 ≤ i.val
    · by_cases h1 : i.val < 6+n
      · have h2 : i.val < 6+(n+1) := by omega
        simp [h0,h1,h2]
      · by_cases h2 : i.val < 6+(n+1)
        · omega
        · simp [h0,h1,h2]
    · simp [h0]

def slotNat (j : ℕ) : Stack :=
  if h : j < 17 then ⟨j+6, by omega⟩ else 6

def clearTime (W : Stack → ℕ) (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun j => W (slotNat j) + 1)

theorem clear_prefix_run (W : Stack → ℕ) (n : ℕ) (hn : n ≤ 17) :
    run (clearTime W n)
      (cfg (some (.clear 0)) (.copy none) (unary W)) =
      cfg (some (.clear ⟨n, by omega⟩)) (.copy none)
        (unary (clearPrefix W n)) := by
  induction n with
  | zero => simp [clearTime, run, clearPrefix_zero]
  | succ n ih =>
      have hlt : n < 17 := by omega
      have hn' : n ≤ 17 := by omega
      have hi := ih hn'
      have hprog : program (.clear ⟨n, by omega⟩) =
          pop (⟨n+6, by omega⟩ : Stack) (fun _ b => State.copy b)
            (branch (fun v => (getCopy v).isSome)
              (goto (fun _ => Label.clear ⟨n, by omega⟩))
              (goto (fun _ => Label.clear ⟨n+1, by omega⟩))) := by
        simp only [program, show n < 17 from hlt, dite_true]
      have hc := clear_stack_run (.clear ⟨n, by omega⟩)
        (.clear ⟨n+1, by omega⟩) (⟨n+6, by omega⟩ : Stack)
        hprog (unary (clearPrefix W n))
        (List.replicate (W ⟨n+6, by omega⟩) true) (.copy none)
        (by simp [clearPrefix_slot W n hlt])
      have hc' : run (W ⟨n+6, by omega⟩+1)
          (cfg (some (.clear ⟨n, by omega⟩)) (.copy none)
            (unary (clearPrefix W n))) =
          cfg (some (.clear ⟨n+1, by omega⟩)) (.copy none)
            (unary (clearPrefix W (n+1))) := by
        simpa only [List.length_replicate,
          show ([] : List Bool) = List.replicate 0 true from rfl,
          unary_update, clearPrefix_succ W n hlt] using hc
      have ht : clearTime W (n+1) =
          clearTime W n + (W ⟨n+6, by omega⟩+1) := by
        simp [clearTime, Finset.sum_range_succ, slotNat, hlt]
      rw [ht, run_add hi]
      exact hc'

def cleared (W : Stack → ℕ) : Stack → ℕ := clearPrefix W 17

theorem clear_all_run (W : Stack → ℕ) :
    run (clearTime W 17 + 2)
      (cfg (some (.clear 0)) (.copy none) (unary W)) =
      cfg none .idle (unary (cleared W)) := by
  have h := clear_prefix_run W 17 (by omega)
  have hlast : run 2 (cfg (some (.clear 17)) (.copy none)
      (unary (clearPrefix W 17))) =
      cfg none .idle (unary (clearPrefix W 17)) := by
    rfl
  exact (run_add h 2).trans hlast

def rawValue (d wordBase cy s binBase : ℕ) : ℕ :=
  tail d wordBase cy s * binPowerValue binBase s +
    d * geom binBase s

def outputWords (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  ![d,wordBase,cy,s,binBase,rawValue d wordBase cy s binBase,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def preclearWords (d wordBase cy s binBase : ℕ) : Stack → ℕ :=
  Function.update
    (Function.update (geomWords d wordBase cy s binBase) 14
      (d * geom binBase s)) 5
    (rawValue d wordBase cy s binBase)

def finalBound (d wordBase cy s binBase : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime d (geom binBase s) 0 +
  MatrixAddressMachine.exactTime (tail d wordBase cy s)
    (binPowerValue binBase s) (d * geom binBase s) +
  1 + clearTime (preclearWords d wordBase cy s binBase) 17 + 2

theorem final_address_run (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ finalBound d wordBase cy s binBase,
      run t (cfg (some (.multiplyWord .outer)) (.address false)
        (unary (geomWords d wordBase cy s binBase))) =
      cfg none .idle (unary (outputWords d wordBase cy s binBase)) := by
  let W0 := geomWords d wordBase cy s binBase
  let W1 := Function.update W0 14 (d * geom binBase s)
  let W2 := preclearWords d wordBase cy s binBase
  obtain ⟨t0,h0,e0⟩ := address_words multiplyWordSlots Label.multiplyWord
    (.multiplyTail .outer) (by intro l; rfl) W0 (by rfl) (by rfl) (by rfl)
  have e0' : run t0 (cfg (some (.multiplyWord .outer)) (.address false)
      (unary W0)) = cfg (some (.multiplyTail .outer)) (.address false)
      (unary W1) := e0
  obtain ⟨t1,h1,e1⟩ := address_words multiplyTailSlots Label.multiplyTail
    .initClear (by intro l; rfl) W1 (by rfl) (by rfl) (by rfl)
  have e1' : run t1 (cfg (some (.multiplyTail .outer)) (.address false)
      (unary W1)) = cfg (some .initClear) (.address false) (unary W2) := e1
  have ei : run 1 (cfg (some .initClear) (.address false) (unary W2)) =
      cfg (some (.clear 0)) (.copy none) (unary W2) := rfl
  have hc := clear_all_run W2
  have hW : cleared W2 = outputWords d wordBase cy s binBase := by
    funext i
    fin_cases i <;> simp [cleared,clearPrefix,W2,W1,W0,
      preclearWords,geomWords,outputWords]
  have c0 := (run_add e0' t1).trans e1'
  have c1 := (run_add c0 1).trans ei
  have c2 := (run_add c1 (clearTime W2 17+2)).trans hc
  refine ⟨t0+t1+1+(clearTime W2 17+2), ?_, ?_⟩
  · dsimp [finalBound]
    have b0 : t0 ≤ MatrixAddressMachine.exactTime
        d (geom binBase s) 0 := by
      simpa [W0,geomWords] using h0
    have b1 : t1 ≤ MatrixAddressMachine.exactTime
        (tail d wordBase cy s) (binPowerValue binBase s)
        (d * geom binBase s) := by
      simpa [W1,W0,geomWords] using h1
    have hclear : clearTime W2 17 =
        clearTime (preclearWords d wordBase cy s binBase) 17 := rfl
    omega
  · simpa only [W2,W0,hW] using c2

def bound (d wordBase cy s binBase : ℕ) : ℕ :=
  tailBound d wordBase cy s + geomBound binBase s +
    finalBound d wordBase cy s binBase

theorem run_arithmetic (d wordBase cy s binBase : ℕ) :
    ∃ t ≤ bound d wordBase cy s binBase,
      run t (cfg (some start) initial
        (unary (inputWords d wordBase cy s binBase))) =
      cfg none .idle (unary (outputWords d wordBase cy s binBase)) := by
  obtain ⟨t0,h0,e0⟩ := tail_run d wordBase cy s binBase
  obtain ⟨t1,h1,e1⟩ := geom_run d wordBase cy s binBase
  obtain ⟨t2,h2,e2⟩ := final_address_run d wordBase cy s binBase
  refine ⟨t0+t1+t2, ?_, ?_⟩
  · dsimp [bound]
    omega
  · exact (run_add ((run_add e0 t1).trans e1) t2).trans e2

open Construction MatrixStage4Codes MatrixStage4Digits

theorem rawValue_actual {a s q cy : ℕ}
    (hcy : 0 < cy) (hb : 2 ≤ binBase a s q cy)
    (d : SecondRows a s q (Fin cy)) :
    rawValue (secondRowCode a s q cy d).val (wordBase a s cy) cy s
      (binBase a s q cy) =
      (rawColumnCode a s q cy (diagonal d)).val := by
  have hw := MatrixStage4Digits.second_row_word d
  have hd := MatrixWeightedDiagonal.diagonal_ordinal_arithmetic hcy hb d
  rw [hw] at hd
  simpa [rawValue,tail,word,tailPowerValue,binPowerValue,geom] using hd.symm

def actualOutputWords {a s q cy : ℕ} (d : SecondRows a s q (Fin cy)) :
    Stack → ℕ :=
  ![(secondRowCode a s q cy d).val,wordBase a s cy,cy,s,
    binBase a s q cy,(rawColumnCode a s q cy (diagonal d)).val,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

/-- The *single* fixed program terminates with the actual frozen-v8
diagonal column ordinal, preserving every supplied operand word and clearing
every scratch stack. The bound counts each physical transition, including
input copies, both variable powers, three divisions, cuts and final cleanup. -/
theorem actual_run {a s q cy : ℕ}
    (hcy : 0 < cy) (hb : 2 ≤ binBase a s q cy)
    (d : SecondRows a s q (Fin cy)) :
    ∃ t ≤ bound (secondRowCode a s q cy d).val (wordBase a s cy) cy s
        (binBase a s q cy),
      run t (cfg (some start) initial
        (unary (inputWords (secondRowCode a s q cy d).val
          (wordBase a s cy) cy s (binBase a s q cy)))) =
      cfg none .idle (unary (actualOutputWords d)) := by
  obtain ⟨t,ht,hr⟩ := run_arithmetic (secondRowCode a s q cy d).val
    (wordBase a s cy) cy s (binBase a s q cy)
  have hv := rawValue_actual hcy hb d
  have hout : outputWords (secondRowCode a s q cy d).val
      (wordBase a s cy) cy s (binBase a s q cy) = actualOutputWords d := by
    funext i
    fin_cases i <;> simp [outputWords,actualOutputWords,hv]
  exact ⟨t,ht,by simpa only [hout] using hr⟩

end EthInapproximability.CurrentPaper.MatrixWeightedDiagonalMachine
