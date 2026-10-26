import EthInapproximability.CurrentPaper.MatrixWeightedOrderPreparation
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.MatrixUnaryCut

/-!
# Physical graph-item count prelude for the weighted bank

The input boundary is two physical unary words: a normalized graph's vertex
count in global cell 54 and the scale `s` in persistent global cell 28.
The controller prepares `v`, `s-3`, and `4s` in the canonical-order seed cells
7--9, and the weighted vertex/auxiliary counts in cells 18 and 15. It must
empty cell 54 before the weighted writer callback starts. No raw table bit or
other scalar is synthesized here.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedGraphItemCountsPrelude

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 64

def copyProgram (ι : Fin 3 ↪ Stack) :
    BitMachineCopy.Label → TM2.Stmt (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => stackStmt ι (BitMachineCopy.program l)

/-- An embedded literal copy preserves its source and every foreign cell. -/
theorem copy_run (ι : Fin 3 ↪ Stack) (S : Stack → List Bool)
    (hempty : S (ι 2) = []) :
    ((advance (copyProgram ι))^[2 * (S (ι 0)).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        Function.update S (ι 1) (S (ι 0) ++ S (ι 1))⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none (S (ι 0)) (S (ι 1)) []
  have hstart : stackCfg ι S c =
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) := by
    dsimp [stackCfg, c, BitMachineCopy.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [BitMachineCopy.stackContents, hempty]
  have hr := BitMachineStackRun.run ι S BitMachineCopy.program c
    (2 * (S (ι 0)).length + 2)
  rw [hstart] at hr
  change _ = stackCfg ι S
    (BitMachineCopy.run (2 * (S (ι 0)).length + 2) c) at hr
  rw [show c = BitMachineCopy.cfg (some .scan) none
      (S (ι 0)) (S (ι 1)) [] from rfl,
    BitMachineCopy.run_correct] at hr
  have hfinish : stackCfg ι S
      (BitMachineCopy.cfg none none (S (ι 0))
        (S (ι 0) ++ S (ι 1)) []) =
      (⟨none, none, Function.update S (ι 1)
        (S (ι 0) ++ S (ι 1))⟩ : TM2.Cfg (fun _ : Stack => Bool)
          BitMachineCopy.Label (Option Bool)) := by
    dsimp [stackCfg, BitMachineCopy.cfg]
    congr 1
    have hloc : BitMachineCopy.stackContents (S (ι 0))
        (S (ι 0) ++ S (ι 1)) [] =
        Function.update (fun k : Fin 3 => S (ι k)) 1
          (S (ι 0) ++ S (ι 1)) := by
      funext k
      fin_cases k <;> simp [BitMachineCopy.stackContents, hempty]
    rw [hloc, bank_update, bank_restrict]
  exact hr.trans hfinish

def addressProgram (ι : Fin 6 ↪ Stack) :
    MatrixAddressMachine.Label → TM2.Stmt (fun _ : Stack => Bool)
      MatrixAddressMachine.Label Bool :=
  fun l => stackStmt ι (MatrixAddressMachine.program l)

/-- A preserving unary product is written into one ambient cell. -/
theorem address_run (ι : Fin 6 ↪ Stack) (S : Stack → List Bool)
    (r w : ℕ)
    (hr : S (ι 0) = List.replicate r true)
    (hw : S (ι 1) = List.replicate w true)
    (hc : S (ι 2) = []) (hrb : S (ι 3) = [])
    (hwb : S (ι 4) = []) :
    ((advance (addressProgram ι))^[MatrixAddressMachine.exactTime r w 0])
      (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none, false, Function.update S (ι 5)
        (List.replicate (r * w) true ++ S (ι 5))⟩ := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate r true) (List.replicate w true) [] [] [] (S (ι 5))
  have hstart : stackCfg ι S c =
      (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) := by
    dsimp [stackCfg, c, MatrixAddressMachine.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [hr, hw, hc, hrb, hwb]
  have hrun := BitMachineStackRun.run ι S MatrixAddressMachine.program c
    (MatrixAddressMachine.exactTime r w 0)
  rw [hstart] at hrun
  change _ = stackCfg ι S
    (MatrixAddressMachine.run (MatrixAddressMachine.exactTime r w 0) c) at hrun
  have hlocal : MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime r w 0) c =
      MatrixAddressMachine.cfg none false (List.replicate r true)
        (List.replicate w true) [] [] []
        (List.replicate (r*w) true ++ S (ι 5)) := by
    simpa only [c, Nat.add_zero, List.replicate_zero] using
      MatrixAddressMachine.address_run r w 0 false (S (ι 5))
  rw [hlocal] at hrun
  have hfinish : stackCfg ι S
      (MatrixAddressMachine.cfg none false (List.replicate r true)
        (List.replicate w true) [] [] []
        (List.replicate (r*w) true ++ S (ι 5))) =
      (⟨none, false, Function.update S (ι 5)
        (List.replicate (r*w) true ++ S (ι 5))⟩ :
          TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) := by
    dsimp [stackCfg, MatrixAddressMachine.cfg]
    congr 1
    have hloc : (![List.replicate r true, List.replicate w true,
        ([] : List Bool), [], [],
        List.replicate (r*w) true ++ S (ι 5)] : Fin 6 → List Bool) =
        Function.update (fun k : Fin 6 => S (ι k)) 5
          (List.replicate (r*w) true ++ S (ι 5)) := by
      funext k
      fin_cases k <;> simp [hr, hw, hc, hrb, hwb]
    rw [hloc, bank_update, bank_restrict]
  exact hrun.trans hfinish

inductive CutLabel where
  | first | second | third
  deriving DecidableEq, Fintype

def cutProgram : CutLabel → TM2.Stmt (fun _ : Stack => Bool) CutLabel Unit
  | .first => .pop 8 (fun _ _ => ()) (.goto (fun _ => .second))
  | .second => .pop 8 (fun _ _ => ()) (.goto (fun _ => .third))
  | .third => .pop 8 (fun _ _ => ()) .halt

private theorem cut_first (S : Stack → List Bool) :
    advance cutProgram
      (⟨some .first, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) CutLabel Unit) =
      ⟨some .second, (), Function.update S 8 (S 8).tail⟩ := rfl

private theorem cut_second (S : Stack → List Bool) :
    advance cutProgram
      (⟨some .second, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) CutLabel Unit) =
      ⟨some .third, (), Function.update S 8 (S 8).tail⟩ := rfl

private theorem cut_third (S : Stack → List Bool) :
    advance cutProgram
      (⟨some .third, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) CutLabel Unit) =
      ⟨none, (), Function.update S 8 (S 8).tail⟩ := rfl

theorem cut_run (S : Stack → List Bool) :
    ((advance cutProgram)^[3])
      (⟨some .first, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        CutLabel Unit) =
      ⟨none, (), Function.update S 8 ((S 8).drop 3)⟩ := by
  change advance cutProgram (advance cutProgram (advance cutProgram
    (⟨some .first, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) CutLabel Unit))) = _
  rw [cut_first, cut_second, cut_third]
  congr 1
  funext k
  by_cases hk : k = 8
  · subst k
    cases h : S 8 with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c ys =>
        cases ys with
        | nil => rfl
        | cons d zs => rfl
  · simp [Function.update_of_ne hk]

def vSlots : Fin 3 ↪ Stack := ⟨![54, 7, 55], by decide⟩
def aSlots : Fin 3 ↪ Stack := ⟨![28, 8, 55], by decide⟩
def kSlots : Fin 3 ↪ Stack := ⟨![28, 9, 55], by decide⟩
def nvSlots : Fin 6 ↪ Stack := ⟨![9, 7, 56, 57, 58, 18], by decide⟩
def nbSlots : Fin 6 ↪ Stack := ⟨![9, 8, 56, 57, 58, 15], by decide⟩

def vProgram := copyProgram vSlots
def aProgram := copyProgram aSlots
def kProgram := copyProgram kSlots
def nvProgram := addressProgram nvSlots
def nbProgram := addressProgram nbSlots

def vaProgram := BitMachineRawSequence.program vProgram aProgram
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)

theorem va_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h55 : S 55 = []) :
    ∃ t ≤ (2*v+2)+(2*s+2)+1,
      ((advance vaProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
          (Option Bool × Option Bool)) =
        ⟨none, (none, none),
          Function.update (Function.update S 7 (List.replicate v true))
            8 (List.replicate s true)⟩ := by
  let T := Function.update S 7 (List.replicate v true)
  have hV : ((advance vProgram)^[2*v+2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, T⟩ := by
    simpa [vProgram, vSlots, T, hv, h7] using
      copy_run vSlots S (by simpa only [vSlots] using h55)
  have hT28 : T 28 = List.replicate s true := by
    simp only [T, Function.update_of_ne (by decide : (28 : Stack) ≠ 7), hs]
  have hT8 : T 8 = [] := by
    simp only [T, Function.update_of_ne (by decide : (8 : Stack) ≠ 7), h8]
  have hT55 : T 55 = [] := by
    simp only [T, Function.update_of_ne (by decide : (55 : Stack) ≠ 7), h55]
  have hA : ((advance aProgram)^[2*s+2])
      (⟨some .scan, none, T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update T 8 (List.replicate s true)⟩ := by
    simpa [aProgram, aSlots, hT28, hT8] using
      copy_run aSlots T (by simpa only [aSlots] using hT55)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs vProgram aProgram
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    (none : Option Bool) none (none : Option Bool) none
    S T (Function.update T 8 (List.replicate s true))
    (2*v+2) (2*s+2) hV hA
  exact ⟨t, ht, by simpa only [vaProgram, T] using hr⟩

def k2Program := BitMachineRawSequence.program kProgram kProgram
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)

theorem k2_run (S : Stack → List Bool) (s p : ℕ)
    (hs : S 28 = List.replicate s true)
    (hp : S 9 = List.replicate p true)
    (h55 : S 55 = []) :
    ∃ t ≤ 2*(2*s+2)+1,
      ((advance k2Program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
          (Option Bool × Option Bool)) =
        ⟨none, (none, none), Function.update S 9
          (List.replicate (p+2*s) true)⟩ := by
  let T := Function.update S 9 (List.replicate (p+s) true)
  have h₁ : ((advance kProgram)^[2*s+2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, T⟩ := by
    simpa [kProgram, kSlots, T, hs, hp,
      List.replicate_append_replicate, Nat.add_comm] using
      copy_run kSlots S (by simpa only [kSlots] using h55)
  have hTs : T 28 = List.replicate s true := by
    simp only [T, Function.update_of_ne (by decide : (28 : Stack) ≠ 9), hs]
  have hTp : T 9 = List.replicate (p+s) true := by simp [T]
  have hT55 : T 55 = [] := by
    simp only [T, Function.update_of_ne (by decide : (55 : Stack) ≠ 9), h55]
  have h₂ : ((advance kProgram)^[2*s+2])
      (⟨some .scan, none, T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S 9
        (List.replicate (p+2*s) true)⟩ := by
    have hcopy := copy_run kSlots T
      (by simpa only [kSlots] using hT55)
    rw [show T (kSlots 0) = List.replicate s true from hTs,
      show T (kSlots 1) = List.replicate (p+s) true from hTp,
      List.length_replicate] at hcopy
    have hcount : s + (p + s) = p + 2*s := by omega
    simpa [kProgram, kSlots, T, hs,
      List.replicate_append_replicate, hcount] using hcopy
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs kProgram kProgram
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    (none : Option Bool) none (none : Option Bool) none
    S T (Function.update S 9 (List.replicate (p+2*s) true))
    (2*s+2) (2*s+2) h₁ h₂
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [k2Program] using hr

def k4Program := BitMachineRawSequence.program k2Program k2Program
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  ((none : Option Bool), none) ((none : Option Bool), none)

theorem k4_run (S : Stack → List Bool) (s : ℕ)
    (hs : S 28 = List.replicate s true)
    (h9 : S 9 = []) (h55 : S 55 = []) :
    ∃ t ≤ 2*(2*(2*s+2)+1)+1,
      ((advance k4Program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, none)), S⟩ : TM2.Cfg
          (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
            (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label))
          ((Option Bool × Option Bool) × (Option Bool × Option Bool))) =
        ⟨none, ((none, none), (none, none)),
          Function.update S 9 (List.replicate (4*s) true)⟩ := by
  let T := Function.update S 9 (List.replicate (2*s) true)
  have h₁ := k2_run S s 0 hs (by simpa using h9) h55
  have hT28 : T 28 = List.replicate s true := by
    simp only [T, Function.update_of_ne (by decide : (28 : Stack) ≠ 9), hs]
  have hT9 : T 9 = List.replicate (2*s) true := by simp [T]
  have hT55 : T 55 = [] := by
    simp only [T, Function.update_of_ne (by decide : (55 : Stack) ≠ 9), h55]
  have h₂ := k2_run T s (2*s) hT28 hT9 hT55
  obtain ⟨t₁, ht₁, hr₁⟩ := h₁
  obtain ⟨t₂, ht₂, hr₂⟩ := h₂
  have hr₁' : ((advance k2Program)^[t₁])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        (none, none), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
        (Option Bool × Option Bool)) = ⟨none, (none, none), T⟩ := by
    simpa only [T, Nat.zero_add] using hr₁
  have hr₂' : ((advance k2Program)^[t₂])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        (none, none), T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
        (Option Bool × Option Bool)) =
      ⟨none, (none, none),
        Function.update S 9 (List.replicate (4*s) true)⟩ := by
    have heq : 2*s + 2*s = 4*s := by omega
    simpa [T, heq] using hr₂
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs k2Program k2Program
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((none, none) : Option Bool × Option Bool) (none, none)
    ((none, none) : Option Bool × Option Bool) (none, none)
    S T (Function.update S 9 (List.replicate (4*s) true))
    t₁ t₂ hr₁' hr₂'
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [k4Program] using hr

def vaCutProgram := BitMachineRawSequence.program vaProgram cutProgram
  CutLabel.first ((none, none) : Option Bool × Option Bool) ()

theorem va_cut_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h55 : S 55 = []) :
    ∃ t ≤ (2*v+2)+(2*s+2)+1+3+1,
      ((advance vaCutProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), ()), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
            CutLabel)
          ((Option Bool × Option Bool) × Unit)) =
        ⟨none, ((none, none), ()),
          Function.update (Function.update S 7 (List.replicate v true))
            8 (List.replicate (s-3) true)⟩ := by
  let T := Function.update (Function.update S 7 (List.replicate v true))
    8 (List.replicate s true)
  obtain ⟨t₁, ht₁, hr₁⟩ := va_run S v s hv hs h7 h8 h55
  have hT8 : T 8 = List.replicate s true := by simp [T]
  have hcut := cut_run T
  have hcut' : ((advance cutProgram)^[3])
      (⟨some .first, (), T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        CutLabel Unit) =
      ⟨none, (), Function.update
        (Function.update S 7 (List.replicate v true))
        8 (List.replicate (s-3) true)⟩ := by
    simpa [T, hT8, List.drop_replicate] using hcut
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs vaProgram cutProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    CutLabel.first ((none, none) : Option Bool × Option Bool)
    (none, none) () () S T
    (Function.update (Function.update S 7 (List.replicate v true))
      8 (List.replicate (s-3) true)) t₁ 3
    (by simpa only [T] using hr₁) hcut'
  exact ⟨t, by omega, by simpa only [vaCutProgram] using hr⟩

abbrev VaCutLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
  CutLabel
abbrev VaCutControl := (Option Bool × Option Bool) × Unit
abbrev K4Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
  (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
abbrev K4Control := (Option Bool × Option Bool) × (Option Bool × Option Bool)

def vaKProgram := BitMachineRawSequence.program vaCutProgram k4Program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
  (((none, none), ()) : VaCutControl)
  (((none, none), (none, none)) : K4Control)

theorem va_k_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h55 : S 55 = []) :
    ∃ t ≤ ((2*v+2)+(2*s+2)+1+3+1) +
        (2*(2*(2*s+2)+1)+1) + 1,
      ((advance vaKProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          ((((none, none), ()), ((none, none), (none, none)))), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label VaCutLabel K4Label)
            (VaCutControl × K4Control)) =
        ⟨none, ((((none, none), ()), ((none, none), (none, none)))),
          Function.update
            (Function.update
              (Function.update S 7 (List.replicate v true))
              8 (List.replicate (s-3) true))
            9 (List.replicate (4*s) true)⟩ := by
  let T := Function.update (Function.update S 7 (List.replicate v true))
    8 (List.replicate (s-3) true)
  obtain ⟨t₁, ht₁, hr₁⟩ := va_cut_run S v s hv hs h7 h8 h55
  have hT28 : T 28 = List.replicate s true := by
    simp only [T, Function.update_of_ne (by decide : (28 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (28 : Stack) ≠ 7), hs]
  have hT9 : T 9 = [] := by
    simp only [T, Function.update_of_ne (by decide : (9 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (9 : Stack) ≠ 7), h9]
  have hT55 : T 55 = [] := by
    simp only [T, Function.update_of_ne (by decide : (55 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (55 : Stack) ≠ 7), h55]
  obtain ⟨t₂, ht₂, hr₂⟩ := k4_run T s hT28 hT9 hT55
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs vaCutProgram k4Program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((none, none), ()) : VaCutControl) ((none, none), ())
    (((none, none), (none, none)) : K4Control)
      ((none, none), (none, none)) S T
    (Function.update T 9 (List.replicate (4*s) true))
    t₁ t₂ (by simpa only [T] using hr₁) hr₂
  exact ⟨t, by omega, by simpa only [vaKProgram, T] using hr⟩

abbrev VaKLabel := BitMachineRawSequence.Label VaCutLabel K4Label
abbrev VaKControl := VaCutControl × K4Control

def vaNvProgram := BitMachineRawSequence.program vaKProgram nvProgram
  MatrixAddressMachine.Label.outer
  (((none, none), ()), ((none, none), (none, none)))
  false

theorem va_nv_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h18 : S 18 = []) (h55 : S 55 = [])
    (h56 : S 56 = []) (h57 : S 57 = []) (h58 : S 58 = []) :
    ∃ t ≤ ((2*v+2)+(2*s+2)+1+3+1) +
        (2*(2*(2*s+2)+1)+1) + 1 +
        MatrixAddressMachine.exactTime (4*s) v 0 + 1,
      ((advance vaNvProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          (((((none, none), ()), ((none, none), (none, none))), false)), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label VaKLabel MatrixAddressMachine.Label)
            (VaKControl × Bool)) =
        ⟨none, (((((none, none), ()), ((none, none), (none, none))), false)),
          Function.update
            (Function.update
              (Function.update
                (Function.update S 7 (List.replicate v true))
                8 (List.replicate (s-3) true))
              9 (List.replicate (4*s) true))
            18 (List.replicate (4*s*v) true)⟩ := by
  let T := Function.update
    (Function.update
      (Function.update S 7 (List.replicate v true))
      8 (List.replicate (s-3) true))
    9 (List.replicate (4*s) true)
  obtain ⟨t₁, ht₁, hr₁⟩ :=
    va_k_run S v s hv hs h7 h8 h9 h55
  have hT9 : T 9 = List.replicate (4*s) true := by simp [T]
  have hT7 : T 7 = List.replicate v true := by simp [T]
  have hT18 : T 18 = [] := by
    simp only [T, Function.update_of_ne (by decide : (18 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (18 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (18 : Stack) ≠ 7), h18]
  have hT56 : T 56 = [] := by
    simp only [T, Function.update_of_ne (by decide : (56 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (56 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (56 : Stack) ≠ 7), h56]
  have hT57 : T 57 = [] := by
    simp only [T, Function.update_of_ne (by decide : (57 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (57 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (57 : Stack) ≠ 7), h57]
  have hT58 : T 58 = [] := by
    simp only [T, Function.update_of_ne (by decide : (58 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (58 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (58 : Stack) ≠ 7), h58]
  have hnv : ((advance nvProgram)^[MatrixAddressMachine.exactTime (4*s) v 0])
      (⟨some .outer, false, T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none, false, Function.update T 18
        (List.replicate (4*s*v) true)⟩ := by
    simpa [nvProgram, nvSlots, hT9, hT7, hT18] using
      address_run nvSlots T (4*s) v hT9 hT7
        (by simpa only [nvSlots] using hT56)
        (by simpa only [nvSlots] using hT57)
        (by simpa only [nvSlots] using hT58)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs vaKProgram nvProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    MatrixAddressMachine.Label.outer
    ((((none, none), ()), ((none, none), (none, none))) : VaKControl)
      (((none, none), ()), ((none, none), (none, none)))
    false false S T
    (Function.update T 18 (List.replicate (4*s*v) true))
    t₁ (MatrixAddressMachine.exactTime (4*s) v 0)
    (by simpa only [T] using hr₁) hnv
  exact ⟨t, by omega, by simpa only [vaNvProgram, T] using hr⟩

abbrev VaNvLabel := BitMachineRawSequence.Label VaKLabel MatrixAddressMachine.Label
abbrev VaNvControl := VaKControl × Bool

def vaNvNbProgram := BitMachineRawSequence.program vaNvProgram nbProgram
  MatrixAddressMachine.Label.outer
  (((((none, none), ()), ((none, none), (none, none))), false) : VaNvControl)
  false

theorem va_nv_nb_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h15 : S 15 = []) (h18 : S 18 = []) (h55 : S 55 = [])
    (h56 : S 56 = []) (h57 : S 57 = []) (h58 : S 58 = []) :
    ∃ t ≤ ((2*v+2)+(2*s+2)+1+3+1) +
        (2*(2*(2*s+2)+1)+1) + 1 +
        MatrixAddressMachine.exactTime (4*s) v 0 + 1 +
        MatrixAddressMachine.exactTime (4*s) (s-3) 0 + 1,
      ((advance vaNvNbProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
          ((((((none, none), ()), ((none, none), (none, none))), false), false)),
          S⟩ : TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label VaNvLabel MatrixAddressMachine.Label)
            (VaNvControl × Bool)) =
        ⟨none,
          ((((((none, none), ()), ((none, none), (none, none))), false), false)),
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update S 7 (List.replicate v true))
                  8 (List.replicate (s-3) true))
                9 (List.replicate (4*s) true))
              18 (List.replicate (4*s*v) true))
            15 (List.replicate (4*s*(s-3)) true)⟩ := by
  let T := Function.update
    (Function.update
      (Function.update
        (Function.update S 7 (List.replicate v true))
        8 (List.replicate (s-3) true))
      9 (List.replicate (4*s) true))
    18 (List.replicate (4*s*v) true)
  obtain ⟨t₁, ht₁, hr₁⟩ :=
    va_nv_run S v s hv hs h7 h8 h9 h18 h55 h56 h57 h58
  have hT9 : T 9 = List.replicate (4*s) true := by simp [T]
  have hT8 : T 8 = List.replicate (s-3) true := by simp [T]
  have hT15 : T 15 = [] := by
    simp only [T, Function.update_of_ne (by decide : (15 : Stack) ≠ 18),
      Function.update_of_ne (by decide : (15 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (15 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (15 : Stack) ≠ 7), h15]
  have hT56 : T 56 = [] := by
    simp only [T, Function.update_of_ne (by decide : (56 : Stack) ≠ 18),
      Function.update_of_ne (by decide : (56 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (56 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (56 : Stack) ≠ 7), h56]
  have hT57 : T 57 = [] := by
    simp only [T, Function.update_of_ne (by decide : (57 : Stack) ≠ 18),
      Function.update_of_ne (by decide : (57 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (57 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (57 : Stack) ≠ 7), h57]
  have hT58 : T 58 = [] := by
    simp only [T, Function.update_of_ne (by decide : (58 : Stack) ≠ 18),
      Function.update_of_ne (by decide : (58 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (58 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (58 : Stack) ≠ 7), h58]
  have hnb : ((advance nbProgram)^[MatrixAddressMachine.exactTime (4*s) (s-3) 0])
      (⟨some .outer, false, T⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none, false, Function.update T 15
        (List.replicate (4*s*(s-3)) true)⟩ := by
    simpa [nbProgram, nbSlots, hT9, hT8, hT15] using
      address_run nbSlots T (4*s) (s-3) hT9 hT8
        (by simpa only [nbSlots] using hT56)
        (by simpa only [nbSlots] using hT57)
        (by simpa only [nbSlots] using hT58)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs vaNvProgram nbProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    MatrixAddressMachine.Label.outer
    (((((none, none), ()), ((none, none), (none, none))), false) : VaNvControl)
      ((((none, none), ()), ((none, none), (none, none))), false)
    false false S T
    (Function.update T 15 (List.replicate (4*s*(s-3)) true))
    t₁ (MatrixAddressMachine.exactTime (4*s) (s-3) 0)
    (by simpa only [T] using hr₁) hnb
  exact ⟨t, by omega, by simpa only [vaNvNbProgram, T] using hr⟩

inductive ClearLabel where
  | clear | done
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel → TM2.Stmt (fun _ : Stack => Bool)
    ClearLabel (Unit × Option Bool)
  | .clear => BitMachineClearBank.clearStep 54 .clear .done
  | .done => .halt

theorem clear_run (S : Stack → List Bool) :
    ((advance clearProgram)^[(S 54).length+2])
      (⟨some .clear, ((), none), S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update S 54 []⟩ := by
  have h := BitMachineClearBank.clear_one_run clearProgram 54
    ClearLabel.clear ClearLabel.done rfl () S
  rw [show (S 54).length+2 = ((S 54).length+1)+1 by omega,
    Function.iterate_succ_apply', h]
  rfl

abbrev VaNvNbLabel := BitMachineRawSequence.Label
  VaNvLabel MatrixAddressMachine.Label
abbrev VaNvNbControl := VaNvControl × Bool

def program := BitMachineRawSequence.program vaNvNbProgram clearProgram
  ClearLabel.clear
  ((((((none, none), ()), ((none, none), (none, none))), false), false) :
    VaNvNbControl)
  ((), none)

abbrev Label := BitMachineRawSequence.Label VaNvNbLabel ClearLabel
abbrev Control := VaNvNbControl × (Unit × Option Bool)

def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))

def initial : Control :=
  ((((((none, none), ()), ((none, none), (none, none))), false), false),
    ((), none))

def finalBank (S : Stack → List Bool) (v s : ℕ) : Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update S 7 (List.replicate v true))
            8 (List.replicate (s-3) true))
          9 (List.replicate (4*s) true))
        18 (List.replicate (4*s*v) true))
      15 (List.replicate (4*s*(s-3)) true))
    54 []

def cost (v s : ℕ) : ℕ :=
  ((2*v+2)+(2*s+2)+1+3+1) +
    (2*(2*(2*s+2)+1)+1) + 1 +
    MatrixAddressMachine.exactTime (4*s) v 0 + 1 +
    MatrixAddressMachine.exactTime (4*s) (s-3) 0 + 1 +
    v+2+1

/-- Complete fixed-bank count prelude; all phases and handoffs are charged. -/
theorem run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h15 : S 15 = []) (h18 : S 18 = []) (h55 : S 55 = [])
    (h56 : S 56 = []) (h57 : S 57 = []) (h58 : S 58 = []) :
    ∃ t ≤ cost v s,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
          Label Control) =
        ⟨none, initial, finalBank S v s⟩ := by
  let T := Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update S 7 (List.replicate v true))
          8 (List.replicate (s-3) true))
        9 (List.replicate (4*s) true))
      18 (List.replicate (4*s*v) true))
    15 (List.replicate (4*s*(s-3)) true)
  obtain ⟨t₁, ht₁, hr₁⟩ :=
    va_nv_nb_run S v s hv hs h7 h8 h9 h15 h18 h55 h56 h57 h58
  have hT54 : T 54 = List.replicate v true := by
    simp only [T, Function.update_of_ne (by decide : (54 : Stack) ≠ 15),
      Function.update_of_ne (by decide : (54 : Stack) ≠ 18),
      Function.update_of_ne (by decide : (54 : Stack) ≠ 9),
      Function.update_of_ne (by decide : (54 : Stack) ≠ 8),
      Function.update_of_ne (by decide : (54 : Stack) ≠ 7), hv]
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    vaNvNbProgram clearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
    ClearLabel.clear
    ((((((none, none), ()), ((none, none), (none, none))), false), false) :
      VaNvNbControl)
    (((((none, none), ()), ((none, none), (none, none))), false), false)
    (((), none) : Unit × Option Bool) ((), none)
    S T (Function.update T 54 []) t₁ (v+2)
    (by simpa only [T] using hr₁)
    (by simpa only [hT54, List.length_replicate] using clear_run T)
  refine ⟨t, ?_, ?_⟩
  · dsimp only [cost]
    omega
  · simpa only [program, start, initial, finalBank, T] using hr

theorem final_order_vertices (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 7 = List.replicate v true := by
  simp [finalBank]

theorem final_order_auxiliary (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 8 = List.replicate (s-3) true := by
  simp [finalBank]

theorem final_order_copies (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 9 = List.replicate (4*s) true := by
  simp [finalBank]

theorem final_vertex_count (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 18 = List.replicate (GraphVectors.vertexCount (Fin v) s) true := by
  simp [finalBank, GraphVectors.vertexCount]

theorem final_auxiliary_count (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 15 = List.replicate (GraphVectors.auxiliaryCount s) true := by
  simp [finalBank, GraphVectors.auxiliaryCount]

theorem final_vertex_source_empty (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 54 = [] := by
  simp [finalBank]

theorem final_foreign (S : Stack → List Bool) (v s : ℕ) (j : Stack)
    (hj7 : j ≠ 7) (hj8 : j ≠ 8) (hj9 : j ≠ 9)
    (hj15 : j ≠ 15) (hj18 : j ≠ 18) (hj54 : j ≠ 54) :
    finalBank S v s j = S j := by
  simp only [finalBank, Function.update_of_ne hj54,
    Function.update_of_ne hj15, Function.update_of_ne hj18,
    Function.update_of_ne hj9, Function.update_of_ne hj8,
    Function.update_of_ne hj7]

theorem final_rawBits (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 22 = S 22 := by
  apply final_foreign <;> decide

theorem final_scale (S : Stack → List Bool) (v s : ℕ) :
    finalBank S v s 28 = S 28 := by
  apply final_foreign <;> decide

/-- The terminal bank is exactly the canonical-order machine's physical
starting bank, once its still-unused work cells are empty. -/
theorem order_start_bank (S : Stack → List Bool) (v s : ℕ)
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h60 : S 60 = []) :
    MatrixWeightedOrderPreparation.sourceBank (finalBank S v s)
      v (s-3) (4*s) = finalBank S v s := by
  unfold MatrixWeightedOrderPreparation.sourceBank
  apply bank_eq_self
  intro i
  fin_cases i <;>
    simp [MatrixWeightedOrderPreparation.slots,
      MatrixWeightedCanonicalOrderMachine.initialBank,
      finalBank, h10, h11, h12, h13, h14, h60]

def joinedProgram := BitMachineRawSequence.program program
  MatrixWeightedOrderPreparation.program
  MatrixWeightedOrderPreparation.start initial
  MatrixWeightedOrderPreparation.initial

abbrev JoinedLabel := BitMachineRawSequence.Label
  Label MatrixWeightedOrderPreparation.Label
abbrev JoinedControl := Control × MatrixWeightedOrderPreparation.Control

/-- One fixed physical controller prepares graph-item counts and the canonical
order word, then clears every order seed/work slot. -/
theorem joined_run (S : Stack → List Bool) (v s : ℕ)
    (hv : S 54 = List.replicate v true)
    (hs : S 28 = List.replicate s true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = [])
    (h15 : S 15 = []) (h18 : S 18 = []) (h55 : S 55 = [])
    (h56 : S 56 = []) (h57 : S 57 = []) (h58 : S 58 = [])
    (h60 : S 60 = []) :
    ∃ t ≤ cost v s +
        MatrixWeightedOrderPreparation.prepCost v (s-3) (4*s) + 1,
      ((advance joinedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel start),
          (initial, MatrixWeightedOrderPreparation.initial), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) JoinedLabel JoinedControl) =
        ⟨none, (initial, MatrixWeightedOrderPreparation.initial),
          MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
            v (s-3) (4*s)⟩ := by
  obtain ⟨t₁, ht₁, hr₁⟩ := run S v s hv hs
    h7 h8 h9 h15 h18 h55 h56 h57 h58
  obtain ⟨t₂, ht₂, hr₂⟩ :=
    MatrixWeightedOrderPreparation.canonical_order_polynomial_run
      (finalBank S v s) v (s-3) (4*s)
  have hsecond : ((advance MatrixWeightedOrderPreparation.program)^[t₂])
      (⟨some MatrixWeightedOrderPreparation.start,
        MatrixWeightedOrderPreparation.initial, finalBank S v s⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          MatrixWeightedOrderPreparation.Label
          MatrixWeightedOrderPreparation.Control) =
      ⟨none, MatrixWeightedOrderPreparation.initial,
        MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
          v (s-3) (4*s)⟩ := by
    simpa only [MatrixWeightedOrderPreparation.run,
      MatrixWeightedOrderPreparation.cfg,
      order_start_bank S v s h10 h11 h12 h13 h14 h60] using hr₂
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    program MatrixWeightedOrderPreparation.program
    start MatrixWeightedOrderPreparation.start
    initial initial MatrixWeightedOrderPreparation.initial
    MatrixWeightedOrderPreparation.initial
    S (finalBank S v s)
    (MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
      v (s-3) (4*s)) t₁ t₂ hr₁ hsecond
  exact ⟨t, by omega, by simpa only [joinedProgram] using hr⟩

theorem joined_order_word (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 60 =
      MatrixWeightedCanonicalOrderMachine.canonicalWord v (s-3) (4*s) :=
  MatrixWeightedOrderPreparation.readyBank_order _ _ _ _

theorem joined_vertex_count (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 18 =
      List.replicate (GraphVectors.vertexCount (Fin v) s) true := by
  rw [MatrixWeightedOrderPreparation.readyBank_frame _ _ _ _ 18
    (by decide)]
  exact final_vertex_count S v s

theorem joined_auxiliary_count (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 15 =
      List.replicate (GraphVectors.auxiliaryCount s) true := by
  rw [MatrixWeightedOrderPreparation.readyBank_frame _ _ _ _ 15
    (by decide)]
  exact final_auxiliary_count S v s

theorem joined_rawBits (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 22 = S 22 := by
  rw [MatrixWeightedOrderPreparation.readyBank_frame _ _ _ _ 22
    (by decide)]
  exact final_rawBits S v s

theorem joined_scale (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 28 = S 28 := by
  rw [MatrixWeightedOrderPreparation.readyBank_frame _ _ _ _ 28
    (by decide)]
  exact final_scale S v s

theorem joined_vertex_source_empty (S : Stack → List Bool) (v s : ℕ) :
    MatrixWeightedOrderPreparation.readyBank (finalBank S v s)
        v (s-3) (4*s) 54 = [] := by
  rw [MatrixWeightedOrderPreparation.readyBank_frame _ _ _ _ 54
    (by decide)]
  exact final_vertex_source_empty S v s

/-- Quadratic in the two physical unary source-word lengths. -/
theorem cost_quadratic (v s : ℕ) :
    cost v s ≤ 100 * (v+s+1)^2 := by
  have hs : s-3 ≤ s := Nat.sub_le s 3
  have hm : 8*s*(s-3) ≤ 8*s*s := Nat.mul_le_mul_left (8*s) hs
  unfold cost MatrixAddressMachine.exactTime
  nlinarith [sq_nonneg (Int.ofNat v - Int.ofNat s)]

#print axioms run
#print axioms joined_run
#print axioms final_rawBits
#print axioms joined_rawBits
#print axioms cost_quadratic

end EthInapproximability.CurrentPaper.MatrixWeightedGraphItemCountsPrelude
