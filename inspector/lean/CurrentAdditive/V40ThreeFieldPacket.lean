import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import CurrentAdditive.GaussSerializeClears
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace CurrentAdditive.V40ThreeFieldPacket

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Stack := Fin 9
abbrev Bank := Stack → List Bool

def copySlots (i : Fin 3) : Fin 3 ↪ Stack where
  toFun j := if j = 0 then ⟨i.val, by omega⟩ else
    if j = 1 then ⟨i.val + 3, by omega⟩ else 6
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]
    all_goals have hi := i.isLt; omega

def serSlots : BitMachineBankSerialize.Stack 3 ↪ Stack where
  toFun
    | .inl i => ⟨i.val + 3, by omega⟩
    | .inr i => ⟨i.val + 6, by omega⟩
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff]
    all_goals omega

def copyProgram (i : Fin 3) := ExactParameterBranchInstall.copyProgram (copySlots i)

def serProgram (l : BitMachineBankSerialize.Label 3) :=
  BitMachineStackEmbedding.stackStmt serSlots (BitMachineBankSerialize.program 3 l)

def p01 := BitMachineRawSequence.program (copyProgram 0) (copyProgram 1)
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)

def p012 := BitMachineRawSequence.program p01 (copyProgram 2)
  BitMachineCopy.Label.scan ((none, none) : Option Bool × Option Bool) (none : Option Bool)

def program := BitMachineRawSequence.program p012 serProgram
  (BitMachineBankSerialize.Label.emit 0)
  (((none, none), none) : (Option Bool × Option Bool) × Option Bool) (none : Option Bool)

abbrev Label01 := BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label
abbrev Label012 := BitMachineRawSequence.Label Label01 BitMachineCopy.Label
abbrev Label := BitMachineRawSequence.Label Label012 (BitMachineBankSerialize.Label 3)

def entry : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))

def initial := ((((none, none), none), none) : ((Option Bool × Option Bool) × Option Bool) × Option Bool)

def words (x y z : List Bool) : Fin 3 → List Bool := ![x, y, z]

def bytes (x y z : List Bool) : List Bool := BitMachineBankCodec.encode (words x y z)

private theorem copy_run (i : Fin 3) (S : Bank) (word : List Bool)
    (hsource : S ⟨i.val, by omega⟩ = word)
    (htarget : S ⟨i.val + 3, by omega⟩ = []) (hscratch : S 6 = []) :
    ∃ t ≤ 2 * word.length + 2,
      ((advance (copyProgram i))^[t])
        (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, none, Function.update S ⟨i.val + 3, by omega⟩ word⟩ := by
  simpa only [copyProgram, copySlots, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.reduceEq, ite_true, ite_false] using
    ExactParameterBranchInstall.copy_run (copySlots i) S word hsource htarget hscratch

theorem run (S : Bank) (x y z : List Bool)
    (h0 : S 0 = x) (h1 : S 1 = y) (h2 : S 2 = z)
    (hblank : ∀ i : Fin 6, S ⟨i.val + 3, by omega⟩ = []) :
    ∃ t ≤ 3 * (bytes x y z).length + 8,
      ((advance program)^[t])
        (⟨some entry, initial, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, initial, Function.update S 8 (bytes x y z)⟩ := by
  let S1 := Function.update S 3 x
  let S2 := Function.update S1 4 y
  let S3 := Function.update S2 5 z
  have hb3 : S 3 = [] := hblank 0
  have hb4 : S 4 = [] := hblank 1
  have hb5 : S 5 = [] := hblank 2
  have hb6 : S 6 = [] := hblank 3
  have hb7 : S 7 = [] := hblank 4
  have hb8 : S 8 = [] := hblank 5
  obtain ⟨a, ha, hca⟩ := copy_run 0 S x h0 hb3 hb6
  obtain ⟨b, hb, hcb⟩ := copy_run 1 S1 y (by simp [S1, h1])
    (by simp [S1, hb4]) (by simp [S1, hb6])
  obtain ⟨c, hc, hcc⟩ := copy_run 2 S2 z (by simp [S2, S1, h2])
    (by simp [S2, S1, hb5]) (by simp [S2, S1, hb6])
  obtain ⟨d, hd, hs⟩ := GaussSerializeClears.serialize_empty (words x y z) [] []
  have hbytes : BitMachineBankSerialize.encode (List.ofFn (words x y z)) = bytes x y z := by
    simp [bytes, BitMachineBankSerialize.encode, BitMachineBankCodec.encode_eq_list]
  have hs' : ((advance (BitMachineBankSerialize.program 3))^[d])
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y z) [] [] []) =
      BitMachineBankSerialize.cfg none none (fun _ => []) [] [] (bytes x y z) := by
    simpa only [BitMachineBankSerialize.run, hbytes, List.append_nil] using hs
  let cs := BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y z) [] [] []
  have hbank : BitMachineStackEmbedding.bank serSlots S3 cs.stk = S3 := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    cases i with
    | inl i => fin_cases i <;> simp [serSlots, cs, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents, words, S3, S2, S1]
    | inr i => fin_cases i <;> simp [serSlots, cs, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents, S3, S2, S1, hb6, hb7, hb8]
  have hser := BitMachineStackRun.run serSlots S3 (BitMachineBankSerialize.program 3) cs d
  rw [hs'] at hser
  have hout : BitMachineStackEmbedding.bank serSlots S3
      (BitMachineBankSerialize.contents (fun _ : Fin 3 => []) [] [] (bytes x y z)) =
      Function.update S 8 (bytes x y z) := by
    have hforeign (i : Fin 3) : BitMachineStackEmbedding.bank serSlots S3
        (BitMachineBankSerialize.contents (fun _ : Fin 3 => []) [] [] (bytes x y z))
          ⟨i.val, by omega⟩ = S ⟨i.val, by omega⟩ := by
      rw [BitMachineStackEmbedding.bank_outside]
      · fin_cases i <;> simp [S3, S2, S1]
      · rintro ⟨j, hj⟩
        have hi := i.isLt
        have hv := congrArg Fin.val hj
        cases j with
        | inl j =>
            change j.val + 3 = i.val at hv
            omega
        | inr j =>
            change j.val + 6 = i.val at hv
            omega
    funext i
    fin_cases i
    · simpa using hforeign 0
    · simpa using hforeign 1
    · simpa using hforeign 2
    all_goals first
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inl 0)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb3])
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inl 1)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb4])
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inl 2)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb5])
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inr 0)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb6])
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inr 1)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb7])
      | (change BitMachineStackEmbedding.bank serSlots S3 _ (serSlots (.inr 2)) = _
         rw [BitMachineStackEmbedding.bank_at]
         simp [BitMachineBankSerialize.contents, serSlots, hb8])
  have hser' : ((advance serProgram)^[d])
      (⟨some (.emit 0), none, S3⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update S 8 (bytes x y z)⟩ := by
    change ((advance serProgram)^[d])
      (⟨some (.emit 0), none, BitMachineStackEmbedding.bank serSlots S3 cs.stk⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, BitMachineStackEmbedding.bank serSlots S3
        (BitMachineBankSerialize.contents (fun _ : Fin 3 => []) [] [] (bytes x y z))⟩ at hser
    rw [hbank, hout] at hser
    exact hser
  obtain ⟨ab, hab, hcab⟩ := BitMachineRawSequence.runs (copyProgram 0) (copyProgram 1)
    .scan .scan none none none none S S1 S2 a b hca hcb
  obtain ⟨abc, habc, hcabc⟩ := BitMachineRawSequence.runs p01 (copyProgram 2)
    (BitMachineRawSequence.leftLabel .scan) .scan (none, none) (none, none) none none
    S S2 S3 ab c hcab hcc
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs p012 serProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) (.emit 0)
    ((none, none), none) ((none, none), none) none none S S3
    (Function.update S 8 (bytes x y z)) abc d hcabc hser'
  have hlen : (bytes x y z).length = 2 * (x.length + y.length + z.length) + 3 := by
    simp [bytes, words, BitMachineBankCodec.encode_length, Fin.sum_univ_succ, Nat.add_assoc]
  refine ⟨t, by rw [hbytes] at hd; omega, ?_⟩
  simpa only [program, entry, initial, p012, p01] using hr

end CurrentAdditive.V40ThreeFieldPacket
