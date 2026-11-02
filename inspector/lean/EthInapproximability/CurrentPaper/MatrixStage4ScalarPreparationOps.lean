import EthInapproximability.CurrentPaper.MatrixWeightedPower
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Reusable physical unary operations for prepared Stage--4 scalars

These lemmas embed already-checked literal controllers into selected ambient
Boolean stacks. Their conclusions describe the entire ambient bank, so no
untouched scalar is silently supplied or changed by an arithmetic call.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {K : Type*} [DecidableEq K]

def copyProgram (ι : Fin 3 ↪ K) :
    BitMachineCopy.Label → TM2.Stmt (fun _ : K => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => stackStmt ι (BitMachineCopy.program l)

theorem copy_run (ι : Fin 3 ↪ K) (S : K → List Bool)
    (hempty : S (ι 2) = []) :
    ((advance (copyProgram ι))^[2 * (S (ι 0)).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        Function.update S (ι 1) (S (ι 0) ++ S (ι 1))⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none (S (ι 0)) (S (ι 1)) []
  have hstart : stackCfg ι S c =
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
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
        (S (ι 0) ++ S (ι 1))⟩ : TM2.Cfg (fun _ : K => Bool)
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

def multiplyProgram (ι : Fin 6 ↪ K) :
    MatrixAddressMachine.Label → TM2.Stmt (fun _ : K => Bool)
      MatrixAddressMachine.Label Bool :=
  fun l => stackStmt ι (MatrixAddressMachine.program l)

theorem multiply_run (ι : Fin 6 ↪ K) (S : K → List Bool)
    (r w : ℕ)
    (hr : S (ι 0) = List.replicate r true)
    (hw : S (ι 1) = List.replicate w true)
    (hc : S (ι 2) = []) (hrb : S (ι 3) = [])
    (hwb : S (ι 4) = []) :
    ((advance (multiplyProgram ι))^[MatrixAddressMachine.exactTime r w 0])
      (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : K => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none, false, Function.update S (ι 5)
        (List.replicate (r * w) true ++ S (ι 5))⟩ := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate r true) (List.replicate w true) [] [] [] (S (ι 5))
  have hstart : stackCfg ι S c =
      (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : K => Bool)
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
          TM2.Cfg (fun _ : K => Bool) MatrixAddressMachine.Label Bool) := by
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

def unaryPowerProgram (ι : MatrixUnaryPower.Stack ↪ K) :
    MatrixUnaryPower.Label → TM2.Stmt (fun _ : K => Bool)
      MatrixUnaryPower.Label MatrixUnaryPower.Control :=
  fun l => stackStmt ι (MatrixUnaryPower.program l)

theorem unary_power_run (ι : MatrixUnaryPower.Stack ↪ K)
    (S : K → List Bool) (a : ℕ)
    (ha : S (ι (.inr ())) = List.replicate a true)
    (h0 : S (ι (.inl 0)) = [])
    (h1 : S (ι (.inl 1)) = [])
    (h2 : S (ι (.inl 2)) = []) :
    ∃ t ≤ 4*2^a + 5*a + 7,
      ((advance (unaryPowerProgram ι))^[t])
        (⟨some (.inr false), ((false,false),none), S⟩ :
          TM2.Cfg (fun _ : K => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, ((false,false),none),
          Function.update S (ι (.inl 0)) (List.replicate (2^a) true)⟩ := by
  let c := MatrixUnaryPower.cfg (some (.inr false))
    ((false,false),none) [] [] [] (List.replicate a true)
  have hstart : stackCfg ι S c =
      (⟨some (.inr false), ((false,false),none), S⟩ :
        TM2.Cfg (fun _ : K => Bool)
          MatrixUnaryPower.Label MatrixUnaryPower.Control) := by
    dsimp [stackCfg, c, MatrixUnaryPower.cfg]
    congr 1
    apply bank_eq_self
    intro k
    rcases k with k | k
    · fin_cases k <;> simp [MatrixUnaryPower.contents, MatrixBinaryAddress.stackContents,
        h0, h1, h2]
    · cases k
      simp [MatrixUnaryPower.contents, ha]
  obtain ⟨t, ht, hr⟩ := MatrixUnaryPower.unary_power_run a
  have he := BitMachineStackRun.run ι S MatrixUnaryPower.program c t
  rw [hstart] at he
  change _ = stackCfg ι S (MatrixUnaryPower.run t c) at he
  rw [show c = MatrixUnaryPower.cfg (some (.inr false))
      ((false,false),none) [] [] [] (List.replicate a true) from rfl, hr] at he
  refine ⟨t, ht, he.trans ?_⟩
  dsimp [stackCfg, MatrixUnaryPower.cfg]
  congr 1
  have hloc : MatrixUnaryPower.contents
      (List.replicate (2^a) true) [] [] (List.replicate a true) =
      Function.update (fun k => S (ι k)) (.inl 0)
        (List.replicate (2^a) true) := by
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [MatrixUnaryPower.contents,
        MatrixBinaryAddress.stackContents, h0, h1, h2]
    · cases k
      simp [MatrixUnaryPower.contents, ha]
  rw [hloc, bank_update, bank_restrict]

def weightedPowerProgram (ι : MatrixWeightedPower.Stack ↪ K) :
    MatrixWeightedPower.Label → TM2.Stmt (fun _ : K => Bool)
      MatrixWeightedPower.Label MatrixWeightedPower.Control :=
  fun l => stackStmt ι (MatrixWeightedPower.program l)

theorem weighted_power_run (ι : MatrixWeightedPower.Stack ↪ K)
    (S : K → List Bool) (base exponent : ℕ)
    (hacc : S (ι (.inl 0)) = [true])
    (hbase : S (ι (.inl 1)) = List.replicate base true)
    (h2 : S (ι (.inl 2)) = [])
    (h3 : S (ι (.inl 3)) = [])
    (h4 : S (ι (.inl 4)) = [])
    (h5 : S (ι (.inl 5)) = [])
    (hfuel : S (ι (.inr 0)) = List.replicate exponent true) :
    ∃ t ≤ MatrixWeightedPower.powerBound base exponent,
      ((advance (weightedPowerProgram ι))^[t])
        (⟨some (.inr .test), (false,false), S⟩ :
          TM2.Cfg (fun _ : K => Bool)
            MatrixWeightedPower.Label MatrixWeightedPower.Control) =
        ⟨none, (false,false),
          Function.update
            (Function.update S (ι (.inl 0))
              (List.replicate (base^exponent) true))
            (ι (.inr 0)) []⟩ := by
  let c := MatrixWeightedPower.cfg (some (.inr .test))
    (false,false) [true] (List.replicate base true) []
    (List.replicate exponent true)
  have hstart : stackCfg ι S c =
      (⟨some (.inr .test), (false,false), S⟩ :
        TM2.Cfg (fun _ : K => Bool)
          MatrixWeightedPower.Label MatrixWeightedPower.Control) := by
    dsimp [stackCfg, c, MatrixWeightedPower.cfg]
    congr 1
    apply bank_eq_self
    intro k
    rcases k with k | k
    · fin_cases k <;> simp [MatrixWeightedPower.bank,
        hacc, hbase, h2, h3, h4, h5]
    · fin_cases k
      simp [MatrixWeightedPower.bank, hfuel]
  obtain ⟨t, ht, hr⟩ := MatrixWeightedPower.power_run base exponent
  have he := BitMachineStackRun.run ι S MatrixWeightedPower.program c t
  rw [hstart] at he
  change _ = stackCfg ι S (MatrixWeightedPower.run t c) at he
  simp only [List.replicate_one] at hr
  rw [show c = MatrixWeightedPower.cfg (some (.inr .test))
      (false,false) [true] (List.replicate base true) []
      (List.replicate exponent true) from rfl, hr] at he
  refine ⟨t, ht, he.trans ?_⟩
  dsimp [stackCfg, MatrixWeightedPower.cfg]
  congr 1
  have hloc : Sum.elim
      (MatrixWeightedPower.bank (List.replicate (base^exponent) true)
        (List.replicate base true) []) (fun _ : Fin 1 => []) =
      Function.update
        (Function.update (fun k => S (ι k)) (.inl 0)
          (List.replicate (base^exponent) true)) (.inr 0) [] := by
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [MatrixWeightedPower.bank,
        hacc, hbase, h2, h3, h4, h5]
    · fin_cases k
      simp [MatrixWeightedPower.bank, hfuel]
  rw [hloc, bank_update, bank_update, bank_restrict]

end EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
