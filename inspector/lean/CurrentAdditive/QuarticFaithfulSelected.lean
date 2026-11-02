import CurrentAdditive.QuarticFaithfulGraphSeedMachine
import CurrentAdditive.QuarticEncodedOutput

/-! A private, manuscript-faithful candidate for the v27 selected output.
It has the same public schedule, dimensions, budget, tape type, and fallback
branch as `select27`; only its scheduled table uses per-draw fallback. -/

namespace Paper2.GenericQuarticFaithful

open Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open CurrentAdditive.RandomizedSchedule

def scheduledOutput27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    TotalFiniteConstructorScratch.SelectedOutput :=
  let old := scheduledOutput27 hn edge Δ γ k hc
  { rows := old.rows
    cols := old.cols
    budget := old.budget
    inputBits := old.inputBits
    Tape := old.Tape
    tapeBits := old.tapeBits
    table := fun bits =>
      table27Faithful hn edge (Nat.clog 2 n) Δ γ k hc bits }

def select27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    TotalFiniteConstructorScratch.SelectedOutput :=
  if hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledOutput27Faithful hn edge Δ γ k hc
  else TotalFiniteConstructorScratch.fallbackOutput edge k

theorem select27Faithful_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    select27Faithful hn edge Δ γ k =
      scheduledOutput27Faithful hn edge Δ γ k hc := by
  simp [select27Faithful, hc]

theorem select27Faithful_bad {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    select27Faithful hn edge Δ γ k =
      TotalFiniteConstructorScratch.fallbackOutput edge k := by
  simp [select27Faithful, hc]

def selectedTape27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27Faithful hn edge Δ γ k hc).Tape) :
    (select27Faithful hn edge Δ γ k).Tape :=
  (select27Faithful_good hn edge Δ γ k hc).symm ▸ bits

private theorem table_bits_transport
    {a b : TotalFiniteConstructorScratch.SelectedOutput}
    (h : a = b) (t : b.Tape) :
    (a.table (h.symm ▸ t)).bits = (b.table t).bits := by
  cases h
  rfl

theorem selected_good_table_bits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27Faithful hn edge Δ γ k hc).Tape) :
    ((select27Faithful hn edge Δ γ k).table
      (selectedTape27Faithful hn edge Δ γ k hc bits)).bits =
      (table27Faithful hn edge (Nat.clog 2 n) Δ γ k hc bits).bits := by
  exact table_bits_transport (select27Faithful_good hn edge Δ γ k hc) bits

def outputBits27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27Faithful hn edge Δ γ k).Tape) : List Bool :=
  EncodedCommunication.encodeInstance
    (EncodedSelectedOutput.instanceOf
      ((select27Faithful hn edge Δ γ k).table t)
      (select27Faithful hn edge Δ γ k).budget)

private theorem output_bits_transport
    {a b : TotalFiniteConstructorScratch.SelectedOutput}
    (h : a = b) (t : b.Tape) :
    EncodedCommunication.encodeInstance
      (EncodedSelectedOutput.instanceOf (a.table (h.symm ▸ t)) a.budget) =
    EncodedCommunication.encodeInstance
      (EncodedSelectedOutput.instanceOf (b.table t) b.budget) := by
  cases h
  rfl

theorem selected_good_output_bits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27Faithful hn edge Δ γ k hc).Tape) :
    outputBits27Faithful hn edge Δ γ k
      (selectedTape27Faithful hn edge Δ γ k hc bits) =
      EncodedCommunication.encodeInstance
        (EncodedSelectedOutput.instanceOf
          (table27Faithful hn edge (Nat.clog 2 n) Δ γ k hc bits)
          (scheduledOutput27Faithful hn edge Δ γ k hc).budget) := by
  exact output_bits_transport (select27Faithful_good hn edge Δ γ k hc) bits

#print axioms select27Faithful_good
#print axioms selected_good_table_bits
#print axioms selected_good_output_bits

end Paper2.GenericQuarticFaithful
