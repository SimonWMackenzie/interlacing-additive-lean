import CurrentAdditive.GaussConcreteGridClock
import CurrentAdditive.GaussFetchPolynomial64

namespace CurrentAdditive.GaussConcreteGridPolynomial
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open GaussCellInitialClock

def invocation (M : BitMachine.Machine) (n T : Nat) : Nat :=
  (2*n+2)+T+(2*(n+T*M.pushBound)+2)+
  (M.stackCount*(n+T*M.pushBound)+M.stackCount+2)+3

theorem invocation_eq (M : BitMachine.Machine) (word : List Bool) (T : Nat) :
    MachineInvokeFull.uniformBound M word T=invocation M word.length T := rfl

def frame (n : Nat) : Nat := invocation V2FieldContext.W n
  ((UnaryBinaryEncoding.coefficient+7)*(n+1)^2)

theorem frame_eq (word : List Bool) : V2FieldContext.clock word=frame word.length := rfl

theorem frame_mono {a b : Nat} (h : a≤b) : frame a≤frame b := by
  unfold frame invocation
  gcongr

def header (n : Nat) : Nat := invocation GaussCountHeader.W n
  ((UnaryBinaryEncoding.coefficient+7)*(n+1)^2)+(2*n+1)+3

theorem header_le (n : Nat) : GaussCountHeader.clock n≤header n := by
  have h := EncodedGraph.natField_length_upper n
  unfold GaussCountHeader.clock header
  rw [invocation_eq]
  simp only [List.length_replicate]
  omega

theorem header_mono {a b : Nat} (h : a≤b) : header a≤header b := by
  unfold header invocation
  gcongr

def request (n : Nat) : Nat := GaussFetchPolynomial64.coefficient*(3*n+2)^3+
  (2*n+5)+2*packetCap n+4

theorem request_le (n : Nat) : requestCap n n≤request n := by
  have h := GaussFetchPolynomial64.fourBound_polynomial (n+n+1) n
  unfold requestCap request
  convert Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right h (2*n+5)) (2*packetCap n)) 4 using 1 <;> ring

def raw (n : Nat) : Nat := (14*n+30)+request n+invocationCap n+
  (52*(n+n+1+request n*GaussRequestGrowth64.requestPush)+54)+3

theorem raw_le (n : Nat) : rawCap n n≤raw n := by
  have h := request_le n
  unfold rawCap raw
  gcongr

def cell (n : Nat) : Nat := raw n+4*answerCap n+frame (answerCap n)+10

theorem cell_le (n : Nat) : framedCap n n≤cell n := by
  have h := raw_le n
  unfold framedCap cell
  rw [frame_eq]
  simp only [List.length_replicate]
  omega

def cellBytes (n : Nat) : Nat := 3*answerCap n+1
def rowValues (n : Nat) : Nat := n*n*cellBytes n
def rowBytes (n : Nat) : Nat := (2*n+1)+n*rowValues n

theorem entry_le_dataCap {m k : Nat} (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))).length≤
      GaussConcreteCellEntry.dataCap B := by
  have h1 := Finset.single_le_sum (f := fun j : Fin k =>
    (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i : Fin m => ∑ j : Fin k,
    (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  dsimp only at h1 h2
  unfold GaussConcreteCellEntry.dataCap
  omega

theorem cell_value_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) (x y : Nat) :
    (GaussConcreteCellEntry.value B r pivot c x y).length≤
      cellBytes (GaussConcreteCellEntry.dataCap B) := by
  by_cases hx : x < m
  · by_cases hy : y < k
    · have ha := answer_length_le B r pivot ⟨x,hx⟩ c ⟨y,hy⟩ hn
        (GaussConcreteCellEntry.dataCap B) (entry_le_dataCap B)
      have hh := EncodedGraph.natField_length_upper
        (GaussFramedCell.answer B r pivot ⟨x,hx⟩ c ⟨y,hy⟩).length
      simp only [GaussConcreteCellEntry.value,hx,hy,↓reduceDIte,V2FieldContext.field,
        List.length_append]
      unfold cellBytes
      omega
    · simp [GaussConcreteCellEntry.value,hy]
  · simp [GaussConcreteCellEntry.value,hx]

theorem row_values_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussConcreteRowClock.valueCap B r pivot c≤rowValues (GaussConcreteCellEntry.dataCap B) := by
  let n := GaussConcreteCellEntry.dataCap B
  have hm : m≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hk : k≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) (_ : j∈Finset.univ) =>
      cell_value_le B r pivot c hn i.val j.val))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hs
  dsimp only [n] at *
  apply hs.trans
  unfold rowValues
  calc
    m*(k*cellBytes (GaussConcreteCellEntry.dataCap B))≤
        GaussConcreteCellEntry.dataCap B*(GaussConcreteCellEntry.dataCap B*cellBytes (GaussConcreteCellEntry.dataCap B)) :=
      Nat.mul_le_mul hm (Nat.mul_le_mul_right _ hk)
    _ = _ := by ring

theorem row_bytes_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussConcreteRowClock.rowCap B r pivot c≤rowBytes (GaussConcreteCellEntry.dataCap B) := by
  let n := GaussConcreteCellEntry.dataCap B
  have hk : k≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hh := (EncodedGraph.natField_length_upper k).trans (show 2*k+1≤2*n+1 by omega)
  have hv := row_values_le B r pivot c hn
  dsimp only [n] at *
  unfold GaussConcreteRowClock.rowCap rowBytes
  gcongr

def row (n : Nat) : Nat := header n+
  GaussWordRowTraversal.writerBound n (cell n) (rowValues n)+(2*n+1)+
  4*rowBytes n+frame (rowBytes n)+11

theorem row_clock_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussConcreteRowClock.clock B r pivot c≤row (GaussConcreteCellEntry.dataCap B) := by
  let n := GaussConcreteCellEntry.dataCap B
  have hk : k≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hh := (header_le k).trans (header_mono hk)
  have hf := (EncodedGraph.natField_length_upper k).trans (show 2*k+1≤2*n+1 by omega)
  have hc := cell_le n
  have hv := row_values_le B r pivot c hn
  have hb := row_bytes_le B r pivot c hn
  have hw : GaussWordRowTraversal.writerBound k (GaussConcreteRowClock.cellClock B)
      (GaussConcreteRowClock.valueCap B r pivot c)≤
      GaussWordRowTraversal.writerBound n (cell n) (rowValues n) := by
    unfold GaussWordRowTraversal.writerBound GaussConcreteRowClock.cellClock
    gcongr
  have hframe := frame_mono hb
  dsimp only [n] at *
  unfold GaussConcreteRowClock.clock row
  rw [frame_eq]
  simp only [List.length_replicate]
  omega

def gridValues (n : Nat) : Nat := n*(3*rowBytes n+1)

theorem grid_values_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussConcreteGridClock.valueCap B r pivot c≤gridValues (GaussConcreteCellEntry.dataCap B) := by
  let n := GaussConcreteCellEntry.dataCap B
  have hm : m≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hlen (i : Fin m) : (GaussConcreteGrid.value B r pivot c i.val 0).length≤3*rowBytes n+1 := by
    have hr := (GaussConcreteRowClock.rowBits_length_le B r pivot c i.val).trans
      (row_bytes_le B r pivot c hn)
    have hh := EncodedGraph.natField_length_upper (GaussConcreteRow.rowBits B r pivot c i.val).length
    dsimp only [n] at *
    simp only [GaussConcreteGrid.value,i.isLt,Nat.zero_lt_one,and_self,↓reduceIte,
      V2FieldContext.field,List.length_append]
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i∈Finset.univ) => hlen i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hs
  dsimp only [n] at *
  exact hs.trans (Nat.mul_le_mul_right _ hm)

def clock (n : Nat) : Nat := header n+
  GaussWordGridTraversal.writerBound n 1 (row n) (gridValues n)+(2*n+1)+1

theorem grid_clock_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussConcreteGridClock.clock B r pivot c≤clock (GaussConcreteCellEntry.dataCap B) := by
  let n := GaussConcreteCellEntry.dataCap B
  have hm : m≤n := by dsimp [n,GaussConcreteCellEntry.dataCap]; omega
  have hh := (header_le m).trans (header_mono hm)
  have hf := (EncodedGraph.natField_length_upper m).trans (show 2*m+1≤2*n+1 by omega)
  have hr := row_clock_le B r pivot c hn
  have hv := grid_values_le B r pivot c hn
  have hw : GaussWordGridTraversal.writerBound m 1 (GaussConcreteRowClock.clock B r pivot c)
      (GaussConcreteGridClock.valueCap B r pivot c)≤
      GaussWordGridTraversal.writerBound n 1 (row n) (gridValues n) := by
    unfold GaussWordGridTraversal.writerBound
    gcongr
  dsimp only [n] at *
  unfold GaussConcreteGridClock.clock clock
  omega

#print axioms grid_clock_le
end
end CurrentAdditive.GaussConcreteGridPolynomial
