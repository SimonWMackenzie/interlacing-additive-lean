import EthInapproximability.CurrentPaper.SourceValidHeaderUnique
import EthInapproximability.CurrentPaper.SourceCSPValidatorPolynomial

namespace EthInapproximability.CurrentPaper.SourceValidAcceptance

open Turing BitMachineEncoding
open scoped Classical

theorem canonical_rows_read {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    SourceCSPCodec.readFn
      (SourceCSPCodec.readRow P.vertices a q) P.constraints
      (SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceCSPCodec.rowsOf P)) =
      some (SourceCSPCodec.rowsOf P, []) := by
  simpa only [List.append_nil] using
    SourceCSPCodec.readFn_append SourceCSPCodec.rowFields
      (SourceCSPCodec.readRow P.vertices a q)
      SourceCSPCodec.readRow_append P.constraints
      (SourceCSPCodec.rowsOf P) []

theorem accepted_halt {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ ta vr Sa,
      ta ≤ SourceCSPValidatorPolynomial.majorantCoefficient a q *
        ((EncodedETHSource.constraintBits P).length + 1)^3 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[ta])
        (SourceCSPGlobalDecisionProgram.initial a q
          (EncodedETHSource.constraintBits P)) =
        ⟨none, .row (vr, some true), Sa⟩ := by
  let input := EncodedETHSource.constraintBits P
  obtain ⟨tp, vp, Sp, htp, hrp, hpositive⟩ :=
    SourceCSPGlobalPositiveRows.raw_positive_rows a q input
  obtain ⟨tc, vc, Sc, htc, hrc, hvc⟩ := combined_positive P hn
  have hvp : vp.2.2 = some .positive :=
    positive_route_unique a q input tc tp vc vp Sc Sp hrc hvc hrp
  obtain ⟨n, m, rest, hinput, hbody⟩ := hpositive hvp
  obtain ⟨hnEq, hmEq, hrestEq⟩ :=
    canonical_header_unique P n m rest hinput
  subst n
  subst m
  subst rest
  obtain ⟨t, S, vr, b, ht, hr, hb, _, _⟩ :=
    hbody ⟨hn, hsize⟩
  have hbtrue : b = true :=
    hb.mpr ⟨SourceCSPCodec.rowsOf P, canonical_rows_read P⟩
  subst b
  have hterminal :
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t + 2])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩ := by
    rw [show t + 2 = 1 + (1 + t) by omega,
      Function.iterate_add_apply,
      show 1 + t = 1 + t by rfl,
      Function.iterate_add_apply, hr]
    rw [Function.iterate_one,
      SourceCSPGlobalDecisionProgram.after_row_success]
    exact SourceCSPGlobalTotalValidation.accept_one_step_halt a q vr S
  have hrowBound : t ≤
      SourceCSPGlobalPositiveRows.physicalRowBound a q input.length := ht
  have htotal : t + 2 ≤
      SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 := by
    let row := SourceCSPGlobalPositiveRows.physicalRowBound a q input.length
    let p := BitMachineStackGrowth.perStep
      (SourceCSPGlobalDecisionProgram.program a q)
    have hscaled : row ≤ (1+p)*row := by
      nlinarith [Nat.zero_le p, Nat.zero_le row]
    have hterm : t + 2 ≤ (1+p)*row+4 := by omega
    have hmax : (1+p)*row+4 ≤
        SourceCSPGlobalTotalValidation.totalBound a q input.length := by
      unfold SourceCSPGlobalTotalValidation.totalBound
      exact (le_max_right _ _).trans (le_max_right _ _)
    omega
  have hpoly := SourceCSPValidatorPolynomial.totalBound_le_cubic
    a q input.length
  exact ⟨t + 2, vr, S, htotal.trans hpoly, hterminal⟩

#print axioms canonical_rows_read
#print axioms accepted_halt

end EthInapproximability.CurrentPaper.SourceValidAcceptance
