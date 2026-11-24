import YM.Integration.WilsonPositionScaleLawGuardEval

/-! Evaluate the genuine rooted scalar substitution inside a noncommuting
truncated field guard. The polynomial overflow is completely calculated. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardSubstitute
open Finset PowerSeries MS.Book.Program
open WilsonPositionScaleLawGuardPoly (Same value mass)
open WilsonPositionScaleLawGuardEval (evaluation printed)
open scoped Polynomial Classical BigOperators
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

def composed (q:ℕ)(p:ℂ[X])(A:PowerSeries R):R[X]:=
  ∑j∈Finset.Iic q,(p^j).map (algebraMap ℂ R)*Polynomial.C (coeff j A)

def system (ψ:PowerSeries ℂ)(A:PowerSeries R):PowerSeries R:=
  PowerSeries.mk (MS.Book.Program.substitute ψ (fun j=>coeff j A))

theorem printedAt (q:ℕ)(p:ℂ[X])(A:PowerSeries R)(z:ℂ):
    value (composed q p A) z=value (trunc (q+1) A) (p.eval z):=by
  change (evaluation z) (∑j∈Finset.Iic q,(p^j).map (algebraMap ℂ R)*Polynomial.C (coeff j A))=_
  rw [map_sum,printed]
  apply Finset.sum_congr rfl;intro j _
  change value ((p^j).map (algebraMap ℂ R)*Polynomial.C (coeff j A)) z=_
  rw [WilsonPositionScaleLawGuardPoly.multiply,WilsonPositionScaleLawGuardEval.scalar,Polynomial.eval_pow]
  simp only [value,Polynomial.eval₂_C,RingHom.id_apply,Algebra.smul_def]

theorem issued {q:ℕ}{p:ℂ[X]}{ψ:PowerSeries ℂ}(h:Same q p ψ)(root:Rooted ψ)(A:PowerSeries R):
    Same q (composed q p A) (system ψ A):=by
  intro k hk
  rw [composed,Polynomial.finsetSum_coeff,system,coeff_mk,larger root hk]
  apply Finset.sum_congr rfl;intro j _
  rw [Polynomial.coeff_mul_C,Polynomial.coeff_map,WilsonPositionScaleLawGuardEval.power h j k hk]
  rw [Algebra.smul_def]

theorem cost (q:ℕ)(ψ:PowerSeries ℂ)(root:Rooted ψ)(A:PowerSeries R){z:ℂ}(hz:‖z‖≤1):
    ‖value (trunc (q+1) A) ((trunc (q+1) ψ).eval z)-value (trunc (q+1) (system ψ A)) z‖≤
    ‖z‖^(q+1)*mass (composed q (trunc (q+1) ψ) A-trunc (q+1) (system ψ A)):=by
  rw [←printedAt]
  exact WilsonPositionScaleLawGuardPoly.cost (issued (WilsonPositionScaleLawGuardPoly.issued q ψ) root A)
    (WilsonPositionScaleLawGuardPoly.issued q _) hz

end YM.Integration.WilsonPositionScaleLawGuardSubstitute
