import YM.Integration.WilsonPositionScaleLawGuardPoly

/-! Central complex evaluation on the original noncommuting field operators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardEval
open Finset PowerSeries
open WilsonPositionScaleLawGuardPoly
open scoped Polynomial Classical BigOperators
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

def evaluation (z:ℂ):R[X]→+R where
  toFun p:=value p z
  map_zero':=Polynomial.eval₂_zero _ _
  map_add' _ _:=Polynomial.eval₂_add _ _

theorem scalar (p:ℂ[X])(z:ℂ):value (p.map (algebraMap ℂ R)) z=algebraMap ℂ R (p.eval z):=by
  induction p using Polynomial.induction_on' with
  | add p u hp hu=>
    rw [Polynomial.map_add,show value (p.map (algebraMap ℂ R)+u.map (algebraMap ℂ R)) z=
      value (p.map (algebraMap ℂ R)) z+value (u.map (algebraMap ℂ R)) z from map_add (evaluation z) _ _,
      Polynomial.eval_add,map_add,hp,hu]
  | monomial n a=>
    rw [Polynomial.map_monomial,value,Polynomial.eval₂_monomial,Polynomial.eval_monomial,map_mul,map_pow];rfl

theorem printed (q:ℕ)(A:PowerSeries R)(z:ℂ):
    value (trunc (q+1) A) z=∑j∈Finset.Iic q,z^j • coeff j A:=by
  rw [WilsonPositionScaleLawGuardPoly.read]
  have sub:(trunc (q+1) A).support⊆Finset.Iic q:=by
    intro j hj
    apply Finset.mem_Iic.mpr
    by_contra! h
    apply Polynomial.mem_support_iff.mp hj
    rw [coeff_trunc,if_neg (by omega)]
  calc
    _=∑j∈Finset.Iic q,z^j • (trunc (q+1) A).coeff j:=by
      apply Finset.sum_subset sub;intro j _ hj
      rw [Polynomial.notMem_support_iff.mp hj,smul_zero]
    _=_:=by
      apply Finset.sum_congr rfl;intro j hj
      rw [coeff_trunc,if_pos (by have he:=Finset.mem_Iic.mp hj;omega)]

omit [NormedAlgebra ℂ R] in
theorem power {q:ℕ}{p:R[X]}{A:PowerSeries R}(h:Same q p A)(j:ℕ):Same q (p^j) (A^j):=by
  induction j with
  | zero=>intro k _;by_cases e:k=0
          · subst k;simp
          · simp [e]
            change (Polynomial.C (1:R)).coeff k=0
            rw [Polynomial.coeff_C];simp [e]
  | succ j ih=>simpa only [pow_succ] using product ih h

end YM.Integration.WilsonPositionScaleLawGuardEval
