import YM.Integration.WilsonPositionScaleLawThermometerPrint

/-! Finite central evaluation of noncommuting operator polynomials.
A proved agreement through degree q prices the entire overflow on the unit disk. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardPoly
open Finset PowerSeries
open scoped Polynomial Classical BigOperators
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

def value (p:R[X])(z:ℂ):R:=p.eval₂ (RingHom.id R) (algebraMap ℂ R z)
def mass (p:R[X]):ℝ:=∑k∈p.support,‖p.coeff k‖
def Same (q:ℕ)(p:R[X])(a:PowerSeries R):Prop:=∀k≤q,p.coeff k=coeff k a

theorem multiply (p u:R[X])(z:ℂ):value (p*u) z=value p z*value u z:=
  Polynomial.eval₂_mul_noncomm _ _ fun k=>(Algebra.commutes z (u.coeff k)).symm

theorem subtract (p u:R[X])(z:ℂ):value (p-u) z=value p z-value u z:=
  Polynomial.eval₂_sub _

theorem read (p:R[X])(z:ℂ):value p z=∑k∈p.support,z^k • p.coeff k:=by
  rw [value,Polynomial.eval₂_eq_sum]
  apply Finset.sum_congr rfl;intro k _
  simp only [RingHom.id_apply,Algebra.smul_def,map_pow]
  simpa only [map_pow] using (Algebra.commutes (z^k) (p.coeff k)).symm

omit [NormedAlgebra ℂ R] in
theorem issued (q:ℕ)(a:PowerSeries R):Same q (trunc (q+1) a) a:=by
  intro k hk;rw [coeff_trunc,if_pos (by omega)]

omit [NormedAlgebra ℂ R] in
theorem product {q:ℕ}{p u:R[X]}{a b:PowerSeries R}(h:Same q p a)(j:Same q u b):
    Same q (p*u) (a*b):=by
  intro k hk
  rw [Polynomial.coeff_mul,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl;intro i hi
  have e:=Finset.mem_range.mp hi
  rw [h _ (by omega),j _ (by omega)]

theorem tail {q:ℕ}(p:R[X])(h:∀k≤q,p.coeff k=0){z:ℂ}(hz:‖z‖≤1):
    ‖value p z‖≤‖z‖^(q+1)*mass p:=by
  rw [read]
  calc _≤∑k∈p.support,‖z^k • p.coeff k‖:=norm_sum_le _ _
       _≤∑k∈p.support,‖z‖^(q+1)*‖p.coeff k‖:=by
          apply Finset.sum_le_sum;intro k hk
          have nz:=Polynomial.mem_support_iff.mp hk
          have high:q<k:=by by_contra! e;exact nz (h k e)
          rw [norm_smul,norm_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hz (by omega)) (norm_nonneg _)
       _=_:=(Finset.mul_sum ..).symm

theorem cost {q:ℕ}{p u:R[X]}{a:PowerSeries R}(h:Same q p a)(j:Same q u a){z:ℂ}(hz:‖z‖≤1):
    ‖value p z-value u z‖≤‖z‖^(q+1)*mass (p-u):=by
  rw [←subtract];apply tail _ _ hz
  intro k hk;rw [Polynomial.coeff_sub,h k hk,j k hk,sub_self]

end YM.Integration.WilsonPositionScaleLawGuardPoly
