import YM.Integration.WilsonOriginalObservedRoseProgram
import Mathlib.RingTheory.PowerSeries.Trunc

/-! A finite thermal reading of ordinary faces incurs a real, explicitly
computable price when it is regrouped as the connected Taylor polynomial.
It starts beyond the last retained coefficient. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseTruncatedFaces
open Finset PowerSeries XSpace XSpace.Rose
open WilsonPositionThermometerConnected (value)
open scoped Classical BigOperators Polynomial
variable (F:Badge→PowerSeries ℂ) (J:ℕ)
def face (s:Badge):Polynomial ℂ:=PowerSeries.trunc (J+1) (F s)
def joined:Polynomial ℂ:=
  let a:=face F J
  a univ-(a {0,1}*a {2}+a {0,2}*a {1}+a {1,2}*a {0})+(2:ℂ) • (a {0}*a {1}*a {2})
def excess:Polynomial ℂ:=joined F J-PowerSeries.trunc (J+1) (Rose.b3 F)
def fee:ℝ:=∑i∈(excess F J).support,‖(excess F J).coeff i‖

private theorem triple (a b c:PowerSeries ℂ)(n:ℕ):
    trunc n (((trunc n a:PowerSeries ℂ) * (trunc n b:PowerSeries ℂ))*(trunc n c:PowerSeries ℂ))=trunc n (a*b*c):=by
  rw [trunc_mul_trunc,←trunc_trunc_mul ((trunc n a:PowerSeries ℂ) * (trunc n b:PowerSeries ℂ)) c,
    trunc_trunc_mul_trunc,trunc_trunc_mul]

theorem grades:PowerSeries.trunc (J+1) (joined F J:PowerSeries ℂ)=PowerSeries.trunc (J+1) (Rose.b3 F):=by
  unfold joined face Rose.b3
  simp only [Polynomial.coe_add,Polynomial.coe_sub,Polynomial.coe_mul,Polynomial.coe_smul,map_add,map_sub,map_smul,
    triple,trunc_trunc_mul_trunc,trunc_trunc]

theorem initial (e:ℕ)(h:e≤J):(excess F J).coeff e=0:=by
  have earlier:=congrArg (fun a:Polynomial ℂ=>a.coeff e) (grades F J)
  rw [coeff_trunc,if_pos (by omega),Polynomial.coeff_coe] at earlier
  exact sub_eq_zero.mpr earlier

theorem signed (g:ℂ):value (fun s=>(face F J s).eval g)-(PowerSeries.trunc (J+1) (Rose.b3 F)).eval g=
    (excess F J).eval g:=by
  simp only [excess,joined,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_smul,
    smul_eq_mul,value]

theorem price (g:ℂ)(hg:‖g‖≤1):
    ‖value (fun s=>(face F J s).eval g)-(PowerSeries.trunc (J+1) (Rose.b3 F)).eval g‖≤
      fee F J*‖g‖^(J+1):=by
  rw [signed,Polynomial.eval_eq_sum,Polynomial.sum_def,fee,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i hi
  have high : J+1 ≤ i := by
    by_contra! low
    exact (Polynomial.mem_support_iff.mp hi) (initial F J i (by omega))
  rw [norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) hg high) (norm_nonneg _)

end YM.Integration.WilsonOriginalObservedRoseTruncatedFaces
