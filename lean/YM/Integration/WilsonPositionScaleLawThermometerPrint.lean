import YM.Integration.WilsonPositionScaleLawThermometerChart

/-! Exact finite products of the seven published ordinary coefficients. The
excess degree of this cubic is controlled by a printed absolute coefficient sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerPrint
open Finset PowerSeries XSpace XSpace.Rose
open scoped BigOperators Classical Polynomial

def cubic {A:Type*}[Ring A](p:Badge→A):A:=
  p univ-(p {0,1}*p {2}+p {0,2}*p {1}+p {1,2}*p {0})+2*(p {0}*p {1}*p {2})

def Same(q:ℕ)(p:ℂ[X])(a:PowerSeries ℂ):Prop:=∀k≤q,p.coeff k=coeff k a

private theorem add {q:ℕ}{p z:ℂ[X]}{a b:PowerSeries ℂ}(h:Same q p a)(g:Same q z b):Same q (p+z) (a+b):=by
  intro k hk;rw [Polynomial.coeff_add,map_add,h k hk,g k hk]

private theorem sub {q:ℕ}{p z:ℂ[X]}{a b:PowerSeries ℂ}(h:Same q p a)(g:Same q z b):Same q (p-z) (a-b):=by
  intro k hk;rw [Polynomial.coeff_sub,map_sub,h k hk,g k hk]

private theorem mul {q:ℕ}{p z:ℂ[X]}{a b:PowerSeries ℂ}(h:Same q p a)(g:Same q z b):Same q (p*z) (a*b):=by
  intro k hk;rw [Polynomial.coeff_mul,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl;intro i hi
  have e:=Finset.mem_range.mp hi
  rw [h _ (by omega),g _ (by omega)]

variable (q:ℕ)(a:Badge→PowerSeries ℂ)
def printed:ℂ[X]:=cubic (fun s=>trunc (q+1) (a s))

theorem present:Same q (printed q a) (b3 a):=by
  have slot (s:Badge):Same q (trunc (q+1) (a s)) (a s):=by
    intro k hk;rw [coeff_trunc,if_pos (by omega)]
  have face:=add (add (mul (slot {0,1}) (slot {2})) (mul (slot {0,2}) (slot {1}))) (mul (slot {1,2}) (slot {0}))
  have triple:=mul (mul (slot {0}) (slot {1})) (slot {2})
  unfold printed cubic b3
  rw [two_mul,two_smul]
  exact add (sub (slot univ) face) (add triple triple)

def fringe:ℂ[X]:=printed q a-trunc (q+1) (b3 a)
def mass:ℝ:=∑k∈(fringe q a).support,‖(fringe q a).coeff k‖

theorem low {k:ℕ}(hk:k≤q):(fringe q a).coeff k=0:=by
  rw [fringe,Polynomial.coeff_sub,coeff_trunc,if_pos (by omega),present q a k hk,sub_self]

theorem evaluated (u:ℂ):WilsonPositionThermometerConnected.value (fun s=>(trunc (q+1) (a s)).eval u)=
    (printed q a).eval u:=by
  simp only [printed,cubic,WilsonPositionThermometerConnected.value,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_ofNat]

theorem cost {u:ℂ}(hu:‖u‖≤1):
    ‖WilsonPositionThermometerConnected.value (fun s=>(trunc (q+1) (a s)).eval u)-(trunc (q+1) (b3 a)).eval u‖≤
      ‖u‖^(q+1)*mass q a:=by
  rw [evaluated,←Polynomial.eval_sub]
  change ‖(fringe q a).eval u‖≤_
  rw [Polynomial.eval_eq_sum]
  calc _≤∑k∈(fringe q a).support,‖(fringe q a).coeff k*u^k‖:=norm_sum_le _ _
       _≤∑k∈(fringe q a).support,‖u‖^(q+1)*‖(fringe q a).coeff k‖:=by
          apply Finset.sum_le_sum;intro k hk
          have nz:=Polynomial.mem_support_iff.mp hk
          have hk':q<k:=by by_contra! h;exact nz (low q a h)
          rw [norm_mul,norm_pow,mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hu (by omega)) (norm_nonneg _)
       _=‖u‖^(q+1)*mass q a:=(Finset.mul_sum ..).symm

end YM.Integration.WilsonPositionScaleLawThermometerPrint
end
