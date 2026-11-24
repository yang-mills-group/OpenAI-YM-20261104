import Mathlib.Analysis.Complex.Basic
/-! Reuse the actual algebra for this budget and the norm scaling pricing
from `Integration/WilsonThermometerWeakPair{Triangle,Budget,Residual}`,
rather than importing the other compact-fork chain. -/
namespace YM.OPE.Logged.Weak
open Function Finset
open scoped Classical BigOperators
variable {I J:Type}
theorem account (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ):
    ‖X-∑u∈i,c u*Y u‖ ≤ ‖X-∑w∈j,A w*v w‖+
        ∑w∈j,‖A w-∑u∈i,c u*B u w‖*‖v w‖+
        ∑u∈i,‖c u‖*‖Y u-∑w∈j,B u w*v w‖:=by
  have transfer : ∑w∈j,∑u∈i,c u*B u w*v w = ∑u∈i,∑w∈j,c u*(B u w*v w):= by
    rw [sum_comm];simp only [mul_assoc]
  have amount:X-∑u∈i,c u*Y u=(X-∑w∈j,A w*v w)+
      (∑w∈j,(A w-∑u∈i,c u*B u w)*v w)-(∑u∈i,c u*(Y u-∑w∈j,B u w*v w)):=by
    simp_rw [sub_mul,mul_sub,sum_sub_distrib,sum_mul,mul_sum];rw [transfer];ring
  rw [amount]
  calc
    _≤(‖X-∑w∈j,A w*v w‖+‖∑w∈j,(A w-∑u∈i,c u*B u w)*v w‖)+
          ‖∑u∈i,c u*(Y u-∑w∈j,B u w*v w)‖:=
      (norm_sub_le ..).trans (add_le_add (norm_add_le ..) (le_refl _))
    _≤_:=by
      have left:=norm_sum_le j (fun w=>(A w-∑u∈i,c u*B u w)*v w)
      have right:=norm_sum_le i (fun u=>c u*(Y u-∑w∈j,B u w*v w))
      simp only [norm_mul] at left right
      exact add_le_add (add_le_add (le_refl _) left) right

theorem product {r t c e B K:ℝ}{d m w:ℕ}(hr:0<r)(rt:r≤t)(en:0≤e)(bn:0≤B)
    (kn:0≤K)(before:r^d*c≤B*r^w)(after:t^(w+m)*e≤K*t):
    (r^d*t^m)*(c*e)≤(B*K)*t:=by
  have ht:=hr.trans_le rt
  have positive:=pow_pos ht w
  apply le_of_mul_le_mul_left _ positive
  calc
    t^w*((r^d*t^m)*(c*e))=(r^d*c)*(t^(w+m)*e):=by rw [pow_add];ring
    _≤(B*r^w)*(K*t):=mul_le_mul before after (mul_nonneg (pow_nonneg ht.le _) en)
        (mul_nonneg bn (pow_nonneg hr.le _))
    _≤(B*t^w)*(K*t):=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le rt _) bn) (mul_nonneg kn ht.le)
    _=t^w*((B*K)*t):=by ring

theorem benefit (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ)
    {W b q t:ℝ}(wp:0≤W)(bp:0≤b)(qp:0≤q)(tp:0≤t)
    (full:W*‖X-∑w∈j,A w*v w‖≤b*t)
    (outer:∀w∈j,W*‖A w-∑u∈i,c u*B u w‖≤b*q)
    (inner:∀u∈i,W*(‖c u‖*‖Y u-∑w∈j,B u w*v w‖)≤b*t):
    W*‖X-∑u∈i,c u*Y u‖ ≤ (1+(∑w∈j,‖v w‖)+i.card)*b*(t+q):=by
  have debt:=mul_le_mul_of_nonneg_left (account i j X Y c A v B) wp
  rw [mul_add,mul_add,mul_sum,mul_sum] at debt
  have D:∀w∈j,W*(‖A w-∑u∈i,c u*B u w‖*‖v w‖)≤(b*q)*‖v w‖:=fun w hw=>by
    rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (outer w hw) (norm_nonneg _)
  have h:=debt.trans (add_le_add (add_le_add full (sum_le_sum D)) (sum_le_sum inner))
  rw [←mul_sum,sum_const,nsmul_eq_mul] at h
  have nn:0≤∑w∈j,‖v w‖:=sum_nonneg (fun w _=>norm_nonneg _)
  have tq:t≤t+q:=le_add_of_nonneg_right qp
  have qt:q≤t+q:=le_add_of_nonneg_left tp
  calc
    _≤_:=h
    _≤b*(t+q)+(b*(t+q))*(∑w∈j,‖v w‖)+(i.card:ℝ)*(b*(t+q)):=by gcongr
    _=_:=by ring


end YM.OPE.Logged.Weak
