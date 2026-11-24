import YM.Integration.WilsonPositionProgramGaussianProductPrice
import YM.Integration.WilsonFiniteOrdinaryTail

/-! The native partition of every ordinary and connected word consumes each marked radius once. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramDisjointWallet
open Finset Multi Marker Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V:Type}[DecidableEq V] {R:Census V}

def table (α:(parts R).Mode→ℂ)(p:Hot R→ℂ)(s:R.Mode):ℂ:=
  ∑u∈shards R s,α u*∏i∈u.val,p i

def salary (α:(parts R).Mode→ℂ)(s:R.Mode):ℝ:=∑u∈shards R s,‖α u‖

def stock (α:(parts R).Mode→ℂ):ℝ:=∑s:R.Mode,salary α s

theorem tariff (α:(parts R).Mode→ℂ)(s:R.Mode):salary α s≤ stock α:=by
  exact single_le_sum (f:=salary α) (fun u _=>by unfold salary;positivity) (mem_univ s)

theorem tallied (w:V→ℝ)(α:(parts R).Mode→ℂ)(p:Hot R→ℂ)(s:R.Mode):
    (Poly.toll w s:ℂ)*table α p s=table α (fun i=>(Poly.toll w i.val:ℂ)*p i) s:=by
  unfold table
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro u hu
  rw [WilsonFiniteOrdinaryTail.toll w s u hu,Complex.ofReal_prod,prod_mul_distrib]
  ring

private theorem value (α:(parts R).Mode→ℂ)(p:Hot R→ℂ)(s:R.Mode){B:ℝ}
    (hb:1≤B)(hp:∀i,‖p i‖≤B):
    ‖table α p s‖ ≤ salary α s*B^(Fintype.card (Hot R)):=by
  unfold table salary
  rw [sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro u _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((WilsonPositionProgramGaussianProductPrice.mass u.val p hp).trans
    (pow_le_pow_right₀ hb (card_le_univ u.val))) (norm_nonneg _)

private theorem signed (α:(parts R).Mode→ℂ)(p q:Hot R→ℂ)(s:R.Mode){B δ:ℝ}
    (hb:1≤B)(hd:0≤δ)(hp:∀i,‖p i‖≤B)(hq:∀i,‖q i‖≤B)(fee:∀i,‖p i-q i‖≤δ):
    ‖table α p s-table α q s‖ ≤ salary α s*((Fintype.card (Hot R):ℝ)*δ*B^(Fintype.card (Hot R))):=by
  unfold table salary
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro u _
  rw [←mul_sub,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (WilsonPositionProgramGaussianProductPrice.change u.val p q hb hd hp hq fee).trans
  have n:=card_le_univ u.val
  exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast n) hd) (pow_le_pow_right₀ hb n)
    (pow_nonneg (zero_le_one.trans hb) _) (by positivity)

theorem common (w:V→ℝ)(hw:∀v,0<w v)(α:(parts R).Mode→ℂ)(p q:Hot R→ℂ)(s:R.Mode){B δ:ℝ}
    (hb:1≤B)(hd:0≤δ)(hp:∀i,Poly.toll w i.val*‖p i‖≤B)
    (hq:∀i,Poly.toll w i.val*‖q i‖≤B)(fee:∀i,Poly.toll w i.val*‖p i-q i‖≤δ):
    Poly.toll w s*‖table α p s‖≤ salary α s*B^(Fintype.card (Hot R)) ∧
    Poly.toll w s*‖table α p s-table α q s‖≤
      salary α s*((Fintype.card (Hot R):ℝ)*δ*B^(Fintype.card (Hot R))):=by
  let weighted (a:Hot R→ℂ)(i:Hot R):ℂ:=(Poly.toll w i.val:ℂ)*a i
  have price(t:R.Mode)(a:ℂ):‖(Poly.toll w t:ℂ)*a‖=Poly.toll w t*‖a‖:=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Poly.worth hw t)]
  have up(i:Hot R):‖weighted p i‖≤B:=(price _ _).le.trans (hp i)
  have down(i:Hot R):‖weighted q i‖≤B:=(price _ _).le.trans (hq i)
  have delta(i:Hot R):‖weighted p i-weighted q i‖≤δ:=by
    unfold weighted
    rw [←mul_sub,price]
    exact fee i
  constructor
  · rw [←price,tallied];exact value α (weighted p) s hb up
  · rw [←price,mul_sub,tallied,tallied];exact signed α (weighted p) (weighted q) s hb hd up down delta

end YM.Integration.WilsonPositionProgramDisjointWallet
end
