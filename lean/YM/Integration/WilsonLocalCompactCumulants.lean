import YM.Integration.WilsonLocalCompactProbability

/-! Connected changes of normalized compact expectations, with prices
expressed solely in the fluctuations of the original law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactCumulants
open MeasureTheory Lattice RG Wilson
open WilsonLocalCompactProbability
open scoped Classical Topology
variable {G:Gauge} {n:Side}
variable (P A:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ) (p:P 1=1) (a:A 1=1) {τ:ℝ}
variable (paid:∀F,|A F-P F|≤τ*spread P F)

include p paid in
theorem single (F:Signal (G:=G) (n:=n)):
    |A (center P F)|≤τ*spread P F:=by
  have z:=zero P p F
  have cost:=paid (center P F)
  rw [z,sub_zero] at cost
  have same:center P (center P F)=center P F:=by
    change center P F-P (center P F) • 1=center P F
    rw [z,zero_smul,sub_zero]
  change _≤τ*P (absolute (center P (center P F))) at cost
  rw [same] at cost;exact cost

include paid in
theorem upper (F:Signal (G:=G) (n:=n)):
    |A F|≤|P F|+τ*spread P F:=by
  calc |A F|=|P F+(A F-P F)|:=by congr 1;ring
       _≤|P F|+|A F-P F|:=abs_add_le .. 
       _≤_:=add_le_add le_rfl (paid F)

include p a paid in
theorem two (F H:Signal (G:=G) (n:=n)):
    let f:=center P F;let h:=center P H
    |covariance A F H-covariance P F H|≤
       τ*spread P (f*h)+(τ*spread P F)*(τ*spread P H):=by
  intro f h
  have pf:P f=0:=zero P p F;have ph:P h=0:=zero P p H
  have af:=single P A p paid F;have ah:=single P A p paid H
  have change_:covariance A F H-covariance P F H=(A (f*h)-P (f*h))-A f*A h:=by
    rw [←translated A a F H (P F) (P H),←translated P p F H (P F) (P H)]
    change (A (f*h)-A f*A h)-(P (f*h)-P f*P h)=_
    rw [pf,zero_mul,sub_zero];ring
  rw [change_]
  refine (abs_sub ..).trans (add_le_add (paid _) ?_)
  rw [abs_mul]
  exact mul_le_mul af ah (abs_nonneg _) ((abs_nonneg _).trans af)

private theorem five (u v w x y:ℝ):
    |u-v-w-x+y|≤|u|+|v|+|w|+|x|+|y|:=by
  linarith only [abs_sub u v,abs_sub (u-v) w,abs_sub (u-v-w) x,abs_add_le (u-v-w-x) y]

include p a paid in
theorem three (F H J:Signal (G:=G) (n:=n)):
    let f:=center P F;let h:=center P H;let j:=center P J
    let cut:=fun X=>τ*spread P X
    let cap:=fun X=>|P X|+cut X
    |third A F H J-third P F H J|≤
      cut (f*h*j)+cut F*cap (h*j)+cut H*cap (f*j)+cut J*cap (f*h)+2*cut F*cut H*cut J:=by
  intro f h j cut cap
  have pf:P f=0:=zero P p F;have ph:P h=0:=zero P p H;have pj:P j=0:=zero P p J
  have af:|A f|≤cut F:=single P A p paid F
  have ah:|A h|≤cut H:=single P A p paid H
  have aj:|A j|≤cut J:=single P A p paid J
  have bill (x y:Signal (G:=G) (n:=n)) (c:ℝ) (hx:|A x|≤c):|A x*A y|≤c*cap y:=by
    rw [abs_mul];exact mul_le_mul hx (upper P A paid y) (abs_nonneg _) ((abs_nonneg _).trans hx)
  have triple:|2*A f*A h*A j|≤2*cut F*cut H*cut J:=by
    simp only [abs_mul,abs_of_nonneg (show 0≤(2:ℝ) by norm_num)]
    have cf:0≤cut F:=(abs_nonneg _).trans af
    have ch:0≤cut H:=(abs_nonneg _).trans ah
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left af (by norm_num)) ah (abs_nonneg _)
      (mul_nonneg (by norm_num) cf)) aj (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) cf) ch)
  have same:third A F H J-third P F H J=
      (A (f*h*j)-P (f*h*j))-A f*A (h*j)-A h*A (f*j)-A j*A (f*h)+2*A f*A h*A j:=by
    rw [←translated_three A a F H J (P F) (P H) (P J),←translated_three P p F H J (P F) (P H) (P J)]
    change third A f h j-third P f h j=_
    simp only [third,pf,ph,pj,zero_mul,mul_zero,sub_zero,add_zero];ring
  rw [same]
  exact (five ..).trans (add_le_add (add_le_add (add_le_add (add_le_add (paid _) (bill f _ _ af))
    (bill h _ _ ah)) (bill j _ _ aj)) triple)

end YM.Integration.WilsonLocalCompactCumulants
