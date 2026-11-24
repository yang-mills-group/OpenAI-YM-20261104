import YM.OPE.Compatible.Kyoto.Yank
import YM.OPE.Compatible.Cres.Away
/-!
# Per-patch evaluation with one-station slope. No infinite series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Set Lattice WithLp Real Finset
open scoped Topology BigOperators Classical
open Stroke Hark Pipes
variable {I:Type}{L:Filter I}{V Ω Bf Bc T ε q p:I→ℝ}{ρ S t δ Λ:ℝ}{u:ℕ}
abbrev Reven (K:ℕ)(b f:ℝ):ℝ:= Real.exp (K*(Real.log f-Real.log b))
section book
private lemma transit (p:ℝ) (k:ℕ)(hp:0≤p)(hx:p ≤1)(h:(1-p)^k≥1/2): p*k/2≤1-(1-p)^k:=by
      induction k with
      | zero=>simp
      | succ k ih=>
          have he:0≤1-p:=by linarith only [hx]
          have hz:1-p≤1:=by linarith only [hp]
          have hy:1/2 ≤ (1-p)^k:= h.trans (pow_le_pow_of_le_one he hz (Nat.le_succ _))
          specialize ih hy; rw[Nat.cast_succ,pow_succ]; linarith only [ih,mul_le_mul_of_nonneg_left hy hp]
lemma revenueZ (d:ℕ)(h:0 < t)(ht:Tendsto Bf L atTop)(hz:∀ᶠ i in L,Bf i-Bc i=t): ∀ᶠ i in L,1 ≤ Reven d (Bc i) (Bf i)∧ Bf i*(1-(Reven d (Bc i) (Bf i))⁻¹^ (2:ℕ)) ≥ t*d/2:=by
       have he : Tendsto (fun i=>1-t/Bf i) L (𝓝 1):=by simpa only [sub_zero] using tendsto_const_nhds.sub ((tendsto_const_nhds (x:=t)).div_atTop ht) -- bind
       filter_upwards [ht.eventually_gt_atTop t, hz,(he.pow d).eventually (le_mem_nhds (by norm_num: (1/2:ℝ)<1^d))] with i hi hp hv
       let p:=Bc i; let q:= Bf i
       have ho: 0<p:=by unfold p; linarith
       have hx :0<q:= h.trans hi
       have hK:p<q:=by unfold p q; linarith
       let r:=t/q; have hg:p/q=1-r:=by unfold r; have hΩ:p=q-t:= (by unfold p q; linarith); rw [hΩ]; field_simp
       have hb : r ≤ 1:= (div_le_one hx).mpr hi.le
       let A:=Reven d p q; have hA:1 ≤ A:= Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.mpr ((Real.log_lt_log ho hK).le)))
       have hB: A⁻¹=(1-r)^d:=by unfold A Reven;rw [←hg, ← Real.exp_neg, ← mul_neg,neg_sub,← Real.log_div ho.ne' hx.ne',Real.exp_nat_mul,Real.exp_log (div_pos ho hx)]
       refine ⟨hA,?_⟩; change t*d/2 ≤ q*(1-A⁻¹^2); have hs:=transit r d (div_nonneg h.le hx.le) hb hv; rw[← hB] at hs; have hj : A⁻¹ ^2 ≤ A⁻¹:=by rw[pow_two]; exact mul_le_of_le_one_right (inv_nonneg.mpr (zero_le_one.trans hA)) (inv_le_one_of_one_le₀ hA)
       refine (le_of_eq ?_).trans ((mul_le_mul_of_nonneg_left hs hx.le).trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hj _) hx.le))
       unfold r; field_simp
variable (d r:ℕ)(h:0< t)(hz:∀ᶠ i in L,Bf i-Bc i=t) (ht:Tendsto V L atTop)(hΩ:Tendsto Bf L atTop)(he: RateLE L V Bf 1) (hx:RateLE L V ε (-(1/2))) (hq:∀ᶠ i in L,Bf i* ε i^(2:ℕ) ≤ 2)
include h hz ht hΩ he hx hq
lemma Γslope (hK:RateLE L V p 0)(hS:1 ≤ S) (hp:0 < Λ) (hv:(↑r:ℝ)*S*2 < t*d/2) :∀ᶠ i in L,(r*Λ^2*S* ε i^2+ |ε i|^3*3* p i^2) ≤ Λ^2*(1- (Reven d (Bc i) (Bf i))⁻¹^ (2:ℕ)):=by
       let z(i):= |ε i|^3*3*p i^2; let c:= (t*d/2 - r*S*2)*Λ^2; have hC:0<c:=mul_pos (sub_pos.mpr hv) (pow_pos hp _); have hp' : Tendsto (fun i=> Bf i*z i) L (𝓝 0) := by have hg:z =_:= (show z=fun i=> ‖ε i‖^3*3*p i^2 from rfl); rw [hg]; exact ((he.mul (((hx.norm.pow 3 ht).mul (RateLE.const 3 ht)).mul (hK.pow 2 ht)))).tends (by norm_num) ht
       filter_upwards [revenueZ d h hΩ hz,hq,hΩ.eventually_gt_atTop 0,hp'.eventually (ge_mem_nhds hC)] with i hi hh hx hk; apply le_of_mul_le_mul_left _ hx; unfold c at *; let u:= Reven d (Bc i) (Bf i); change Bf i*z i≤ _ at hk; unfold z at hk
       linarith only [mul_le_mul_of_nonneg_right hi.2 (sq_nonneg Λ), mul_le_mul_of_nonneg_right hh (show 0≤ (r:ℝ)*S*Λ^2 from by positivity), hk] -- z eta
end book
end YM.OPE.Dial
