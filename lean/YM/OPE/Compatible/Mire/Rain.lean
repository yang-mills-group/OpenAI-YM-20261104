import YM.OPE.Compatible.Mire.Ember
/-!
# Angular Mellin = Lap test on even homogeneous
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sagebrush
open Function MeasureTheory Set Topology Metric Filter Lattice Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Extra.FD.OPE
variable {x:E4}{k:ℕ}{f g:E4→ℝ}{s:ℝ}
def countM (s:ℝ)(k:ℕ)(f:E4→ℝ):=∫ x, annA s x*rr x^(k+2)* f x
lemma lid_ice (k:ℕ)(s:ℝ): ContDiff ℝ ∞ (annA s*rr^k):= iceAway _ (fun _ hx=> (rr_smooth hx).pow _)
lemma lid_pay (k:ℕ)(hs:0<s):HasCompactSupport (annA s*rr^k):= HasCompactSupport.mul_right (shipA hs)
lemma bug_turn (hp:PureA (2*k) f)(hs:0<s): (∫ x,bug s (k+1) x*f x)=∫ x, bug 1 (k+1) x*f x:=by
    let g:=fun x=> bug 1 (k+1) x*f x; have hh(x:E4): bug s (k+1) x*f x=s^4*g (s • x):=by unfold g; rw [bug_scale hs,hp.rad,smul_eq_mul,show 2*(k+1+1)=4+2*k from by omega, pow_add]; ring
    simp_rw [hh]; rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume g s (hR:=hs.le), YM.Next.Rank.Radian.spaceD]; change s^4 * ((s^4)⁻¹ * _)= _; rw [←mul_assoc, mul_inv_cancel₀ (by positivity),one_mul]
lemma entry (hp:PureA (2*(k+1)) f)(hs:0<s): countM s k (lap f)= 4*((k:ℝ)+1)*((k:ℝ)+2)*countM s (k+1) f:=by
   let m:=k+1
   have ht:0<s:=hs
   let H:=annA s*rr^(k+2)
   let L:=annA s*rr^(k+3); have he:=lap_self_pay (lid_pay (k+2) hs) hp.smooth (lid_ice (k+2) s)
   change (∫ x,H x*lap f x)=∫ x,lap H x*f x at he
   change (∫ x,H x*lap f x)= _; rw [he]
   let r:=4*((k:ℝ)+1)*(k+2); rw [show lap H=r • L+(bug s (k+2)-bug 1 (k+2)) from by convert! lap_bug s (k+1) using 3; unfold r; push_cast; ring]
   have hy (t)(ht:0<t): Integrable (fun x=>bug t (k+2) x*f x):= coal_fin (box_bug ht) hp.smooth.continuous (silk_bug t _).continuous
   simp_rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply, add_mul,sub_mul, mul_assoc r]
   erw [integral_add ((coal_fin (lid_pay (k+3) hs) hp.smooth.continuous (lid_ice ..).continuous).const_mul r) ((hy s ht).sub (hy 1 zero_lt_one)), integral_sub (hy s ht) (hy 1 zero_lt_one), show (∫ x, bug s (k+2) x*f x)=(∫ x, bug 1 (k+2) x*f x) from bug_turn hp hs]; simp only [sub_self,add_zero]; rw [integral_const_mul]; rfl
lemma ladder (hp:PureA (2*k) f)(hs:0<s): countM s k f=countM s 0 1*(ends k f/brim k) :=by
   induction k generalizing f with
   | zero=> have h:PureA 0 f:=hp; unfold ends; rw [show f=(fun _=> f 0) from h.zeroth]; simp only [iterate_zero_apply]; unfold countM brim; simp only [zero_add,Nat.factorial_zero,Nat.cast_one, div_one,Nat.factorial_one,pow_zero,mul_one,Pi.one_apply]; rw [integral_mul_const]
   | succ k ih=>
     have he:=entry hp hs; rw [ih (show PureA (2*k) (lap f) from Pure.laplace ((show 2*(k+1)=2*k+2 by omega) ▸ hp)),ends_lap] at he; rw [brim_next]; have hb: brim k≠0:=by unfold brim; positivity
     let r:=ends (k+1) f
     have hr: 4*((k:ℝ)+1)*((k:ℝ)+2) ≠ 0:=by positivity
     field_simp; field_simp at he; linarith only [he]
end YM.OPE.Sagebrush
