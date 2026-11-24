import YM.GapsContact.Dusk.Tariff

/-!
# Coasting tariff

At step m, multiply the radii (all potentially simultaneous legs) by aBrake
before testing the WHOLE shot & budget. K close-up price must also restore same
precious quota after paying for every singleton & mixed activity. The additional
price on the single-leg inputs here is appropriate for a *terminal* span since
we won't repay it at every step, only upon entering. Uniform after post-L
registration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext.Repeat PhysicalNext.Repeat.Mallow MergeProof Merge.Palette
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open PhysicalNext PhysicalNext.Repeat.Roof Daisy Charity Rain Roost Lotus Extra.Multi
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {P:Teller G} (Q:Target G P) (L:Side)
set_option quotPrecheck false

def aBrake (x:ℝ):= (gate x^40)⁻¹
def coupon (x:ℝ):= x^(-(2:ℝ))
structure Ticks (x y u:ℝ) (r:ℕ) : Prop where
    price : 1 ≤ gate x
    met : 1 ≤ gate y
    precise : precious x ≤ 1 ∧ precious y ≤ 1
    capE : let T:= r*siteFactor (radiusB y)*coupon y + 4*(aBrake y*precious y); T+Real.exp T*T ≤ ipo y
    capK : let b:= radiusB x; let T:= u+r*siteFactor b*coupon y;
              (((b+b+1:ℕ):ℝ)^4 * T ≤ 1/2) ∧ (Real.exp T-1 ≤ precious x)
variable (r:ℕ)
lemma gate_rate : Rate G L 0 (fun x=> gate (betaF G x L)) := by
   apply Rate.bill.compare; filter_upwards [(beta_slide (G:=G) L).eventually_gt_atTop 1] with x hx
   rw[abs_of_nonneg (gate_pos hx).le,abs_of_nonneg (zero_le_one.trans (Delay.bill_ge ..))]
   have ht:= sq_nonneg (Real.log (betaF G x L)-1); have hw : 0≤ (radiusB x:ℝ):= Nat.cast_nonneg _; unfold Delay.bill gate; nlinarith only [ht,hw,Real.log_pos hx]
lemma precious_rate : Rate G L rBase (fun x=> precious (betaF G x L)):=by
   unfold precious nice; apply (Rate.power.mul (gate_rate L)).weaken; rw [add_zero]
include G L in
lemma precious_eventual : ∀ᶠ x in atTop, precious x ≤ 1:=by
   have h := (precious_rate (G:=G) L).below (by norm_num [rBase]) 1 zero_lt_one
   -- omitted G implicit; lemma need include
   let y:= G.slopeConstant*Real.log L.val
   have he := (tendsto_atTop_add_const_right _ (-y) tendsto_id).eventually h
   filter_upwards [he] with x hx; apply (le_abs_self _).trans; change |precious (x + -y + y)| ≤ 1 at hx; rwa [neg_add_cancel_right] at hx

lemma ipo_grants (b:ℝ→ℝ) (r':ℝ) (hb:r' < rBase) (h:Rate G L r' b) : ∀ᶠ x in atTop,b x ≤ ipo (betaF G x L):=by
   have hf := h.mul (gate_rate (G:=G) L|>.pow 30); rw [zero_mul,add_zero] at hf
   filter_upwards [hf rBase hb, (beta_slide (G:=G) L).eventually_gt_atTop 1] with x hx he;
   exact (le_div_iff₀ (pow_pos (gate_pos he) _)).2 ((le_abs_self _).trans hx)
lemma site_cost (p:ℝ) : ∀ᶠ x in atTop,↑r*siteFactor (radiusB x)*p ≤ gate x ^ 30:=by
   let v(x:ℝ):= 2*(16*((radiusB x):ℝ)+9); let w:= max 0 p; let t:= (r:ℝ)*Real.exp 1 * (82:ℝ)^4
   have hu :0 ≤ w:= le_max_left ..; have ht :0 ≤ t:=by unfold t; positivity
   filter_upwards [gate_large.eventually_ge_atTop 1, gate_large.eventually_ge_atTop (t*w)] with x h H
   let m:= gate x; have hx:0 ≤ ((radiusB x):ℝ):= Nat.cast_nonneg _
   have he: ‖v x‖ ≤ 82*m^2:=by
        have hy: (radiusB x:ℝ) ≤ m^2+1:= (Nat.ceil_lt_add_one (sq_nonneg _)).le
        unfold v; rw [Real.norm_of_nonneg (by positivity)]; linarith only [one_le_pow₀ (show 1 ≤ m from h) (n:=2),hy] -- v RHS: if m=1 82 fits 82
   have hh: r*siteFactor (radiusB x) ≤ t*m^8:=by
      unfold t siteFactor; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ 2*(16*(radiusB x:ℝ)+9)) ((Real.le_norm_self (v x)).trans he) 4) (Real.exp_pos _).le) (Nat.cast_nonneg _)) ?_; exact Eq.le (by ring)
   calc _ ≤ (↑r*siteFactor (radiusB x))*w:= mul_le_mul_of_nonneg_left (le_max_right ..) (by unfold siteFactor; positivity)
        _ ≤ t*m^8*w:=mul_le_mul_of_nonneg_right hh hu
        _ = (t*w)*m^8:= by ring
        _ ≤ m^9:= by rw [show m^9=m*m^8 from (by ring)]; exact mul_le_mul_of_nonneg_right H (zero_le_one.trans (one_le_pow₀ (show 1 ≤ m from h) (n:=8)))
        _ ≤ _ := pow_le_pow_right₀ h (by omega)

lemma ipo_ship (hg:G.Simple) (he:Q.rate=rBase): ∀ᶠ x in atTop, Merge.Palette.shipPrice L Q x r (ipo (betaF G x L)):=by
   let y(x:ℝ):= betaF G x L
   have hxy(x:ℝ):x≤y x:=le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos hg).le (Real.log_nonneg (by exact_mod_cast L.property)))
   let v:= Q.relative*Footprint.preCost (Q.halo+5); let w:= (Q.relative+1)*Footprint.preCost (Q.halo+5); let A:= Real.exp (w-v)
   filter_upwards [eventually_gt_atTop (1:ℝ), site_cost r A] with x hx h
   have hy:0<gate (y x):=gate_pos (hx.trans_le (hxy x)); have ht:0≤ nice (y x):=Real.rpow_nonneg (zero_le_one.trans (hx.trans_le (hxy x)).le) _
   unfold shipPrice ribbon ConnectedActivityE6.Target.goal; rw [he]
   calc _ = (r*siteFactor (radiusB x)*A)*(ipo (y x)*Real.exp v):=by rw [show Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5))=A*Real.exp v from by unfold A; rw[← Real.exp_add, sub_add_cancel]];ring
        _ ≤ gate (y x)^30*(ipo (y x)*Real.exp v):=mul_le_mul_of_nonneg_right (h.trans (pow_le_pow_left₀ (gate_pos hx).le (Real.log_le_log (zero_lt_one.trans hx) (hxy x)) _)) (mul_nonneg (ipo_pos (hx.trans_le (hxy x))).le (Real.exp_pos _).le)
        _ = _:=by unfold ipo nice; field_simp; rfl

private lemma first_account : Rate G L (-(2:ℝ)) (fun x=> ↑r*siteFactor (radiusB (betaF G x L))*coupon (betaF G x L)):=by
   have hc(i):0 ≤ siteFactor i:=by unfold siteFactor; positivity
   have hx:= (beta_slide (G:=G) L).eventually (site_cost r 1)
   have hh:Rate G L 0 (fun x=> ↑r*siteFactor (radiusB (betaF G x L))) := ((gate_rate (G:=G) L |>.pow 30).weaken (by rw [zero_mul])) |>.compare (hx.mono fun i h=>by rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc _))]; rw [mul_one] at h; exact h.trans (le_abs_self _))
   simpa only [coupon,zero_add] using! (hh.mul Rate.power)

private lemma exp_one_small {u:ℝ} (h:0≤u) (ht:u≤1/2): Real.exp u - 1 ≤ 2*u:=by
   have he:=Real.add_one_le_exp (-u)
   rw [Real.exp_neg] at he; have hq:=Real.exp_pos u
   have hp:Real.exp u *(1-u) ≤1:=by
      rw [mul_comm]; rw [← le_div_iff₀ hq]; rw [one_div]; linarith
   have hx:Real.exp u ≤2:=by linarith only [hp, mul_le_mul_of_nonneg_left ht hq.le]
   nlinarith only [mul_le_mul_of_nonneg_right hx h,hp]
lemma shore_finance (hg:G.Simple) {μ:ℝ} (hm:0<μ): ∀ᶠ x in atTop,Ticks x (betaF G x L) (straw μ L G x) r:=by
   let y(x:ℝ):= betaF G x L
   have hxy(x:ℝ):x≤y x:=le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos hg).le (Real.log_nonneg (by exact_mod_cast L.property)))
   let u x := r*siteFactor (radiusB (y x))*coupon (y x); let k (x:ℝ):= (straw μ L G x + r*siteFactor (radiusB x)*coupon (y x))
   let b (x:ℝ):= radiusB x+radiusB x+1
   have hK:Rate G L (-(2:ℝ)) k := by
      unfold k; simpa only [coupon,zero_add] using! ((infuso L (G:=G) 2 (μ/4) (1/4) (by positivity) (by norm_num) (-2)).add (((warmLane L Rate.radius_price).mul_left (r:ℝ)).mul Rate.power|>.weaken (by simp)))
   have hb:Rate G L (-2) (fun x=>(b x:ℝ)^4*k x):=by
      have hx:=Rate.radius_price (L:=L) (G:=G); simpa only [b, Nat.cast_add, Nat.cast_one,zero_mul,zero_add] using! (((hx.add hx).add (Rate.const 1)).pow 4|>.mul hK)
   have hU(x)(ht:1<x):0 ≤ u x ∧ 0 ≤ k x:=by
      have hp:0 ≤ coupon (y x):=Real.rpow_nonneg (zero_le_one.trans (ht.trans_le (hxy x)).le) _; have hk(n):0 ≤ siteFactor n:=by unfold siteFactor; positivity
      have hf:0 ≤ straw μ L G x:=by unfold straw lauge; positivity
      constructor; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hk _)) hp; exact add_nonneg hf (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hk _)) hp)
   have he:= first_account (G:=G) L r
   filter_upwards [gate_large.eventually_ge_atTop 100, ((beta_slide (G:=G) L).eventually (gate_large.eventually_ge_atTop 100)),(hb.below (by norm_num) _ (by norm_num : (0:ℝ)<1/2)),hK.below (by norm_num) _ (by norm_num: (0:ℝ)<1/2),ipo_grants (G:=G) L _ _ (by norm_num [rBase]) (he.mul_left 100),((hK.mul_left 2) _ (by norm_num [rBase]:-(2:ℝ)<rBase)), precious_eventual (G:=G) L, (beta_slide (G:=G) L).eventually (precious_eventual (G:=G) L),eventually_gt_atTop (1:ℝ)] with x ht hy hbc hk hu hm hs hp hx
   obtain ⟨h1,h2⟩:= hU x hx
   have h₀:1≤gate x:= le_trans (by norm_num) ht; have h:1≤gate (y x):=le_trans (by norm_num : (1:ℝ)≤100) hy
   have hv:1<y x:=hx.trans_le (hxy x); have hc:0≤nice x:=Real.rpow_nonneg (by linarith : 0 ≤ x) _
   refine ⟨h₀,h,⟨hs,hp⟩,?_,?_⟩
   · let s:= gate (y x); have h' : 0<s:=zero_lt_one.trans_le h; let w:= precious (y x); let t:=aBrake (y x); let T:=u x + 4*(t*w); let v:= ipo (y x); have hw:0 < w:= precious_pos hv; have hT:0 ≤ T:=by have hz:0<t:=inv_pos.mpr (pow_pos h' _); unfold T; positivity
     have hu':100*u x ≤ v:=hu
     have hv': v≤w:=by
       have hx:0 < nice (y x):=Real.rpow_pos_of_pos (zero_lt_one.trans hv) _
       refine (div_le_self hx.le (one_le_pow₀ h)).trans (le_mul_of_one_le_right hx.le h)
     have hx₁: t*w ≤ v/100:=by
       have hz: t*w*s^9 = v:= by unfold t aBrake w precious v ipo s; field_simp
       rw [← hz]; have hh : 100 ≤ s^9:=le_trans (show 100 ≤ s from hy) ((pow_one s).symm.trans_le (pow_le_pow_right₀ h (by omega)))
       apply (le_div_iff₀ (by norm_num)).2; exact mul_le_mul_of_nonneg_left hh (by have hz:0≤t:=inv_nonneg.mpr (pow_pos h' _|>.le); positivity)
     have hr:T ≤ v/20:= by unfold T; linarith only [hu',hx₁];
     have hq:= exp_one_small hT (by linarith only [hr,hv', (show w≤1 from hp)])
     have hh: Real.exp T ≤ 3:=by linarith only [hr,hv',(show w≤1 from hp),hq]
     change T+Real.exp T*T ≤ v; linarith only [mul_le_mul_of_nonneg_right hh hT,hr,hT]
   refine ⟨(le_abs_self _).trans hbc,le_trans (exp_one_small h2 ((le_abs_self _).trans hk)) ((?_ : 2*k x ≤ nice x).trans (le_mul_of_one_le_right hc h₀))⟩
   exact ((le_abs_self _).trans hm).trans (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hx) (hxy x) (by norm_num [rBase]))
end YM.GapsContact.Dusk
