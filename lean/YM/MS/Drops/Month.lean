import YM.MS.Drops.Ghost
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
variable (L K:Degree G)
lemma hour_s (i:Axis)(j:CI G)(p:QP)(u:ℝ): fax L (W i j (u • p))= u ^ (L.degree + 1) • fax L ( W i j p ):= by
   change Theater.item i _ j _=u^(_:ℕ) • Theater.item _ _ _ _; rw [ (portθ ..).scale,zpow_natCast ]
local notation "U" => xy (fax L) (fax K)
abbrev Epoch:= L.degree+K.degree+2
lemma slot_s (p:QP)(u:ℝ): U (u • p)= u ^ Epoch L K • U p:= by
    unfold xy; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [ ← smul_neg, hour_s, hour_s, show Epoch L K=L.degree+1+(K.degree+1) from (by unfold Epoch; omega), pow_add ]; push_cast [Complex.real_smul]; ring
lemma dark_p (p:QP)(s:ℝ): dark_s p s=exp s^2 • dark_s (exp s • p) 0:= by
    have hu : Landau.low (exp s) p= Landau.low 1 ( exp s • p ):= by simp only [Landau.low,coat,pow_zero,one_mul,one_smul] -- ν radius
    rw [ dark_s, dark_s, Real.exp_zero, scaling, ← hu ]; push_cast [Complex.real_smul]; have hp: (exp s:ℂ)≠0:= by exact_mod_cast (exp_pos s).ne';
    by_cases he: Momentum.sq p=0; rw [he]; simp; field_simp [show ( (Momentum.sq p:ℂ) ≠ 0 ) from by exact_mod_cast he] <;> ring -- at zero
abbrev hgt := Epoch L K+2
lemma strength (t s:ℝ)(p:E4)(ht:t=exp s) : t^(hgt L K) • wearΦ L K s p=t^4 • wearΦ L K 0 ( t • p ):= by
    unfold wearΦ; rw [ dark_p, map_smul,slot_s, ← ht ]; simp only [Complex.real_smul]; unfold hgt; push_cast; ring -- exponent a+p².
lemma aim (x y:E4)(t:ℝ): Radian.wave ( t • x ) y=Radian.wave x (t • y):= by rw [ ← ν_bill,← ν_bill,map_smul,map_smul,bill,bill ]; unfold Momentum.pairing; simp_rw [Pi.smul_apply,smul_eq_mul]; congr 3; exact Finset.sum_congr rfl fun i _=> by ring
lemma Year (s:ℝ)(x:E4) : γX L K x s = (exp s ^ (hgt L K))⁻¹ • γX L K ((exp s)⁻¹ • x) 0:= by
    let r:= exp s; let v:= r⁻¹ • x; let f(p:E4):= Radian.wave v p * wearΦ L K 0 p; let k:= hgt L K; have ht := exp_pos s; have he : r^k≠0:= pow_ne_zero _ ht.ne'; apply smul_right_injective ℂ he; change r^k • γX L K x s=r^k • (r^k)⁻¹ • _; rw [ smul_inv_smul₀ he,γX,Radian.wind,← integral_smul ]; change _=∫ p,f p; obtain hv := Measure.integral_comp_smul_of_nonneg volume f r ( hR:=ht.le ); rw [Radian.spaceD] at hv; rw [ ← ( smul_inv_smul₀ ( pow_ne_zero 4 (show r≠0 from ht.ne') ) ( ∫ p,f p ) ), ← hv, ← integral_smul ]; refine integral_congr_ae (Eventually.of_forall fun p=>?_); dsimp only
    rw [show Radian.wave x p= Radian.wave v ( r • p ) from Eq.trans (show _=Radian.wave ( r • v ) p from (congr_arg ( fun x:E4=> Radian.wave x p ) ( smul_inv_smul₀ ht.ne' x )).symm ) ( aim v p r ) ]; unfold f; rw [ ← mul_smul_comm,← mul_smul_comm (r^4), show r^k • wearΦ L K s p= _ from strength L K _ _ _ rfl ] -- args order
lemma θsign (L:Degree G): (stand L).comp ( gaugeJet (G:=G) ) = ( L.degree.factorial:ℝ ) • ( constrain (G:=G) ( fromF G ( basis ∘ L.layout ) L.paint L.a.val.1 L.a.val.2 )):= by
    apply LinearMap.ext; intro Y; change stand L ( gaugeJet Y ) = _; rw [stand_K,match_leg]; rfl
lemma scope_val (x:E4)(hx:x≠0): Prayer.gleam L K x= legKernel ((stand L).comp ( gaugeJet (G:=G) )) ((stand K).comp (gaugeJet (G:=G))) x:= by
    unfold Prayer.gleam; change _= Maxwell.pairing ( show x∈ Maxwell.away from hx ) _ _; rw [ θsign,θsign,map_smul,map_smul,LinearMap.smul_apply,raw_mixed _ _ _ _ _ _ _ _ hx ]; simp only [smul_eq_mul]; ring
lemma Right (x:E4)(hx:x≠0)(s:ℝ): Prayer.gleam L K x=( exp s ^ hgt L K )⁻¹ *Prayer.gleam L K ( exp (-s) • x ):= by
    let r:= exp s; let y:= exp (-s); let h':= exp_pos s; let k:= hgt L K; obtain he:= Prayer.grown L K ( exp_pos (-s) ) x hx; rw [Beamer.amount,Beamer.amount,← pow_add,show L.degree+2+(K.degree+2)=hgt L K from by unfold hgt Epoch; omega] at he; rw [← inv_pow,← exp_neg]; exact he.symm -- exact exp inv equivalence type
lemma parityX (x:E4)(s:ℝ): γX L K x s=γX K L (-x) s:= by
    unfold γX; rw [Radian.wind,Radian.wind, ← integral_neg_eq_self (fun p=> Radian.wave (-x) p* wearΦ K L s p) ]; refine integral_congr_ae (Eventually.of_forall fun p=>?_); dsimp only; rw [ ←ν_bill, ←ν_bill,map_neg,map_neg,Tone.inverse,Tone.opp,inv_inv]; unfold wearΦ dark_s; rw [map_neg,sq_neg, show Landau.low _ (-ν p) = Landau.low (exp s) (ν p) from by simp [Landau.low,coat] ]; congr 2; unfold xy; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; rw [neg_neg,mul_comm]
end YM.MS.Drops
