import YM.GapsContact.Dusk.Purchase
/-!
# Exact Rényi powers instead of subpowers in cell-window prices

All functions of the reference coupling beta. Use one stage demand at a time;
order of DelayLe & terminal certificate after θ/L. `rBase`, etc. crucially
independent of stage (cost 100 below fixed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext.Repeat PhysicalNext.Repeat.Mallow
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open PhysicalNext PhysicalNext.Repeat.Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {P:Teller G} (Q:Target G P) (L:Side)
set_option quotPrecheck false

def rBase : ℝ:= -(15/32:ℝ)
def gate (x:ℝ) := Real.log x
/-- The small-budget exponent. -/
def nice (x:ℝ):= x^rBase
def precious (x:ℝ):= nice x * gate x
def ipo (x:ℝ):= nice x / gate x ^ 30
lemma gate_pos {x:ℝ}(h:1 < x) : 0<gate x:= Real.log_pos h
lemma precious_pos {x:ℝ}(h:1 < x) : 0<precious x:= mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans h) _) (gate_pos h)
lemma ipo_pos {x:ℝ}(h:1 < x) : 0 < ipo x:= div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans h) _) (pow_pos (gate_pos h) _)
lemma gate_large : Tendsto gate atTop atTop:= Real.tendsto_log_atTop

private lemma root_small {μ:ℝ}(h:0<μ):∀ᶠ x in atTop,(Q.costs L μ 1 x 0).rootHit ≤ 2*Q.goal L x:=by
   let u (x:ℝ):= Real.exp (-(Delay.hatWin G L (μ/2) (1/2) x)/4)
   have hc : Rate G L (Q.rate-1) u:= (Rate.monitor_cutoff (show 0 < μ/16 from by positivity) (show (0:ℝ)<2 by norm_num)).congr
        (Eventually.of_forall (fun x=> by unfold u Delay.hatWin; simp only [Real.rpow_two]; congr 1; ring))
   filter_upwards [hc Q.rate (sub_one_lt _)] with x hx; change u x+ _ ≤ _; apply le_trans (add_le_add_left ((le_abs_self (u x)).trans hx) (Q.goal L x)); exact (two_mul _).symm.le

private lemma pledge_power {μ:ℝ} {e a:ℝ} (hm:0<μ):
    ∃ S:ℝ,0 ≤ S∧∀ᶠ x in atTop, ∀ _ : Bikes Q L μ x a e 0 0 0,
       2*(pledgeA L Q μ x 0 0 0*(1-sailUp Q L x)⁻¹) ≤ S * Q.goal L x:= by
    let U:= Real.exp (Q.relative*Footprint.preCost (Q.halo+5)); let V:= Reserves.extract Q.ε 0 0 0; let c := 2+U; let p:= 4*V+4*V*c
    have hV:0≤V:=by unfold V Reserves.extract Reserves.polyPrice; rw [pow_zero]; positivity
    have hu:0≤ c:=by unfold c U; positivity
    have hp:0 ≤ p:=by unfold p; positivity
    refine ⟨4*p,by positivity,?_⟩; filter_upwards [root_small Q L hm] with x h b
    let u:= Q.goal L x; have hx:0 ≤ u:=Real.rpow_nonneg b.paid.le _; let C₀:= Q.costs L μ 1 x 0
    let T:=swing Q L μ 1 x 0; have hA:T.rootHit ≤ c*u:= le_trans (add_le_add_left h (ribbon Q L x)) (by unfold ribbon c U u; exact Eq.le (by ring))
    let y:= (1-sailUp Q L x)⁻¹; have hy:0≤ y:=inv_nonneg.mpr (by linarith [b.within]); have hz:y ≤ 2:=(inv_anti₀ (by norm_num : (0:ℝ)< 1/2) (by linarith [b.within])).trans_eq (by norm_num)
    have hR := mul_le_mul_of_nonneg_right hA hy; have he:= mul_le_mul_of_nonneg_left hz (mul_nonneg hu hx);
    let K:= T.ceiling 0 0 0 0;
    have hZ:T.ceiling 0 0 0 0 ≤ 2*V*c*u:=by
       unfold Mixed.Costs.ceiling Reserves.treeYield
       simp only [Nat.cast_zero,mul_zero,pow_zero,mul_one]
       exact (mul_le_mul_of_nonneg_left (le_trans hR he) hV).trans_eq (by ring)
    have hF: Q.overture L μ x 0 ≤ 4*V*u:=by
       unfold ConnectedActivityE6.Target.overture ConnectedActivityE6.Target.quantum Mixed.Costs.ceiling Reserves.treeYield
       simp only [Nat.cast_zero,mul_zero,pow_zero,mul_one]
       change V *((C₀.rootHit)*(1-(1:ℝ)/2)⁻¹)≤_
       rw [show (1-(1:ℝ)/2)⁻¹=2 by norm_num]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h zero_le_two) hV).trans_eq (by unfold u;ring)
    let S := pledgeA L Q μ x 0 0 0
    have he': S≤p*u:=by
       unfold S pledgeA p; rw [mul_zero,add_zero,one_mul]; linarith
    exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right he' hy).trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hp hx))) zero_le_two).trans_eq (by unfold u; ring)
lemma beta_slide : Tendsto (fun x:ℝ=> betaF G x L) atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_id
-- Budget for Volant using IPO(m+1) offer and precious(m) output
lemma sails_near {μ:ℝ} (X:Q.Expense) (hg:G.Simple)(hm:0<μ)(he:Q.rate=rBase) : ∀ᶠ x in atTop,
    let e:=(Q.exp-X.earn)/3; Bikes Q L μ x X.earn e 0 0 0 ∧
    2*(pledgeA L Q μ x 0 0 0*(1-sailUp Q L x)⁻¹) ≤ precious x := by
    let e:=(Q.exp-X.earn)/3; have hx:0<e:=by unfold e; linarith only [X.first,X.second,X.worth]
    obtain ⟨S,hS,hA⟩:= pledge_power Q L (a:=X.earn) (e:=e) hm
    filter_upwards [hA, gate_large.eventually_ge_atTop S, Daisy.stables L Q hm (fun _=>0) hx (by unfold e; linarith only [X.first,X.second,X.worth] : X.earn+e+e ≤ Q.exp) X.price (Rate.const _) 0 0 0, eventually_gt_atTop (0:ℝ)] with x h hx hk hv v; refine ⟨hk.1, le_trans (h hk.1) ?_⟩
    unfold ConnectedActivityE6.Target.goal; rw [he]; unfold precious nice; rw [mul_comm (x^rBase)]; refine mul_le_mul hx ?_ (Real.rpow_nonneg hk.1.paid.le _) (hS.trans hx)
    apply Real.rpow_le_rpow_of_nonpos hv ?_ (by norm_num [rBase]); exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos hg).le (Real.log_nonneg (by exact_mod_cast L.property)))
end YM.GapsContact.Dusk
