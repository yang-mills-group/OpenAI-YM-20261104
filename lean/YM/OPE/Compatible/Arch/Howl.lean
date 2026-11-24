import YM.OPE.Compatible.Arch.Acorn
/-!
# Local Mellin calculation. Uniformity at each fixed regulator only; arbitrary measurable gate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "Lf" => Tested.germ
open Zone Radial ScriptJ Metric
local notation "R" => Radial.zone (E:=E)
variable (μ:Measure E)[μ.HasTemperateGrowth] {c:ℝ}{A:ℝ→E→ℝ}{p:ScriptJ E}{k:E→ℝ}
lemma balanceH (hb:Bears (shade c) A p)(ha:∀ i, Measurable (A i))(hr:KernFit k (c+c))(he:0<c)(hv:Measurable k): ∃ δ>0,∀ s:Set E,s⊆ ball 0 δ→ s∈𝓝 0→MeasurableSet s→ Reads (fun t:ℝ=> ∫ x in Suber s t,(A t*k) x ∂μ) (gemLift μ k p) := by
    obtain ⟨e,d,m,hd,hm,hK⟩:=hb.slope.cost -- order C
    let δ:=e/2; refine ⟨δ,half_pos hd,fun s hs hp hh=>?_⟩
    unfold Reads; let U(t):= Suber s t; have hU(t):MeasurableSet (U t):= hh.preimage (show Measurable (fun x:E=>t•x) by fun_prop)
    let D(t):= A t*k-quitt p t*k
    let f(t:ℝ):= ∫ x in U t,D t x ∂μ; let g(t:ℝ):= ∫ x in (U t)ᶜ,(quitt p t*k) x ∂μ
    have hL:0<c+c:=add_pos he he
    have htX(t:ℝ)(hy:0<t)(ht:t<δ): (∀ᵐ x ∂μ.restrict (U t),‖D t x‖ ≤ (d*t^3)*bill m c x):=by
       filter_upwards [ae_restrict_mem (hU t)] with x hx; let w:= (R).w x; have hw1:= ((R).high x); have hw:0<w:= lt_of_lt_of_le zero_lt_one hw1
       have hv : t*‖x‖<δ:=by have he:= hs (show t•x∈s from hx); simpa [norm_smul_of_nonneg hy.le,mem_ball_zero_iff] using he
       have ha:= hK x t hy (show t*w ≤e from by change t*(1+‖x‖) ≤ _; unfold δ at ht hv; linarith)
       have hh : shade c x*k x≤ Real.exp (-c*‖x‖^2) :=by apply le_trans (mul_le_mul_of_nonneg_left (hr x).2 (show 0≤shade c x from Real.exp_nonneg _)); unfold shade; rw [← Real.exp_add]; apply le_of_eq; congr 1;ring
       calc
          _ ≤ d*w^m*shade c x*t^3*k x:=by rw [show D t x=(A-quitt p) t x*k x by simp only [D,Pi.sub_apply,Pi.mul_apply];ring,norm_mul,Real.norm_eq_abs (k x),abs_of_nonneg (hr x).1]; exact mul_le_mul_of_nonneg_right ha (hr x).1
          _ = d*t^3*w^m*(shade c x*k x):=by ring
          _ ≤ _ := by unfold bill; apply le_trans (mul_le_mul_of_nonneg_left hh (by positivity)); rw [mul_assoc]
    have hf : f=O[Lf](gradeP 3):=by rw [Reads.isTariff]; refine ⟨d*∫ x:E,bill m c x ∂μ, mul_nonneg hm (integral_nonneg fun x=>bill_nonneg ..),?_⟩; filter_upwards [Tested.eventually_small (show 0<δ from half_pos hd)] with t hy; exact (billCap μ (mul_nonneg hm (pow_nonneg hy.1.le _)) he (htX t hy.1 hy.2)).trans_eq (by ring)
    apply (hf.sub (show g=O[Lf](gradeP 3) from quit_collapsed μ hr hL hb.toll hp hh)).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [Tested.eventually_small (half_pos hd)] with t ht;
    have hk:= paying μ hr hv hL hb.toll t; have hi : IntegrableOn (D t) (U t) μ:= ((bill_integrable μ m he).const_mul _).integrableOn.mono' (show AEStronglyMeasurable _ _ from ((ha t).mul hv).aestronglyMeasurable.sub hk.integrableOn.1) (htX t ht.1 ht.2); have hV: IntegrableOn (A t*k) (U t) μ:= by rw [←sub_add_cancel (A t*k) (quitt p t*k)]; exact hi.add hk.integrableOn
    change f t-g t=(∫ x in U t,_ ∂μ)-_
    rw [show (gemLift μ k p).atK t=∫ x,(quitt p t*k) x ∂μ from (costing μ hr hv hL hb.toll t).symm, ← integral_add_compl (s:=U t) (hU t) hk,show f t= _ from integral_sub hV hk.integrableOn]; unfold g; abel
end YM.OPE.Libra
