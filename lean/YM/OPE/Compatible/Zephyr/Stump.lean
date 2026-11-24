import YM.OPE.Compatible.Zephyr.Lodge
/-! # Proportional perturbation ball. zero case needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
section
variable {α:Type}[MeasurableSpace α]{μ:Measure α}{f g h p:α→ℝ}{d u v:ℝ}
lemma tied (hx: ‖d‖ ≤1)(he:‖d‖ ≤ u): ‖Real.exp d-1‖ ≤ 2*u:=by
      rw[Real.norm_eq_abs]; exact (Real.abs_exp_sub_one_le hx).trans (by change |d|≤ _ at he; linarith)
lemma mutiny (hf:Integrable f μ)(he:Integrable g μ)(hv:Integrable (f*p) μ)(hw:Integrable (g*p) μ)(hH:∀ i, 0 ≤ f i)(hθ:0≤u)(hu:u≤1/2)(hy:∀ i,‖g i-f i‖≤ f i *u)(hp:0≤v)(ht:∀ i,‖p i‖ ≤ v):
     let a:=∫ i,g i ∂μ; let x:=∫ i,g i*p i ∂μ; let b:=∫ i,f i ∂μ; let y:=∫ i,f i*p i ∂μ
     ‖x/a-y/b‖ ≤ 4*u*v:=by
       intro a x b y; have hz:0 ≤ b:=integral_nonneg hH
       have hh: ‖a-b‖ ≤ b*u:=by
          rw [show a-b=∫ i,g i-f i ∂μ from (integral_sub he hf).symm]; apply (norm_integral_le_integral_norm _).trans; rw [show b*u=∫ i,f i*u ∂μ from (integral_mul_const ..).symm];exact integral_mono (he.sub hf|>.norm) (hf.mul_const _) hy
       have hL: ‖x-y‖≤ b*(u*v):=by
          rw [show x-y=∫ i,(g*p) i-(f*p) i ∂μ from (integral_sub hw hv).symm]; apply (norm_integral_le_integral_norm _).trans; rw [show b*(u*v)=∫ i,f i*(u*v) ∂μ from (integral_mul_const ..).symm]; refine integral_mono (hw.sub hv|>.norm) (hf.mul_const _) (fun i=>?_); simp only [Pi.mul_apply,←sub_mul,norm_mul,← mul_assoc]; exact mul_le_mul (hy _) (ht _) (norm_nonneg _) (mul_nonneg (hH i) hθ)
       have hY: ‖y‖ ≤ b*v:=by rw [show b*v=∫ i,f i*v ∂μ from (integral_mul_const ..).symm]; apply (norm_integral_le_integral_norm _).trans; refine integral_mono (hv.norm) (hf.mul_const _) (fun i=>?_);rw [norm_mul,Real.norm_of_nonneg (hH i)]; exact mul_le_mul_of_nonneg_left (ht i) (hH i)
       by_cases h':b=0
       · rw [h',sub_zero,zero_mul] at hh; rw [norm_le_zero_iff] at hh; rw [hh,h',div_zero,div_zero,sub_zero,norm_zero]; positivity
       have hb:0<b:=hz.lt_of_ne (Ne.symm h'); have hw : b≤2*a:=by rw [Real.norm_eq_abs] at hh; linarith only [hh,neg_le_abs (a-b),mul_le_mul_of_nonneg_left hu hz]
       have ha:0<a:=by linarith only[hw,hb]
       have hY':‖y/b‖ ≤ v:=(by rw [norm_div,Real.norm_of_nonneg hb.le,div_le_iff₀ hb]; exact hY.trans_eq (mul_comm ..))
       refine le_of_mul_le_mul_left (a:=a) ?_ ha; rw [← show ‖a*(x/a - y/b)‖=a*‖x/a-y/b‖ from (by rw [norm_mul,Real.norm_of_nonneg ha.le]),show a*(x/a-y/b)=(x-y)-(a-b)*(y/b) by field_simp; ring]
       apply (norm_sub_le ..).trans; rw [norm_mul]; refine (add_le_add hL (mul_le_mul hh hY' (norm_nonneg _) (mul_nonneg hb.le hθ))).trans ?_; have hx:=mul_le_mul_of_nonneg_right hw (mul_nonneg hθ hp); linarith only [hx]
end
end YM.PhysicalNext.Repeat.Aroma
