import YM.FormalOPE.RG10.BlockGauge.Penalty
import YM.PertExtension.OrbExpansion
/-!
 # pin choice law on the regulator and expose calculation conventions

 `finite_t` operator `noise`. Uses any designated Step choice on ambient full torus (weights in
 formal germs for primitive gauge-invariant stamps ignore tags because on equal principal branch
 on chart: prove from concrete laws). `mixture` version if wanting exact real tag votes in formal
 integral: always use ONE actual choice globally for all factors in a term.Accept.Reg geometry
 fingerprint of entire even quotient from that observation. On that toy auxiliary joint integral
 OR if interpreting θ-specific quantities, same assertion. Never claiming conditioning on physical
 nonpert fields by here. Geometry k even ≤ Bound, no volume claims. Future.Pause.
 No smoothing Price.Project$ patch estimates. Real ratios used in projection unit.Laurent separate.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Function Finset PowerSeries Topology Metric Lattice Gauge RG Wilson MeasureTheory
open PertExtension PertExtension.Orb InversionWard Push.Loops
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f n:Side}
variable (S : StepData c f)
variable (H:S.patch.Branches S.kernel G)
variable (t:S.Choices)
local notation "Ω"=> LinkFrame G f
local notation "Ψ"=> LinkFrame G c
variable (U:LinkFrame G f)(V:LinkFrame G c)(β:ℝ)
-- before blocking Crew
 def noise := (zone β c f G S)⁻¹ * Real.exp (-β * BlockGauge.penalty S t U V)
 def mixture := ∑ t:S.Choices, S.likelihood (liftLinks U) t * noise S t U V β
local notation "μ"=> Chart.physical G (OEdge c)
lemma pos : 0<noise S t U V β:= mul_pos (inv_pos.mpr (zone_pos ..)) (Real.exp_pos _)
lemma normalized : ∫ V, noise S t U V β ∂μ = 1:= by unfold noise; rw [integral_const_mul,heating,inv_mul_cancel₀ (zone_pos ..|>.ne')]

include H
lemma meets : ∀ᶠ U:LinkFrame G f in 𝓝 1, ∀ V:LinkFrame G c, mixture S U V β=noise S t U V β:= by
 filter_upwards [same_choice S H t] with U h V; unfold mixture;
 have he t' : noise S t' U V β=noise S t U V β := by unfold noise BlockGauge.penalty ; rw [show atStep S t' U=atStep S t U from funext (fun i=> congr_fun (h t') i.val)]
 rw [show ∑ t':S.Choices, S.likelihood (liftLinks U) t' * noise S t' U V β=∑ t':S.Choices, S.likelihood (liftLinks U) t' * noise S t U V β from Finset.sum_congr rfl fun i _=> congr_arg (_ * ·) (he i)]; rw [← Finset.sum_mul, StepData.chosen S H,one_mul]
lemma measurable_penalty : Measurable (fun a: LinkFrame G f × LinkFrame G c=> BlockGauge.penalty S t a.1 a.2):= by unfold BlockGauge.penalty distance; apply Measurable.const_mul; refine Finset.measurable_fun_sum _ fun i _=> ?_; exact G.continuous_price.measurable.comp (((measurable_pi_apply _).comp (measurable_snd.mul ((atStep_meas S H t).comp measurable_fst).inv)))
lemma measurable_noise : Measurable (fun a: LinkFrame G f × LinkFrame G c=> noise S t a.1 a.2 β):=by unfold noise; exact Measurable.const_mul (Measurable.exp (Measurable.const_mul (measurable_penalty S H t) _)) _
omit H
lemma snug : Integrable (fun V=> noise S t U V β) μ:= by
 have he : Continuous (fun V=> noise S t U V β):= continuous_const.mul ( heat_cont (G:=G) S β|>.comp (continuous_id.mul_const _))
 exact he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
include H
lemma closure : ∫ V,mixture S U V β ∂μ=1:= by
 unfold mixture; rw [integral_finsetSum];
 · simp_rw [integral_const_mul,normalized, mul_one]; exact StepData.chosen S H (liftLinks U)
 exact fun i _=> (snug S i U β).const_mul _
lemma smooth_penalty {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {x:E}{U:E→LinkFrame G f}{V:E→LinkFrame G c}
   (hu:MatDiffAt U x)(hv:MatDiffAt V x) (ha:U x=1) : ContDiffAt ℝ ω (fun i=> BlockGauge.penalty S t (U i) (V i)) x:= by
 unfold BlockGauge.penalty BlockGauge.distance; refine contDiffAt_const.mul (ContDiffAt.sum (s:=univ) (fun _ _=>?_)) -- signature
 exact Push.Loops.price_diff (ContDiffAt.mul (hv _) (mat_inv_diff (atStep_smooth S H t hu ha _)))
end YM.FormalOPE.RG10.BlockGauge
