import YM.AllOrder.Laplace.Span
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Sum
/-! # Collars on the actual gauge slices. Fixed-period auxiliaries.

Measure conventions as in PhysicalNext.Repeat.Fare.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Filter Metric
open scoped Topology ENNReal ContDiff Classical
section basic
variable {Y:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
lemma stick_closed (μ:Measure Y) [μ.IsAddHaarMeasure] (F K:ℝ×Y→ℝ) {r t:ℝ} (ht:0<t)(hp:0<r): stick μ F K r t= ∫ y in closedBall 0 (r/t), K (t, t • y)*Real.exp (-F (t,t • y)/t^2) ∂μ := by
   unfold stick; refine setIntegral_congr_set ?_
   have he : (disc t r : Set Y)=ball 0 (r/t):= by ext y; rw [Radial.disc_mem ht.le, mem_ball_zero_iff,lt_div_iff₀ ht, mul_comm t];
   rw [he]; filter_upwards [show ∀ᵐ x ∂μ,x∉sphere 0 (r/t) from (by simpa only [ae_iff, not_not,setOf_mem_eq] using Measure.addHaar_sphere_of_ne_zero μ (0:Y) (div_pos hp ht|>.ne'))] with x hx; change (dist x 0<r/t) = (dist x 0≤r/t); apply propext; exact ⟨fun h=> h.le, fun h=> lt_of_le_of_ne h hx⟩
end basic
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side} {S:StepData c f}
variable (F:Forest S.ratio) (O:ChartRatio G)
local notation "K"=>Precision.Key F G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "Ω"=> ℝ×Poll.Body (Precision.Key F G)

def collar (P:ℝ → Config G c) (W:ℝ→Y) (δ t:ℝ): Set (F.Slice G):= staying F (W t) t (δ/t) (P t)
def angle (P:ℝ → Config G c)(W:ℝ→Y) (H:ℝ→F.Slice G→ℝ) (δ t:ℝ):ℝ:= (t^Fintype.card (Precision.Key F G))⁻¹ * ∫ z in collar F P W δ t,H t z ∂ F.order G
lemma enter (P:ℝ→ Config G c)(W:ℝ→Y)(δ t:ℝ)(ht:0<t): collar F P W δ t= (fun y=> draw F (P t) (W t+y)) '' closedBall 0 δ:= by
    ext z
    unfold collar staying; constructor
    · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩; exact ⟨t•y,(by rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg ht.le,mul_comm]; exact le_of_le_of_eq ((le_div_iff₀ ht).mp (mem_closedBall_zero_iff.mp hy)) rfl),rfl⟩
    rintro ⟨y,hy,rfl⟩; refine ⟨W t+y,⟨t⁻¹•y,?_,?_⟩,rfl⟩; swap; · simp only [smul_inv_smul₀ ht.ne']
    rw [mem_closedBall_zero_iff, norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_eq_div]; exact (div_le_div_of_nonneg_right (mem_closedBall_zero_iff.mp hy) ht.le)

lemma wind_gate (h:LocalRatio O):∀ᶠ y :Y in 𝓝 0, windmill F y∈mouth O:= by
    have hl (i:F.Free) : Continuous (fun y:Y=>windmill F y i) := (continuous_apply _).comp (((weld (Precision.Key F G)).trans (Uniform.tint G _)).continuous)
    have hg i : ∀ᶠ y:Y in 𝓝 0, windmill F y i∈ ball 0 O.radius:= (hl i).continuousAt.eventually (ball_mem_nhds (0:G.Color) h.patch)
    filter_upwards [Filter.eventually_all.mpr hg] with y hy i _ using hy i

variable (P:ℝ → Config G c)(W:ℝ→Poll.Body (Precision.Key F G)) (H:ℝ→F.Slice G→ℝ) {A B:ℝ×Poll.Body (Precision.Key F G)→ℝ}
-- general equality on punctured germ (positive t). or t≠0 only; could ask ∀ᶠ w in 𝓝 joint if nonzero. e^penalty folded in H. Future marks.
lemma angle_comes (h:LocalRatio O) (hh:∀ᶠ t in Tested.germ, StronglyMeasurable (H t)) (hm:Tendsto W (𝓝 0) (𝓝 0))
    (H':∀ᶠ x in 𝓝 (0:ℝ×Poll.Body (Precision.Key F G)),0<x.1→ H x.1 (draw F (P x.1) (W x.1+x.2)) * pay O (windmill F (W x.1+x.2))=B x*Real.exp (-A x/x.1^2)): ∀ᶠ δ in Tested.germ, angle F P W H δ=ᶠ[Tested.germ] stick volume A B δ:= by
   have he : Tendsto (fun x:Ω=> W x.1+x.2) (𝓝 0) (𝓝 0):= by rw [← add_zero (0:Y)]; exact (hm.comp continuous_fst.continuousAt.tendsto).add (@continuous_snd ℝ Y _ _).continuousAt.tendsto -- edit
   filter_upwards [Tested.eventually_pos,round _ ((he.eventually (wind_gate F O h)).and H')] with δ hd hF
   filter_upwards [Tested.eventually_small hd, hh] with t ht hy
   unfold angle collar
   have hw (x:Y) (hz : ‖x‖ ≤ δ/t): ‖t•x‖ ≤ δ:=by rw [norm_smul_of_nonneg ht.1.le,mul_comm]; exact (le_div_iff₀ ht.1).mp hz
   have hg x hx:= hF t ((abs_lt.mpr ⟨by linarith only [hd,ht.1],ht.2⟩).le) (t• x) (hw x hx)
   rw [stick_closed volume _ _ ht.1 hd, cubits F O _ _ _ _ _ ht.1 h (fun x hx=> (hg x hx).1) hy, inv_mul_cancel_left₀ (pow_pos ht.1 _|>.ne')]; apply setIntegral_congr_fun measurableSet_closedBall; intro y hy; exact (mul_comm ..).trans ((hg y (mem_closedBall_zero_iff.mp hy)).2 ht.1)
end YM.AllOrder.Laplace
