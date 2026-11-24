import YM.Comparison.RG02.Laplace.Trunc
import YM.Comparison.RG02.Integral.Healthy
import YM.Comparison.RG02.Integral.Comparison
import YM.PertExtension.Tails
/-!
# Identifying the integrand coefficients after a small aperture, at fixed period

Before Hardy circles. Keep linear drift (F.ρ') & use K.critical vacuum. Cost of
 exponential (g Zonals with slight Gaussian exponential commitment) valid per THIS regulator.
 Do not assert any RG cost like `|g_m|^r poly` with this invocation of Fernique.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] {R : Census V}
section
lemma gauss_table (x : Gaussian.Table I) : IsGaussian (Gaussian.cloud x) := by
   change IsGaussian ((multivariateGaussian 0 x).map (WithLp.ofLp (p:=2) : EuclideanSpace ℝ I → I→ℝ))
   let L := (WithLp.linearEquiv 2 ℝ (I→ℝ)).toContinuousLinearEquiv
   change IsGaussian ((multivariateGaussian 0 x) |>.map L); infer_instance
end

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g c₀:ℝ)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)
local notation "L"=> Precision.Key F G → ℝ
local notation "μ"=> Gaussian.cloud (K.covariance F t)
local notation "ζ"=> Bulk.translated K F x

def room (v : L) := (Radial.zone (E:=Bulk.Joint S F (G:=G))).w (ζ v)
lemma room_cost (v : L) : room K F x v = 1+‖ζ v‖:=rfl
lemma room_funded (v : L) : 1 ≤ room K F x v:=le_add_of_nonneg_right (norm_nonneg _)
lemma room_pos (v : L) : 0 < room K F x v := zero_lt_one.trans_le (room_funded ..)
lemma translated_cont : Continuous ζ := Continuous.add continuous_const (Bulk.hinge F).continuous_on_pi

lemma gauss_translated : ∃ r:ℝ, 0<r ∧ ∀ p:ℕ, Integrable (fun v=> (room K F x v)^p* Radial.shade r (ζ v)) μ := by
   letI:= gauss_table (K.covariance F t)
   let V := Bulk.Joint S (G:=G) F
   letI : MeasurableSpace (Bulk.Joint S (G:=G) F):= borel _
   haveI : BorelSpace (Bulk.Joint S (G:=G) F) := ⟨rfl⟩
   let m' := (μ).map ζ
   let T : (Precision.Key F G→ℝ)→L[ℝ] Bulk.Joint S (G:=G) F:= (Bulk.hinge F).toContinuousLinearMap
   let S' := Bulk.stage K F x
   have hT:= translated_cont K F x
   haveI : IsGaussian m':= by
      unfold m'
      rw [show (μ).map ζ=((μ).map T).map (S' + ·) by rw [Measure.map_map (show Measurable (S'+·) by fun_prop) T.continuous.measurable]; rfl]; infer_instance
   obtain ⟨C,hC,H⟩:= IsGaussian.exists_integrable_exp_sq m'; let r:= C/2
   have hr : 0<r:= half_pos hC; refine ⟨r,hr,fun p=>?_⟩
   -- absorb every power
   let f (x : V):= (1+‖x‖)^p * Radial.shade r x
   have hc:Continuous f:= by unfold f Radial.shade; fun_prop
   obtain ⟨a,ha,h⟩:= Radial.bounded_exp hr p
   have he : Integrable f m' := (H.const_mul a).mono' hc.aestronglyMeasurable (Eventually.of_forall fun y=>by
      have hp : 0 ≤ f y:= by unfold f Radial.shade; positivity
      rw [Real.norm_of_nonneg hp]
      have hh:=h ‖y‖ (norm_nonneg _)
      calc
       _ = (1+‖y‖)^p * Real.exp (-r*‖y‖^2) * Real.exp (C*‖y‖^2) := by unfold f Radial.shade; rw [mul_assoc,← Real.exp_add]; unfold r; ring_nf
       _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le)
   exact he.comp_aemeasurable hT.measurable.aemeasurable

variable {c₁ k δ : ℝ} (r : ℕ) (s : R.Mode)
-- Demand on chosen window for extent measurements

def Small (A : ℝ → Set (F.Slice G)) (δ : ℝ): Prop := ∀ᶠ g in along,∀ v : Precision.Key F G→ℝ, v∈ scope K F g x (A g) → g*room K F x v≤δ

-- cost of inside-chart reg Taylor (fixed β parameter thresholds). no need inverse Hessian bound except implicit Gaussian integrability here.
-- `A` often fixed while shrinking `g`--which only tending to 0⁺ on this ring, not physical iteration.
variable (A : ℝ → Set (F.Slice G))
omit [Fintype V] in
lemma volume_bill {Y : Type*} [MeasurableSpace Y] {v : Measure Y} {a:Y→ℝ} (ha : ∀ y, 0≤a y) (hI : Integrable a v) {g:ℝ → Lit R Y}
    (C : ℝ) (he : 0≤C) (h : ∀ᶠ t in along, ∀ y, ‖(g t y).part s‖ ≤ (C*t^r)*a y) :
    Bill r fun t=> (charge v (g t)).part s := by
  refine ⟨C*∫ y,a y ∂v,mul_nonneg he (integral_nonneg ha),?_⟩
  filter_upwards [h,eventually_pos] with t H ht; rw [components]
  apply (norm_integral_le_of_norm_le ( (hI).const_mul (C*t^r)) (Eventually.of_forall (fun y=> H y))).trans_eq; rw [integral_const_mul]; ring
variable (hW : Bulk.Well W)
include hW

lemma park : ∃ δ : ℝ,0 < δ ∧ ∀ A, Small K F x A δ → Bill (r+1) (fun g=> (charge μ (drift K F t g x W (A g) r)).part s) := by
   let α:=Assembly.numeric W.power (Bulk.markFn S F W) (Bulk.geometric K F t W)
   obtain ⟨c₁,hC,he⟩:=gauss_translated K F t x
   let paid := Radial.shade (E:=Bulk.Joint S F (G:=G)) c₁
   let hP:= Bulk.geometric_ready K F t W hW
   have hz := Assembly.radial_comparison W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) hP hC
   obtain ⟨δ,C,p,hδ,H,h⟩:= (Assembly.Zonal.remainder _ hz s r).cost
   let M (v : L):= room K F x v ^ p * paid (ζ v)
   have hm (v:L): 0 ≤ M v := mul_nonneg (pow_nonneg (room_pos ..).le _) (Real.exp_pos _).le
   refine ⟨δ,hδ,fun A ha=> ?_⟩; apply volume_bill (r+1) s hm (he p) C H
   filter_upwards [Tested.eventually_pos,ha] with t' ht hF v
   by_cases hv : v∈scope K F t' x (A t')
   · unfold drift; rw [Set.indicator_of_mem hv, Pi.sub_apply, Extra.Trajectories.part_sub]; refine (h (ζ v) t' ht (hF v hv)).trans_eq ?_
     unfold M room paid; ring
   unfold drift; rw [Set.indicator_of_notMem hv,Poly.part_nil, norm_zero]
   exact mul_nonneg (mul_nonneg H (pow_nonneg ht.le _)) (hm _)
end YM.Comparison.RG02.Laplace
