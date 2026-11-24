import YM.RGComparison.Core16.Forge.Raise
import YM.Push.STRESS_FLUX.Haar

/-!
# Link-coordinate Schwinger variation for the true near-field estimator

Use analytic curvature coordinate even though actual FK definition is through lieExp in the
conditional block. Need pullback theorem to actual Fitted and Fk clients; never solve in another
gauge. The deterministic wall purchases volumes before these IBP in this Fk formulation. Work also
with genuinely conditioned variates after likelihood summation; require only Envelope plus existence
of the one direction derivative (payment at EVERY point). This permits indicators on other links and
strict nonanalytic predictors at their exterior.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Pressure Push
open Precision Forge Forge.Hut Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge} {ι:Type} (k:G.ColorIndex)
abbrev colors (G:Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ

-- invertible curvature coords only as **analytic GERM** (Lie exp chart precomposed). No second
-- density representation relying on this rather than actual F measure.
def turn (x : G.Color) := G.curvature (G.lieExp x)
lemma turn_hot : ContDiff ℝ ω (turn (G:=G)):=by
    rw [contDiff_iff_contDiffAt]; intro x; apply curvature_diff_mat
    exact G.exp_jet.contDiffAt
lemma turn_roll : HasFDerivAt (turn (G:=G)) (ContinuousLinearEquiv.refl ℝ G.Color).toContinuousLinearMap 0:=by
    have h := @turn_hot G |>.contDiffAt (x:=0) |>.differentiableAt (by simp)|>.hasFDerivAt
    rw [show (ContinuousLinearEquiv.refl ℝ G.Color).toContinuousLinearMap= fderiv ℝ turn 0 from ?_]; exact h
    apply ContinuousLinearMap.ext; intro x
    have hp : HasDerivAt (fun t:ℝ=> t • x) x 0:= by simpa using! ((hasDerivAt_id (x:=(0:ℝ))).smul_const x)
    exact (G.leading_curvature x).unique ((show HasFDerivAt (turn (G:=G)) (fderiv ℝ (turn (G:=G)) 0) ((0:ℝ) • x) by rw [zero_smul]; exact h).comp_hasDerivAt (f:=fun t:ℝ=>t • x) 0 hp)
lemma turn_zero : turn (0:G.Color)=0:= by simp [turn]

def axis := @turn_hot G|>.contDiffAt.toOpenPartialHomeomorph _ (@turn_roll G) (by simp)

def launch (x:G.Color):= G.lieExp (axis.symm x)
lemma axis_zero : axis.symm (0:G.Color)=0 :=by
    let T:=axis (G:=G); have h :(0:G.Color)∈T.source:=ContDiffAt.mem_toOpenPartialHomeomorph_source ..
    exact (congr_arg _ (turn_zero (G:=G))).symm.trans (T.left_inv h)
lemma launch_zero : launch (0:G.Color)=1:=by rw [launch,axis_zero]; simp
lemma axis_hot : ContDiffAt ℝ ω (@axis G).symm 0 := by
    rw [← turn_zero (G:=G)] -- target all
    exact (@turn_hot G|>.contDiffAt (x:=0)).to_localInverse turn_roll (by simp)
lemma launch_cont : ContinuousAt (launch (G:=G)) 0:= by unfold launch; exact ((show Continuous G.lieExp from by fun_prop).continuousAt.comp axis_hot.continuousAt)
lemma launch_data : ContDiffAt ℝ ω (fun x=>G.mat (launch x)) 0:=by
    exact G.exp_jet.contDiffAt.comp (f:=axis.symm) _ axis_hot
lemma genesis : ∀ᶠ x:G.Color in 𝓝 0, G.curvature (launch x)=x:=by
    let T:=@axis G; have h:0∈T.source:= ContDiffAt.mem_toOpenPartialHomeomorph_source ..; have hh: T 0=0:= turn_zero
    filter_upwards [T.open_target.mem_nhds (show 0∈T.target from hh ▸ T.map_source h)] with x hx; exact T.right_inv hx
lemma leaving : ∀ᶠ x:G.El in 𝓝 1, launch (G.curvature x)=x:=by
    have h: Tendsto (fun x:G.El=> G.plog (G.mat x)) (𝓝 1) (𝓝 0) := by
       have he : G.plog (G.mat 1)=0:= by simp
       rw [← he]; exact (G.mat_one.symm ▸ G.plog_diff.continuousAt : ContinuousAt G.plog (G.mat 1)).tendsto.comp G.continuous_mat.continuousAt.tendsto
    let A:=@axis G; have ht:0∈A.source:= ContDiffAt.mem_toOpenPartialHomeomorph_source ..
    filter_upwards [G.plog_right,h.eventually (A.open_source.mem_nhds ht)] with x hx hz
    let y:= G.plog (G.mat x); change G.lieExp y=x at hx; rw [←hx]
    exact congr_arg G.lieExp (A.left_inv (show y∈A.source from hz))

-- flow on all finitely counted links.
def spin (k:G.ColorIndex)(x:G.El)(t:ℝ):= G.lieExp (t • colors G k)*x
lemma spin_zero (x:G.El): spin k x 0=x:=by simp [spin]
@[fun_prop] lemma spin_cont : Continuous (fun t:G.El×ℝ=>spin k t.1 t.2):=by unfold spin; fun_prop

lemma spin_mat (x:G.El): HasDerivAt (fun t=> G.mat (spin k x t)) (G.colorMat (colors G k) * G.mat x) 0:=by
    simp only [spin,G.mat_mul]
    apply HasDerivAt.mul_const; simp only [G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat (colors G k)) (0:ℝ)

def roll (A : G.Mat): G.Color:= G.projectColor ((1/2 : ℝ) • (G.colorMat (colors G k)* A - star (G.colorMat (colors G k)*A)))
lemma roll_hot : ContDiff ℝ ω (roll k):=by
    unfold roll; apply G.projectColor.toContinuousLinearMap.contDiff.comp (g:=_); let u (x:G.Mat):=G.colorMat (colors G k)*x; have h : ContDiff ℝ ω u:= contDiff_const.mul contDiff_id
    exact (h.sub ((starL' ℝ (A:=G.Mat)).contDiff.comp h)).const_smul _
lemma sleeve (x:G.El): HasDerivAt (fun t=> G.curvature (spin k x t)) (roll k (G.mat x)) 0:=by
    simp_rw [Gauge.curvature,G.mat_inv]; exact G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (((spin_mat k x).sub (spin_mat k x).star).const_smul (1/2:ℝ))
lemma roll_one : roll k (1:G.Mat)=colors G k:=by
    rw [← G.mat_one]; apply (sleeve k 1).unique; simpa only [spin,mul_one] using G.leading_curvature (colors G k)

variable (i:ι)
def gust (t:ℝ)(x:Sky G ι):Sky G ι:=fun j=> if j=i then spin k (x j) t else x j
lemma gust_zero (x:Sky G ι): gust k i 0 x=x:=by funext j; simp [gust,spin_zero]
lemma gust_cont : Continuous (fun p:ℝ×Sky G ι=>gust k i p.1 p.2):=by
    refine continuous_pi fun j=>?_ ; unfold gust; split
    · unfold spin; fun_prop
    exact (continuous_apply (A:=fun _:ι=>G.El) j).comp continuous_snd
lemma gust_add (s t : ℝ) (x:Sky G ι): gust k i (s+t) x=gust k i s (gust k i t x):=by
    funext j; unfold gust; split
    · unfold spin; rw [← mul_assoc]; congr 1
      apply G.mat_injective
      rw [G.mat_mul]; simp only [G.mat_lieExp,map_smul,add_smul,map_add]; letI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _; exact NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (colors G k))).smul_left s).smul_right t)
    · rfl

variable [Fintype ι]
lemma preserves (r:ℝ) : MeasurePreserving (gust k i r) (skillet G ι) (skillet G ι):=by
    refine measurePreserving_pi _ _ (f:=fun j x=> if j=i then spin k x r else x) (fun j=> ?_)
    by_cases h:j=i <;> simp only [h, ↓reduceIte]; exact measurePreserving_mul_left G.probHaar (G.lieExp (r • colors G k)); exact MeasurePreserving.id _

-- Haar for Sky conditional instead of all Config. No variation in density allowed silently.
theorem air {f f' : Sky G ι→ℝ}(hf:Envelope f)(hp:Envelope f') (h:∀ x:Sky G ι, HasDerivAt (fun t:ℝ=>f (gust k i t x)) (f' x) 0) :
    ∫ x,f' x ∂skillet G ι=0:=by
    let F (t:ℝ)(x: Sky G ι):= f (gust k i t x)
    let F' (t:ℝ)(x: Sky G ι):= f' (gust k i t x)
    let μ:= skillet G ι
    obtain ⟨-,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (F:=F) (x₀:= (0:ℝ)) (F':=F') (bound:=fun _=> hp.cost.choose) (s:=Set.univ) Filter.univ_mem (.of_forall (fun t=> (hf.meas.comp (preserves k i t).measurable).aestronglyMeasurable)) (by unfold F; simpa only [gust_zero] using hf.integrable μ) (by unfold F'; simpa only [gust_zero] using hp.meas.aestronglyMeasurable) (.of_forall (fun x t _=> hp.cost.choose_spec _)) (integrable_const _) (Eventually.of_forall fun x t _ => by
      have hh := (neg_add_cancel t|>.symm ▸ h (gust k i t x) : HasDerivAt (fun s => f (gust k i s (gust k i t x))) (F' t x) (-t+t)); simpa only [F,← gust_add,neg_add_cancel_comm] using! hh.comp_const_add (-t) t)
    have he t: ∫ x,F t x∂μ=∫ x,f x∂μ:=by
      have hx:= preserves k i t; have hw:= integral_map (μ:=μ) (φ:=gust k i t) (f:=f) hx.measurable.aemeasurable hf.meas.aestronglyMeasurable
      rw [show Measure.map (gust k i t) μ=μ from hx.map_eq] at hw; exact hw.symm
    simp only [F',gust_zero,he] at hd; exact hd.unique (hasDerivAt_const ..)
end YM.RGComparison.Core16.Lumen
