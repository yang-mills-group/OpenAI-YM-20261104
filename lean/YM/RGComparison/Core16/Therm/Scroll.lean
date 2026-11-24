import YM.PertExtension.Interior
import YM.PertExtension.Aspiration
/-!
# Pulling Taylor/Wick prescription onto a ray of external coarse potential

Use Radial on x=phase parameter AND fine coordinates; x is pulled out by delta.
In order to have the full ambient quadratic positive after completing square of all
fine coordinates, we will add a temporary pure quadratic in bare coarse parameter
(algebraically removes; external classical log kept exactly). These are estimates
of genuine integrals of germs with a radial test, not of the full-sector real group
push. Constants FOR THIS period; use for independence of joint log jet identification.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Therm
open Function Filter MeasureTheory Set Metric Asymptotics
open scoped Topology ContDiff NNReal
open PertExtension PertExtension.Series Tested Radial
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (K f : ℝ × E→ℝ)

def screen (μ : Measure E) (x : ℝ) := μ.map fun y => (x,y)

lemma screen_embedding (x : ℝ) : MeasurableEmbedding (fun y : E=> (x,y)) := by
  letI := FiniteDimensional.complete ℝ E
  apply Topology.IsClosedEmbedding.measurableEmbedding
  apply Isometry.isClosedEmbedding; rw [isometry_iff_dist_eq]; simp

instance [μ.HasTemperateGrowth] (x : ℝ) : (screen μ x).HasTemperateGrowth := by
  refine ⟨μ.integrablePower, (screen_embedding (E:=E) x).integrable_map_iff.mpr ?_⟩
  apply (μ.integrable_pow_neg_integrablePower).mono'
  · have hp : Continuous (fun i : E=> (1+‖(x,i)‖) ^ (-(μ.integrablePower : ℝ))) := by
      apply Continuous.rpow (by fun_prop) continuous_const
      intro i; exact Or.inl (by positivity)
    exact hp.aestronglyMeasurable
  apply Eventually.of_forall
  intro i
  change ‖(1+‖(x,i)‖) ^ (-(μ.integrablePower : ℝ))‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]; exact Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [Prod.norm_def]; simp) (neg_nonpos.mpr (Nat.cast_nonneg _))

def localFull (x t r : ℝ): ℝ := Radial.partialSum (screen μ x) K f r t

def chartLine (x t r : ℝ): ℝ := ∫ y in Radial.disc t r, projection K f t (x,y) ∂μ

def stamp (x : ℝ) (j : ℕ) : ℝ := Radial.moment (screen μ x) K f j

theorem stamp_moment (x j) : stamp μ K f x j=∫ y:E,Radial.normTerm K f j (x,y) ∂μ :=
  (screen_embedding (E:=E) x).integral_map _

lemma affordability [μ.HasTemperateGrowth] (k : ℕ) (x : ℝ) (hF : Stationary f) (hg : ContDiffAt ℝ ∞ K 0) (he : ∃ c>0, ∀ u : ℝ×E,c*‖u‖^2 ≤ jet f 2 u) : Integrable (fun y:E=>normTerm K f k (x,y)) μ :=
  (screen_embedding (E:=E) x).integrable_map_iff.mp <| hF.integrableTerm (screen μ x) hg he

lemma local_chartLine {t x r : ℝ} (ht : 0 ≤ t) (hx : t * ‖x‖ < r) : localFull μ K f x t r = chartLine μ K f x t r := by
  unfold localFull Radial.partialSum screen chartLine; rw [(screen_embedding (E:=E) x).setIntegral_map]
  congr 2; ext y
  simp only [mem_preimage, disc_mem ht,Prod.norm_def,mul_max_of_nonneg _ _ ht,max_lt_iff,hx,true_and]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma stamp_protect {K' f' : ℝ × E → ℝ} (hK : K =ᶠ[𝓝 0] K') (hf : f =ᶠ[𝓝 0] f') : stamp μ K f=stamp μ K' f' := by
  have hjet {F H : ℝ × E→ℝ} (h : F =ᶠ[𝓝 0] H) : jet F = jet H := by
    funext j u; rw [jet,jet,(h.iteratedFDeriv ℝ j).self_of_nhds]
  have hl : layers f = layers f' := funext fun j=>funext fun x=>by rw [layers,layers,hjet hf]
  funext x j
  unfold stamp moment; simp only [normTerm, Radial.kernel, integrandSeries,hjet hK,hjet hf,hl]

omit μ in
private lemma guards {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
    (f : Y→ℝ) (h : ContDiffAt ℝ ω f 0) : ∃ f' : Y→ℝ, Measurable f' ∧ f =ᶠ[𝓝 0] f' := by
  classical
  obtain ⟨d,hd,he⟩:= Metric.mem_nhds_iff.mp (h.eventually (by simp))
  let S:= ball (0:Y) d
  have hx : ContinuousOn f S:= fun x hx=>(show ContDiffAt ℝ ω f x from he hx).continuousAt.continuousWithinAt
  refine ⟨S.piecewise f (fun _=>0), hx.measurable_piecewise continuousOn_const isOpen_ball.measurableSet,?_⟩
  filter_upwards [ball_mem_nhds (0:Y) hd] with y hy; exact (piecewise_eq_of_mem _ _ _ hy).symm

/-- At EACH local direction and fixed order. Constants in the PERT coefficient comparison
are after choosing everything in this finite calculation, not pre-movement content. -/
theorem aspirates [μ.HasTemperateGrowth] (k : ℕ) (x : ℝ) (h : Stationary f) (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω K 0) (he : ∃ c>0, ∀ u : ℝ×E,c*‖u‖^2 ≤ jet f 2 u) :
    ∃ d>0, ∀ r∈Ioo 0 d, Tested.Bill (k+1) ((fun t => chartLine μ K f x t r) - Tested.peval (stamp μ K f x) k) := by
  obtain ⟨f',ha,hu⟩:= guards f hf
  obtain ⟨K',hb,hv⟩:= guards K hg
  obtain ⟨γ,hγ,hψ⟩:= Metric.mem_nhds_iff.mp (hu.and hv)
  have hk (v : ℝ×E) (k) : jet f' k v = jet f k v := by rw [jet,jet,(hu.symm.iteratedFDeriv ℝ k).self_of_nhds]
  obtain ⟨δ,hδ,hd⟩:= (show Stationary f' from ⟨h.smooth.congr_of_eventuallyEq hu.symm, hu.symm.self_of_nhds.trans h.base0, fun i=>(hk i 1).trans (h.base1 i)⟩).rescale_estimate
    (screen μ x) ((hg.congr_of_eventuallyEq hv.symm).of_le le_top) hb ha (by simpa only [hk] using he) k
  refine ⟨min δ γ,lt_min hδ hγ,fun r hr=>?_⟩; obtain ⟨C,hC⟩:= hd r ⟨hr.1,hr.2.trans_le (min_le_left ..)⟩
  rw [stamp_protect μ K f hv hu]
  refine ⟨|C|,by positivity,?_⟩
  have hX : Tendsto (fun t : ℝ=>t*‖x‖) Tested.germ (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds; simpa only [id_eq,zero_mul] using (continuous_id.mul_const ‖x‖).tendsto 0
  filter_upwards [eventually_pos,hC,hX.eventually (eventually_lt_nhds hr.1)] with t (ht : 0 < t) hC (h : t*‖x‖<r)
  rw [Pi.sub_apply, show chartLine μ K f x t r=localFull μ K' f' x t r by
    rw [local_chartLine _ _ _ ht.le h]; refine setIntegral_congr_fun (disc_meas ..) fun y hy=> ?_
    have hz : t*‖(x,y)‖<r := by rw [Prod.norm_def,mul_max_of_nonneg _ _ ht.le]; exact max_lt h ((disc_mem ht.le r y).mp hy)
    have hp : t • (x,y)∈ ball 0 γ := (disc_mem (E:=ℝ × E) ht.le γ _).mpr (hz.trans (hr.2.trans_le (min_le_right ..)))
    rw [projection_eq,projection_eq,(hψ hp).1,(hψ hp).2]]
  exact hC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

omit μ in
lemma disc_balls (t r : ℝ)(ht : 0 < t) : Radial.disc (E:=E) t r=ball 0 (r/t) := by
  ext y; rw [disc_mem ht.le, mem_ball_zero_iff]; rw [lt_div_iff₀ ht]; rw [mul_comm]

def lit (K f : ℝ × E → ℝ) : Prop :=
  ContDiffAt ℝ ω K 0 ∧ ContDiffAt ℝ ω f 0 ∧ 0 < K 0

namespace lit
lemma ranges {K f : ℝ × E → ℝ} (h : lit K f) [IsFiniteMeasureOnCompacts μ](x : ℝ) :
    ∃ d>0, ∀ r ∈ Ioo 0 d, ∀ᶠ t in Tested.germ, IntegrableOn (fun y : E=> Radial.projection K f t (x,y)) (Radial.disc t r) μ ∧
      0 ≤ᵐ[μ.restrict (disc t r)] (fun y : E=> Radial.projection K f t (x,y)) := by
  obtain ⟨δ,hδ,hA⟩:= Metric.mem_nhds_iff.mp (((h.1.eventually (by simp)).and (h.2.1.eventually (by simp))).and
    (h.1.continuousAt.tendsto.eventually (eventually_gt_nhds h.2.2)))
  refine ⟨δ,hδ,fun r hr=> ?_⟩
  have hX : Tendsto (fun t : ℝ=>t*‖x‖) Tested.germ (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds; simpa only [id_eq,zero_mul] using (continuous_id.mul_const ‖x‖).tendsto 0
  filter_upwards [Tested.eventually_pos,hX.eventually (eventually_lt_nhds hr.1)] with t ht (hh : t*‖x‖ < r)
  let K₀ := closedBall (0:E) (r/t); let Y : E→ℝ × E:= fun i=> t • (x,i); have he : Continuous Y := by unfold Y; fun_prop
  have hp (y : E) (hy : y∈ K₀) : Y y∈ ball 0 δ := by
    rw [mem_closedBall_zero_iff] at hy; change ‖y‖ ≤ _ at hy
    apply (disc_mem ht.le δ (x,y)).mpr
    rw [Prod.norm_def,mul_max_of_nonneg _ _ ht.le]; exact max_lt (hh.trans hr.2) (lt_of_le_of_lt (mul_comm ..|>.trans_le ((le_div_iff₀ ht).mp hy)) hr.2)
  rw [disc_balls t r ht]
  refine ⟨IntegrableOn.mono_set (t:=K₀) (ContinuousOn.integrableOn_compact (isCompact_closedBall ..) ?_) ball_subset_closedBall,?_⟩
  · simp_rw [projection_eq]; exact fun y hy=> (((hA (hp y hy)).1.1.continuousAt.comp he.continuousAt).mul (Real.continuous_exp.continuousAt.comp (((hA (hp y hy)).1.2.continuousAt.comp he.continuousAt).neg.div_const _))).continuousWithinAt
  filter_upwards [ae_restrict_mem (s:=ball (0:E) (r/t)) isOpen_ball.measurableSet] with y hy
  change 0 ≤ _; rw [projection_eq]; exact mul_nonneg (le_of_lt (hA (hp y (ball_subset_closedBall hy))).2) (Real.exp_pos _).le
end lit
end YM.RGComparison.Core16.Therm
