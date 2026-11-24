import YM.Integration.FVA1Physical.Wilson.MovingSources
import YM.Integration.FVA1Physical.Wilson.MovingCoercive

/-! Exact restriction of the physical multilevel Haar integral to the scaled
Lie-algebra chart. The source may depend on every fine and retained field
and on the coupling; only its local representative is fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Metric Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FVA2.CityHistory FVA2.RayScatter
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)
abbrev PathSource := ℝ → Config G c → Fields G d → ℝ

def CommonGerm (J : PathSource (G:=G) d) (W : SpaceF G d → ℝ) : Prop :=
  ∀ᶠ z in 𝓝 (0:SpaceF G d), ∀ g > (0:ℝ), J g (expLinks G _ z.2) (d.tablePath z.1) = W z

def chartAmplitude (Z : ChartRatio G) (a : ℕ → ℝ) (t : d.Tags) (W : SpaceF G d → ℝ)
    (x : SpaceF G d) : ℝ :=
  jacobian Z x.1 * (Fintype.card d.Tags : ℝ)⁻¹ * Real.exp (-consume d t a x) * W x

theorem chartAmplitude_analytic {Z : ChartRatio G} (hZ : LocalRatio Z) (h : d.OK G)
    (a : ℕ → ℝ) (t : d.Tags) {W : SpaceF G d → ℝ} (hw : ContDiffAt ℝ ω W 0) :
    ContDiffAt ℝ ω (chartAmplitude d Z a t W) 0 :=
  ((((Chart.Ratio.jacobian_smooth hZ).comp (f:=Prod.fst) 0 contDiffAt_fst).mul
    contDiffAt_const).mul ((thermal d t h a).neg.exp)).mul hw

/-- The artificial scalar Gaussian produces exactly the common factor
`exp (-1)` on this slice, including with a nonzero retained ray. -/
theorem path_inside (h : d.OK G) {Z : ChartRatio G} (hZ : LocalRatio Z)
    (a : ℕ → ℝ) (t : d.Tags) (u : Pins G c)
    (J : PathSource (G:=G) d) (hJ : ∀ g > (0:ℝ), ∀ V, Measurable (J g V))
    (W : SpaceF G d → ℝ) (hw : CommonGerm d J W) :
    ∃ δ > (0:ℝ), δ ≤ small G Z ∧ ∀ r ∈ Ioo 0 δ, ∀ᶠ g in Tested.germ,
      Real.exp (-1) * pathRegion d g a t (J g) (expLinks G _ (g • u)) (chamber G d.Links r) =
      Therm.chartLine (tangent G d.Links) (chartAmplitude d Z a t W ∘ recover u)
        (rayPhase d t u) 1 g r := by
  obtain ⟨b,hb,loc⟩ := Metric.mem_nhds_iff.mp (hw.and (likeliest d h))
  refine ⟨min b (small G Z),lt_min hb (Chart.Ratio.small_pos hZ),min_le_right ..,?_⟩
  intro r hr
  have coarse : Tendsto (fun g : ℝ => g • u) Tested.germ (𝓝 0) := by
    have ht : Continuous (fun g : ℝ => g • u) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (ht.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [eventually_pos,coarse.eventually (ball_mem_nhds _ hb)] with g hg hu
  let E := Coordinates G d
  let V := expLinks G _ (g • u)
  let U := pathAmplitude d (offset a g) t (J g) V
  let f (z : E) := jacobian Z z * U (d.tablePath z)
  let μ := tangent G d.Links
  let B := ball (0:E) r
  let I := disc (E:=E) g r
  have iden (v : E) : B.indicator f (g • v) = I.indicator (fun y => f (g • y)) v := by
    by_cases e : v ∈ I
    · rw [indicator_of_mem e,indicator_of_mem (show g • v ∈ B from e)]
    rw [indicator_of_notMem e,indicator_of_notMem (show g • v ∉ B from e)]
  have changeVar := Measure.integral_comp_smul_of_nonneg μ (B.indicator f) g (hR:=hg.le)
  simp_rw [iden] at changeVar
  rw [integral_indicator (s:=I) (disc_meas ..),integral_indicator (s:=B) isOpen_ball.measurableSet] at changeVar
  have haar : (∫ x in chamber G d.Links r, U x ∂ d.measure G) = ∫ x in B, f x ∂μ :=
    Chart.Ratio.chamber_integral hZ U (pathAmplitude_measurable d h _ t _ V (hJ g hg V))
      (hr.2.trans_le (min_le_right ..)) hr.1
  change Real.exp (-1)*((g^Module.finrank ℝ E)⁻¹ * ∫ x in _, U x ∂d.measure G) = _
  rw [haar,show (g^Module.finrank ℝ E)⁻¹ * _ = _ from changeVar.symm,← integral_const_mul]
  apply setIntegral_congr_fun (disc_meas ..)
  intro v hv
  let z : SpaceF G d := (g • v, g • u)
  let y := d.tablePath (g • v)
  have hz : z ∈ ball 0 b := by
    rw [mem_ball_zero_iff,Prod.norm_def]
    exact max_lt ((mem_ball_zero_iff.mp (show g • v ∈ B from hv)).trans
      (hr.2.trans_le (min_le_left ..))) (mem_ball_zero_iff.mp hu)
  have hray : recover u (g • ((1:ℝ),v)) = z := by simp [recover,z]
  have hphase : rayPhase d t u (g • ((1:ℝ),v)) = g^2 + d.action t V y := by
    change 1*(g*1)^2 + consume d t 1 ((recover u) (g • ((1:ℝ),v))) = _
    rw [mul_one,one_mul,hray]; rfl
  have hexp : Real.exp (-(g^2+d.action t V y)/g^2) =
      Real.exp (-1) * Real.exp (-(d.action t V y)/g^2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hc := (loc hz).1 g hg
  have hp := (loc hz).2 t
  change J g V y = W z at hc
  change d.probability t y = _ at hp
  change Real.exp (-1) * f (g • v) = projection (chartAmplitude d Z a t W ∘ recover u) (rayPhase d t u) g (1,v)
  rw [projection_eq,hphase,hexp,Function.comp_apply,hray]
  change Real.exp (-1) * (jacobian Z (g • v) * (d.probability t y *
    Real.exp (-d.account (offset a g) t V y) * J g V y)) =
    (jacobian Z (g • v) * _ * Real.exp (-d.account a t V y) * W z) * _
  rw [account_offset,neg_add,Real.exp_add,hc,hp,show
    -(g⁻¹^2*d.action t V y) = -d.action t V y / g^2 by rw [inv_pow,div_eq_mul_inv]; ring]
  ring

end YM.Integration.FVA1Physical.Wilson
