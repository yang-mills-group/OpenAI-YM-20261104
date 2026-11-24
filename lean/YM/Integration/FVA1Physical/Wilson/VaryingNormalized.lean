import YM.Integration.FVA1Physical.Wilson.VaryingWick
import YM.Integration.FVA1Physical.Wilson.MovingVacuumBank

/-! Normalized, all-order physical matching at each fixed finite geometry
with genuinely varying inherited couplings. Both the signed source and the
vacuum use the complete tag measure and the same nonlinear clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FVA2 FVA2.CityHistory FVA2.RayScatter
open FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Router
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)

structure AnalyticClocks (z : ℕ → ℝ → ℝ) (w : ℕ → PowerSeries ℝ) : Prop where
  hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0
  head : ∀ i ≤ d.depth, z i 0 = 1
  nonneg : ∀ i ≤ d.depth, ∀ g, 0 ≤ z i g
  expansion : ∀ i ≤ d.depth, Aspiration (z i) (term (w i))
  sound : Legacy.SoundZ w

def varyingTotal (u : Pins G c) (z : ℕ → ℝ → ℝ) (J : d.Tags → PathSource (G:=G) d) : ℝ → ℝ :=
  ∑ i, varyingReading d z i u (J i)

variable (Z : ChartRatio G) (hZ : LocalRatio Z) (t : d.Tags) (h : d.Room G)
    (z : ℕ → ℝ → ℝ) (w : ℕ → PowerSeries ℝ) (clock : AnalyticClocks d z w)

def variedVacuum (u : Pins G c) :=
  let D := μLedger d Z t h w
  C (rayGaussian d t h u) * Stack.read u D * (Stack.read 0 D)⁻¹

include hZ in
theorem varied_den {u : Pins G c} :
    constantCoeff (Stack.read u (μLedger d Z t h w)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,Stack.reading_term,coeff_zero_eq_constantCoeff_apply,
    marketZ d Z t h w hZ]
  rfl

private theorem charge_tilt (u : Pins G c) (i : d.Tags) :
    rayFactor d Z i u h = rayGaussian d t h u * rayFactor d Z i 0 h := by
  rw [rayGaussian,← pure_t d i t h]
  unfold rayFactor basePower
  change Real.exp (-1-(retained d i h).flourish u/2)*_ * _ =
    Real.exp (-(retained d i h).flourish u/2) * (Real.exp (-1-(retained d i h).flourish 0/2)*_ * _)
  rw [show (retained d i h).flourish 0 = 0 by simp [Quadratic.flourish],zero_div,sub_zero,
    show -1-(retained d i h).flourish u/2 = -(retained d i h).flourish u/2 + (-1) by ring,Real.exp_add]
  ring

local notation "D₀" => μLedger d Z t h w
local notation "M₀" => (∑ i, rayFactor d Z i 0 h)
local notation "income" => fun (v : Pins G c) => C M₀ * (C (rayGaussian d t h v) * Stack.read v D₀)

include hZ clock in
theorem varying_absolute (u : Pins G c) (J : d.Tags → PathSource (G:=G) d)
    (hJ : ∀ i g, 0<g → ∀ V, Measurable (J i g V)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i g, 0<g → ∀ V x, ‖J i g V x‖ ≤ B) (W : SpaceF G d → ℝ)
    (germ : ∀ i, CommonGerm d (J i) W) (hw : ContDiffAt ℝ ω W 0) :
    Aspiration (varyingTotal d u z J)
      (term (income u * Stack.read u (premiere d Z t h w (Stack.rise W)))) := by
  have pay i := varying_expansion d h hZ z clock.hot clock.head clock.nonneg i u (J i)
    (hJ i) hB (hb i) W (germ i) hw
  have all := Aspiration.sum Finset.univ _ _ (fun i _ => pay i)
  have bank : (∑ i, mk (varyingCoefficient d Z z i u W)) =
      income u * Stack.read u (premiere d Z t h w (Stack.rise W)) := by
    change _ = (C M₀ * (C (rayGaussian d t h u) * Stack.read u D₀)) * _
    rw [map_sum,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [varied_ticket d Z hZ i h u z w clock.hot clock.head clock.expansion clock.sound W hw,
      _root_.map_mul (Stack.read u),sameFieldDen Z d i t w h,sameFieldOut Z d i t w h,
      charge_tilt d Z t h u i,map_mul]
    ring
  rw [← bank]
  have ec : term (∑ i, mk (varyingCoefficient d Z z i u W)) = ∑ i, varyingCoefficient d Z z i u W := by
    funext k
    simp [term,Finset.sum_apply]
  rw [ec]
  exact all

include hZ clock in
theorem varying_vacuum_absolute (u : Pins G c) :
    Aspiration (varyingTotal d u z 1) (term (income u)) := by
  have H := varying_absolute d Z hZ t h z w clock u 1 (fun _ _ _ _ => measurable_const)
    (B:=1) zero_le_one (fun _ _ _ _ _ => by simp) 1 (fun _ => Eventually.of_forall fun _ _ _ => rfl) contDiffAt_const
  have unit : premiere d Z t h w (Stack.rise (1:SpaceF G d→ℝ)) = 1 := by
    rw [Stack.rise_one]
    unfold premiere Quadratic.fit
    rw [mul_one]
    exact spend_it (marketZ d Z t h w hZ)
  simpa only [unit,map_one,mul_one] using H

include hZ clock in
theorem varying_conditional (u : Pins G c) (J : d.Tags → PathSource (G:=G) d)
    (hJ : ∀ i g, 0<g → ∀ V, Measurable (J i g V)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i g, 0<g → ∀ V x, ‖J i g V x‖ ≤ B) (W : SpaceF G d → ℝ)
    (germ : ∀ i, CommonGerm d (J i) W) (hw : ContDiffAt ℝ ω W 0) :
    Aspiration (varyingTotal d u z J / varyingTotal d u z 1)
      (term (Stack.read u (premiere d Z t h w (Stack.rise W)))) := by
  let f := income u
  let A := Stack.read u (premiere d Z t h w (Stack.rise W))
  have pos : 0 < constantCoeff f := by
    dsimp only [f]
    rw [map_mul,map_mul,constantCoeff_C,constantCoeff_C,varied_den d Z hZ t h w,mul_one]
    exact mul_pos (Finset.sum_pos (fun i _ => rayFactor_pos d Z i 0 hZ h) Finset.univ_nonempty) (Real.exp_pos _)
  have e := (varying_absolute d Z hZ t h z w clock u J hJ hB hb W germ hw).quotient
    (varying_vacuum_absolute d Z hZ t h z w clock u)
    ((coeff_zero_eq_constantCoeff_apply _).trans_ne pos.ne')
  have back (T : PowerSeries ℝ) : mk (term T) = T := PowerSeries.ext (fun i => coeff_mk ..)
  change Aspiration _ (divide (term (f*A)) (term f)) at e
  simpa only [divide,back,mul_right_comm f A,PowerSeries.mul_inv_cancel _ pos.ne',one_mul] using e

include hZ in
theorem varied_head (u : Pins G c) : constantCoeff (variedVacuum d Z t h w u) = rayGaussian d t h u := by
  have hv := (varied_den d Z hZ t h w (u:=0)).trans_ne one_ne_zero
  have hi := congrArg (constantCoeff (R:=ℝ)) (PowerSeries.mul_inv_cancel (Stack.read 0 D₀) hv)
  rw [map_mul,varied_den d Z hZ t h w,one_mul,map_one] at hi
  rw [variedVacuum,map_mul,map_mul,constantCoeff_C,varied_den d Z hZ t h w,mul_one,hi,mul_one]

include h in
private theorem varying_vacuum_total (u : Pins G c) (g : ℝ) :
    varyingTotal d u z 1 g =
    (Real.exp (-1)*(g^Module.finrank ℝ (Coordinates G d))⁻¹*(d.scalar G (clockAt z g))⁻¹) *
      d.vacuum (clockAt z g) (expLinks G _ (g • u)) := by
  rw [← weighted_unit,path_formula (room_ok d h) (clockAt z g) (g:=1) continuous_const (fun _ _ => rfl)]
  have hS := (scalar_pos G d (clockAt z g)).ne'
  simp only [varyingTotal,Finset.sum_apply,varyingReading,clockRegion,setIntegral_univ]
  change (∑ s : d.Tags, Real.exp (-1) * ((g^_)⁻¹ *
    ∫ x, d.integrand (clockAt z g) s 1 (expLinks G _ (g • u)) x ∂d.measure G)) = _
  simp_rw [← Finset.mul_sum]
  field_simp

include hZ clock in
theorem varying_vacuum_ray (u : Pins G c) :
    Aspiration (fun g : ℝ => d.vacuum (clockAt z g) (expLinks G _ (g • u)) /
      d.vacuum (G:=G) (clockAt z g) 1) (term (variedVacuum d Z t h w u)) := by
  let A := income u
  let B := income 0
  have hv := (varied_den d Z hZ t h w (u:=0)).trans_ne one_ne_zero
  have hm : 0 < M₀ := Finset.sum_pos (fun i _ => rayFactor_pos d Z i 0 hZ h) Finset.univ_nonempty
  have hB : constantCoeff B ≠ 0 := by
    dsimp only [B]
    rw [rayGaussian_zero,map_one,one_mul,map_mul,constantCoeff_C,varied_den d Z hZ t h w,mul_one]
    exact hm.ne'
  have estimate := (varying_vacuum_absolute d Z hZ t h z w clock u).quotient
    (varying_vacuum_absolute d Z hZ t h z w clock 0) ((coeff_zero_eq_constantCoeff_apply _).trans_ne hB)
  have back (T : PowerSeries ℝ) : mk (term T) = T := PowerSeries.ext (fun i => coeff_mk ..)
  have eqn : variedVacuum d Z t h w u = A*B⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq hB).mpr
    dsimp only [variedVacuum,A,B]
    rw [rayGaussian_zero,map_one,one_mul]
    calc
      _ = income u * (Stack.read 0 D₀ * (Stack.read 0 D₀)⁻¹) := by ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel _ hv,mul_one]
  rw [eqn]
  intro k
  apply Comparison.RG02.Laplace.bill_congr _ (estimate k)
  filter_upwards [eventually_pos] with g hg
  change varyingTotal d u z 1 g / varyingTotal d 0 z 1 g - peval (divide (term A) (term B)) k g = _
  rw [divide,back,back,varying_vacuum_total d h z u g,varying_vacuum_total d h z 0 g,
    smul_zero,FormalOPE.RG10.Inherit.identity_zero,mul_div_mul_left _ _
    (mul_ne_zero (mul_ne_zero (Real.exp_pos _).ne' (inv_ne_zero (pow_pos hg _).ne')) (inv_ne_zero (scalar_pos ..).ne'))]
  rfl

end YM.Integration.FVA1Physical.Wilson
