import YM.Integration.FVA1Physical.Wilson.VaryingInterior
import YM.Integration.FVA1Physical.Wilson.ClockPhaseJets

/-! Fixed-period, all-order expansion with an analytic inverse-coupling reset at every level. The genuine nonlinear clocks of a realized physical scene are allowed on every retained gauge
direction and at every finite depth. The exponent includes all inherited
action and inverse-coupling offsets. Signed insertions may depend on the
whole path and on the coupling away from their common analytic germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FVA2.RayScatter
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)

def varyingReading (z : ℕ → ℝ → ℝ) (t : d.Tags) (u : Pins G c)
    (J : PathSource (G:=G) d) (g : ℝ) : ℝ :=
  Real.exp (-1) * clockRegion d g (clockAt z g) t (J g) (expLinks G _ (g • u)) univ

def varyingCoefficient (Z : ChartRatio G) (z : ℕ → ℝ → ℝ) (t : d.Tags) (u : Pins G c)
    (W : SpaceF G d → ℝ) : ℕ → ℝ :=
  Therm.stamp (tangent G d.Links) (clockAmplitude d Z W ∘ recover u) (clockPhase d t u z) 1

theorem varying_expansion (h : d.Room G) {Z : ChartRatio G} (hZ : LocalRatio Z)
    (z : ℕ → ℝ → ℝ) (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0)
    (head : ∀ i ≤ d.depth, z i 0 = 1) (nonneg : ∀ i ≤ d.depth, ∀ g, 0 ≤ z i g)
    (t : d.Tags) (u : Pins G c) (J : PathSource (G:=G) d)
    (hJ : ∀ g > (0:ℝ), ∀ V, Measurable (J g V))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ g > (0:ℝ), ∀ V x, ‖J g V x‖ ≤ B)
    (W : SpaceF G d → ℝ) (hc : CommonGerm d J W) (hw : ContDiffAt ℝ ω W 0) :
    Aspiration (varyingReading d z t u J) (varyingCoefficient d Z z t u W) := by
  let V (g : ℝ) := expLinks G _ (g • u)
  let K := clockAmplitude d Z W ∘ recover u
  have hK : ContDiffAt ℝ ω K 0 :=
    ContDiffAt.comp (f:=recover u) 0 (by rw [map_zero]; exact clockAmplitude_hot d hZ hw)
      (recover (E:=Coordinates G d) u).contDiff.contDiffAt
  let φ := clockPhase d t u z
  have hf : ContDiffAt ℝ ω φ 0 := clockPhase_hot d t u (room_ok d h) hot
  have hs : Radial.Stationary φ := by
    apply FormalOPE.RG10.Inherit.stable hf
    · change clockPhase d t u z 0 = 0
      rw [clockPhase_exact]
      simp [thermal_zero d t (room_ok d h)]
    intro v
    rw [show φ v = _ from clockPhase_exact d t u z v]
    exact add_nonneg (sq_nonneg _) (account_nonnegative d (fun i hi => nonneg i hi _) t _ _)
  have gap := clockPhase_coercive d t u h hot head
  obtain ⟨δ,hδ,hδZ,inside⟩ := varying_inside d (room_ok d h) hZ z t u J hJ W hc
  have near : ∀ᶠ g : ℝ in Tested.germ, ∀ i ≤ d.depth, (2*g)⁻¹^2 ≤ clockAt z g i := by
    have loaded := eventually_all.mpr (fun i : Fin (d.depth+1) => ((hot i (Nat.le_of_lt_succ i.isLt)).continuousAt
      |>.tendsto |>.mono_left (show Tested.germ ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)).eventually
        (lt_mem_nhds (show (1:ℝ)/4 < z i 0 by rw [head i (Nat.le_of_lt_succ i.isLt)]; norm_num)))
    filter_upwards [eventually_pos,loaded] with g hg enough i hi
    have e : (1:ℝ)/4 < z i g := enough ⟨i,Nat.lt_succ_of_le hi⟩
    change (2*g)⁻¹^2 ≤ z i g / g^2
    apply (le_div_iff₀ (sq_pos_of_pos hg)).mpr
    convert e.le using 1
    field_simp
    norm_num
  intro k
  obtain ⟨η,hη,estimate⟩ := Therm.aspirates (tangent G d.Links) K φ k 1 hs hf hK gap
  let r := min η δ / 2
  have hr : 0 < r := half_pos (lt_min hη hδ)
  have hrη : r < η := (half_lt_self (lt_min hη hδ)).trans_le (min_le_left ..)
  have hrδ : r < δ := (half_lt_self (lt_min hη hδ)).trans_le (min_le_right ..)
  obtain ⟨ε,hε,tail⟩ := clock_exterior d h Z hZ hr (hrδ.le.trans hδZ) B hB
  obtain ⟨A,hA,tails⟩ := tail (k+1)
  obtain ⟨C,hC,prices⟩ := estimate r ⟨hr,hrη⟩
  refine ⟨C+Real.exp (-1)*A,add_nonneg hC (mul_nonneg (Real.exp_pos _).le hA),?_⟩
  filter_upwards [eventually_pos,near,inside r ⟨hr,hrδ⟩,prices,
    (moving_ray_quiet u hε).filter_mono nhdsWithin_le_nhds] with g hg high exactChart cost quiet
  let S := chamber G d.Links r
  let f (U : Set (Fields G d)) := clockRegion d g (clockAt z g) t (J g) (V g) U
  have split : f univ = f S + f Sᶜ := by
    unfold f clockRegion
    rw [setIntegral_univ,← mul_add,integral_add_compl
      (Chart.Ratio.chamber_open hZ (hrδ.le.trans hδZ)).measurableSet
      (pathAmplitude_integrable d (room_ok d h) (clockAt z g) t (J g) _ (hJ g hg _) (hb g hg _))]
  have integral : ‖f Sᶜ‖ ≤ A*g^(k+1) := tails g hg (clockAt z g) high (V g) quiet t (J g) (hb g hg _)
  change ‖Real.exp (-1)*f univ - peval (varyingCoefficient d Z z t u W) k g‖ ≤ _
  rw [split,mul_add,add_sub_right_comm]
  have cost' : ‖Real.exp (-1)*f S - peval (varyingCoefficient d Z z t u W) k g‖ ≤ C*g^(k+1) := by
    change ‖Real.exp (-1) * clockRegion d g (clockAt z g) t (J g) _ _ - _‖ ≤ _
    rw [exactChart]; exact cost
  have outside : ‖Real.exp (-1) * f Sᶜ‖ ≤ (Real.exp (-1)*A)*g^(k+1) := by
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_assoc]
    exact mul_le_mul_of_nonneg_left integral (Real.exp_pos _).le
  exact (norm_add_le ..).trans ((add_le_add cost' outside).trans_eq (add_mul ..).symm)

end YM.Integration.FVA1Physical.Wilson
