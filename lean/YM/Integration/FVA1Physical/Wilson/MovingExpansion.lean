import YM.Integration.FVA1Physical.Wilson.MovingInterior

/-! Fixed-period, all-order physical expansion on every retained gauge
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

def rayReading (a : ℕ → ℝ) (t : d.Tags) (u : Pins G c)
    (J : PathSource (G:=G) d) (g : ℝ) : ℝ :=
  Real.exp (-1) * pathRegion d g a t (J g) (expLinks G _ (g • u)) univ

def rayCoefficient (Z : ChartRatio G) (a : ℕ → ℝ) (t : d.Tags) (u : Pins G c)
    (W : SpaceF G d → ℝ) : ℕ → ℝ :=
  Therm.stamp (tangent G d.Links) (chartAmplitude d Z a t W ∘ recover u) (rayPhase d t u) 1

theorem path_expansion (h : d.Room G) {Z : ChartRatio G} (hZ : LocalRatio Z)
    (a : ℕ → ℝ) (t : d.Tags) (u : Pins G c) (J : PathSource (G:=G) d)
    (hJ : ∀ g > (0:ℝ), ∀ V, Measurable (J g V))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ g > (0:ℝ), ∀ V x, ‖J g V x‖ ≤ B)
    (W : SpaceF G d → ℝ) (hc : CommonGerm d J W) (hw : ContDiffAt ℝ ω W 0) :
    Aspiration (rayReading d a t u J) (rayCoefficient d Z a t u W) := by
  let V (g : ℝ) := expLinks G _ (g • u)
  let K := chartAmplitude d Z a t W ∘ recover u
  have hK : ContDiffAt ℝ ω K 0 :=
    ContDiffAt.comp (f:=recover u) 0 (by rw [map_zero]; exact chartAmplitude_analytic d hZ (room_ok d h) a t hw)
      (recover (E:=Coordinates G d) u).contDiff.contDiffAt
  let φ := rayPhase d t u
  have hf : ContDiffAt ℝ ω φ 0 := charge_hot 1 u (thermal d t (room_ok d h) 1)
  have hs := rayPhase_stationary d t u (room_ok d h)
  have gap := rayPhase_coercive d t u h
  obtain ⟨δ,hδ,hδZ,inside⟩ := path_inside d (room_ok d h) hZ a t u J hJ W hc
  let M := ∑ i ∈ Finset.range (d.depth+1), ‖a i‖
  have ha : d.Band M a := fun i hi => Finset.single_le_sum (fun j _ => norm_nonneg (a j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  intro k
  obtain ⟨η,hη,estimate⟩ := Therm.aspirates (tangent G d.Links) K φ k 1 hs hf hK gap
  let r := min η δ / 2
  have hr : 0 < r := half_pos (lt_min hη hδ)
  have hrη : r < η := (half_lt_self (lt_min hη hδ)).trans_le (min_le_left ..)
  have hrδ : r < δ := (half_lt_self (lt_min hη hδ)).trans_le (min_le_right ..)
  obtain ⟨ε,hε,tail⟩ := path_exterior d h Z hZ hr (hrδ.le.trans hδZ) M B hB
  obtain ⟨A,hA,tails⟩ := tail (k+1)
  obtain ⟨C,hC,prices⟩ := estimate r ⟨hr,hrη⟩
  refine ⟨C+Real.exp (-1)*A,add_nonneg hC (mul_nonneg (Real.exp_pos _).le hA),?_⟩
  filter_upwards [eventually_pos,inside r ⟨hr,hrδ⟩,prices,
    (moving_ray_quiet u hε).filter_mono nhdsWithin_le_nhds] with g hg exactChart cost quiet
  let S := chamber G d.Links r
  let f (U : Set (Fields G d)) := pathRegion d g a t (J g) (V g) U
  have split : f univ = f S + f Sᶜ := by
    unfold f pathRegion
    rw [setIntegral_univ,← mul_add,integral_add_compl
      (Chart.Ratio.chamber_open hZ (hrδ.le.trans hδZ)).measurableSet
      (pathAmplitude_integrable d (room_ok d h) (offset a g) t (J g) _ (hJ g hg _) (hb g hg _))]
  have integral : ‖f Sᶜ‖ ≤ A*g^(k+1) := tails g hg a ha (V g) quiet t (J g) (hb g hg _)
  change ‖Real.exp (-1)*f univ - peval (rayCoefficient d Z a t u W) k g‖ ≤ _
  rw [split,mul_add,add_sub_right_comm]
  have cost' : ‖Real.exp (-1)*f S - peval (rayCoefficient d Z a t u W) k g‖ ≤ C*g^(k+1) := by
    change ‖Real.exp (-1) * pathRegion d g a t (J g) _ _ - _‖ ≤ _
    rw [exactChart]; exact cost
  have outside : ‖Real.exp (-1) * f Sᶜ‖ ≤ (Real.exp (-1)*A)*g^(k+1) := by
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_assoc]
    exact mul_le_mul_of_nonneg_left integral (Real.exp_pos _).le
  exact (norm_add_le ..).trans ((add_le_add cost' outside).trans_eq (add_mul ..).symm)

end YM.Integration.FVA1Physical.Wilson
