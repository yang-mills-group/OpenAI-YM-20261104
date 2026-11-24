import YM.Integration.FVA1Physical.Wilson.RecalibratedLimit
import YM.Integration.FVA1Physical.Wilson.SceneClockGerm

/-! The Gaussian Schur complement of the independently iterated FVA2 action
is the leading kinetic quadratic of the very same recalibrated physical scene,
at each retained level, all coarse fields and every finite period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Function RG Lattice YM.Wilson Exterior Tree Precision RGComparison.Core16
open FVA2.CityHistory PertExtension.Chart PertExtension.Series.Tested
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Cacao Comparison.RG02 Push Push.Uniform
open scoped Classical Topology
variable {G : Gauge} {L : Levels G} {H : Horizon L} {Z : ChartRatio G}
    {K : Kin H Z} {N p k r m : ℕ} {e : G.Color} (S : Scene L p r)
    (hS : Realized K N p k r e S) (T : Slices L p) (hm : m ≤ N) (hk : k ≤ m)
    (h : (traversal T hm).Room G) (t : (traversal T hm).Tags) (hZ : LocalRatio Z)
    (u : Pins G (L.S.side m p))
include hS hk hZ

theorem calibrated_vacuum_limit :
    Tendsto (fun g : ℝ => S.film m g (expLinks G _ (g • u))) PertExtension.Series.Tested.germ
      (𝓝 (rayGaussian (traversal T hm) t h u)) := by
  have slope : ∀ i ≤ (traversal T hm).depth, Tendsto (fun g : ℝ => g^2 * sceneTemperatures S m g i)
      PertExtension.Series.Tested.germ (𝓝 1) := by
    intro i hi
    rw [traversal_depth] at hi
    exact scene_temperature_leading S hS i m hk (by omega)
  exact (changing_centered (traversal T hm) Z t h hZ u (sceneTemperatures S m) slope).congr'
    (Eventually.of_forall fun g => (congrFun (scene_descent S hS T hm hk g) _).symm)

theorem purchase_kinetic_identification :
    let c := L.S.side m p
    let x := (tint G (Body 1 c)).symm (axesP G c u)
    (retained (traversal T hm) t h).flourish u / 2 = height c (L.params m).clip (K.path N m) x := by
  intro c x
  let B := height c (L.params m).clip (K.path N m) x
  let A := picture x (S.Poly m)
  let F g := Real.log (S.film m g (postcard G c g x))+B
  have fit := (hS.budget m hm hk).1
  have hx : ∀ᶠ g in PertExtension.Series.Tested.germ, yard 1 g x :=
    (awake.eventually_ge_atTop ‖x‖).mono fun _ h => by simpa [yard] using h
  have approx : Wave.Approx F A r :=
    Rolling.Price.inherits (V:=fun _ (_:Unit) => True) (fit.tune 1)
      (fun _ _ => x) (hx.mono fun _ hc _ _ => hc)
  have head : PowerSeries.coeff 0 A = 0 := by
    unfold A picture
    rw [PowerSeries.coeff_map,fit.bond,map_zero]
  have zero : Tendsto F PertExtension.Series.Tested.germ (𝓝 0) := Metric.tendsto_nhds.mpr fun ε he =>
    (Wave.Approx.tends approx ε he).mono fun g hg => by simpa [head,Real.dist_eq] using hg
  have eq (g : ℝ) : postcard G c g x = expLinks G _ (g • u) := by
    rw [postcard,map_smul]
    change represent (g • (tint G _) ((tint G _).symm (axesP G c u))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,← (axesP G c).map_smul,direct_link]
  have bound := calibrated_vacuum_limit S hS T hm hk h t hZ u
  have physical := ((Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp bound).add_const B
  have same : Tendsto F PertExtension.Series.Tested.germ (𝓝 (Real.log (rayGaussian (traversal T hm) t h u)+B)) :=
    physical.congr' (Eventually.of_forall fun g => by dsimp only [F,Function.comp_apply]; rw [eq])
  have cmp := tendsto_nhds_unique same zero
  rw [rayGaussian,Real.log_exp] at cmp
  linarith

end YM.Integration.FVA1Physical.Wilson
