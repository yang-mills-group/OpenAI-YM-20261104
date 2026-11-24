import YM.Integration.FVA1Physical.Wilson.SceneWilsonClock
import YM.Integration.FVA1Physical.Wilson.SceneKinetic
import YM.Integration.FVA1Physical.Wilson.VaryingNormalized

/-! At every inherited depth the realized physical scene has the same
vacuum coefficients as the independently iterated FVA2 ledger at its
actual clock series. The comparison includes the nonflat retained ray
and the unperturbed vacuum normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function Finset RG Lattice YM.Wilson Exterior Tree Precision RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Cacao Comparison.RG02 Push Push.Uniform
open scoped Classical Topology ContDiff
variable {G : Gauge} {L : Levels G} {H : Horizon L} {Z : ChartRatio G}
    {K : Kin H Z} {N p k r m : ℕ} {e : G.Color} (S : Scene L p r)
    (hS : Realized K N p k r e S) (T : Slices L p) (hm : m ≤ N) (lo : k ≤ m)
    (h : (traversal T hm).Room G) (t : (traversal T hm).Tags) (hZ : LocalRatio Z)
    (u : Pins G (L.S.side m p))
set_option quotPrecheck false
local notation "d₁" => traversal T hm
local notation "w" => formalSceneClock S N m
local notation "z₁" => relativeSceneClock S m
local notation "V₀" => variedVacuum d₁ Z t h w u
local notation "E₀" => rayGaussian d₁ t h u

include hS lo in
theorem priced_clock : AnalyticClocks d₁ z₁ w where
  hot i hi := scene_clock_hot S hS m i lo (by rw [traversal_depth] at hi; omega)
  head i hi := by simp only [relativeSceneClock,(scene_product_germ S hS i m lo
    (by rw [traversal_depth] at hi; omega)).1,one_pow]
  nonneg i _ g := sq_nonneg (resetProduct S i m g)
  expansion i hi := formalScene_rates S hS m i lo (by rw [traversal_depth] at hi; omega)
  sound := formalScene_sound S hS m lo

include hS lo hZ in
theorem film_ledger :
    Aspiration (fun g : ℝ => S.film m g (expLinks G _ (g • u))) (term V₀) := by
  have rate := varying_vacuum_ray d₁ Z hZ t h z₁ w (priced_clock S hS T hm lo) u
  have same (g : ℝ) : sceneTemperatures S m g = clockAt z₁ g := funext (clock_measures S m g)
  have eqn (g : ℝ) := congrFun (scene_descent S hS T hm lo g) (expLinks G _ (g • u))
  simp_rw [same] at eqn
  simp_rw [eqn]
  exact rate

private theorem log_price {A : PowerSeries ℝ} {F : ℝ → ℝ} (price : Aspiration F (term A))
    (positive : 0 < PowerSeries.coeff 0 A) (r : ℕ) :
    let P := peval (term A) r
    Wave.Grade (fun g => Real.log (F g) - ∑ i ∈ range (r+1),g^i * Wave.bill (Real.log ∘ P) i) (r+1) := by
  intro P
  let b := PowerSeries.coeff 0 A/2
  have hb : 0<b := half_pos positive
  have small : b < term A 0 := half_lt_self positive
  have h0 : P 0 = term A 0 := by simp [P,Zone.eval,Finset.sum_range_succ']
  have smooth : ContDiff ℝ ω P := by unfold P peval Zone.eval; fun_prop
  have ht : Tendsto P Tested.germ (𝓝 (term A 0)) :=
    h0 ▸ (smooth.continuous.continuousAt.mono_left nhdsWithin_le_nhds)
  have jet := Wave.certified ((Real.contDiffAt_log.mpr (h0.trans_ne positive.ne')).comp 0 smooth.contDiffAt) r
  obtain ⟨C,hC,bill⟩ := price r
  have e : Wave.Grade (fun g => Real.log (F g) - Real.log (P g)) (r+1) := by
    apply Price.fixed 0 (C/b)
    filter_upwards [bill,price.tendsto_first.eventually (lt_mem_nhds small),ht.eventually (lt_mem_nhds small)]
      with g error p q _ _
    change ‖F g-P g‖ ≤ C*g^(r+1) at error
    rw [Real.norm_eq_abs] at error ⊢
    rw [pow_zero,mul_one]
    apply le_of_mul_le_mul_left (a:=b) _ hb
    exact ((Order.log_contrast (hb.trans p) (hb.trans q) p.le q.le).trans error).trans_eq (by field_simp)
  apply (e.nsum jet).egress
  filter_upwards with g _ _
  simp only [Function.comp_def]
  ring

include hS lo hZ in
theorem scene_ledger_coefficients {i : ℕ} (hi : i ≤ r) :
    let c := L.S.side m p
    let x := (tint G (Body 1 c)).symm (axesP G c u)
    Lis.atlas (S.Poly m) r i (K.path N m) (L.params m).clip x =
      Wave.bill (Real.log ∘ peval (term V₀) r) i := by
  intro c x
  let B := height c (L.params m).clip (K.path N m) x
  let P i := Lis.atlas (S.Poly m) r i (K.path N m) (L.params m).clip x
  let K' i := Wave.bill (Real.log ∘ peval (term V₀) r) i
  have hx : ∀ᶠ g in Tested.germ, yard 1 g x :=
    (awake.eventually_ge_atTop ‖x‖).mono fun _ H => by simpa [yard] using H
  have fit := (hS.budget m hm lo).1
  have estimate : Wave.Grade (fun g => Real.log (S.film m g (postcard G c g x)) -
      ∑ j ∈ range (r+1),g^j * P j) (r+1) := by
    apply (Rolling.Price.inherits (V:=fun _ (_:Unit) => True) (fit.tune 1)
      (fun _ _ => x) (hx.mono fun _ H _ _ => H)).egress
    filter_upwards with g _ _
    have eqn := Wave.tariff_data r (L.params m).clip (K.path N m) (S.Poly m) fit x r g
    unfold taste picture at eqn
    simp only [PowerSeries.coeff_map] at eqn
    unfold P taste picture Lis.atlas Wave.joy
    simp only [PowerSeries.coeff_map]
    linarith only [eqn]
  have postcard_eq (g : ℝ) : postcard G c g x = expLinks G _ (g • u) := by
    rw [postcard,map_smul]
    change represent (g • (tint G _) ((tint G _).symm (axesP G c u))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,← (axesP G c).map_smul,direct_link]
  simp_rw [postcard_eq] at estimate
  have positive : 0 < PowerSeries.coeff 0 V₀ := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,varied_head d₁ Z hZ t h w u]
    exact Real.exp_pos _
  have transfer := log_price (film_ledger S hS T hm lo h t hZ u) positive r
  apply sub_eq_zero.mp
  apply Wave.magnitude (f:=fun j => P j-K' j) (n:=r) _ i hi
  apply (transfer.cut estimate).egress
  filter_upwards with g _ _
  simp only [mul_sub,sum_sub_distrib,K']
  ring

end YM.Integration.FVA1Physical.Wilson
