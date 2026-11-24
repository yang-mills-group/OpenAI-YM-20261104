import YM.Integration.FVA1Physical.Wilson.OrbitKernel

/-! The full signed physical reading from its exterior orbit marginal and the
new, normalized Wilson kernel. The physical interaction only enters outside. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}
variable (W : ForestCell Q R out)
local notation "O" => represent (tint G (Exterior.Body 1 c) W.x)
local notation "I" => board W.F W.X
local notation "Y" => youth W.F W.Y
local notation "A" => hotel W.F W.X W.Y W.J O W.center W.a W.b
local notation "F₀" => woolModel W.F W.X W.J R W.Y W.source O W.center W.a W.b
local notation "E" => expect Q R O
local notation "copy" => chambers W.F W.Y W.J O W.center

theorem exterior_orbit_price {σ C δ Λ w g r ε χ : ℝ}
    (adm : Admitted O R Q σ C δ Λ w) (pos : ∀ U,0<R.eval U) (branches : Q.patch.Branches Q.kernel G)
    (dec : WilsonStartup.Decent R.clip R.p) (beta : 0≤R.beta) (B : Positions (Primary f G)→ℝ)
    (bcont : Continuous B) (hg : 0<g) (hr : 0<r) (fit : W.Fits g r) (hε : 0≤ε)
    (rows : ∀ z u : Positions (Primary f G),
      (∀ t∈Set.Icc (0:ℝ) 1,z+t • u∈Metric.closedBall 0 r) →
      |(Real.log (R.eval (palace (g • (z+u)))) - B (z+u)) -
       (Real.log (R.eval (palace (g • z)))-B z)|≤(∑ j,|u j|)*(ε/r))
    (tact : Tonic.Loan.Tact W.F W.X A F₀ Y R O 1 χ) (rare : chance Q R O Aᶜ ≤ χ)
    (φ : Config G f→ℝ) (loc : GaugeLocal Q Y φ) (bound : ∀ U,|φ U| ≤ 1) :
    let P := interiorEnergy Q O W.source copy R.beta g B
    |E (orbitKernel W.F I A P φ)-E φ| ≤ χ + (Real.exp (2*(motionCost G W.X r*(ε/r)))-1) + 4*χ := by
  intro P
  let Kf := orbitKernel W.F I A P φ
  let Lf := angularLaw W.F I A P φ
  let Tf := Rota.resample W.F I F₀ A φ
  have rot := Posture.harvest W.grant W.voice W.posture adm.lawful branches dec beta W.radius_le W.garden
  have model := Posture.buy W.source W.grant W.voice W.posture adm.lawful branches dec beta
  have eP : Envelope P := interiorEnergy_envelope W adm.lawful model.currency B bcont
  have ha : MeasurableSet A := rot.reforms.from_here
  obtain ⟨env,cal⟩ := signed_tact adm rot tact loc bound
  have cap := orbitKernel_envelope W.F I A P φ ha eP loc.currency.meas zero_le_one bound
  have cut := expect_on_chart O ha adm Kf cap.1 zero_le_one cap.2 rare
  change |E Kf-E (Set.indicator A (orbitKernel W.F I A P φ))| ≤ 1*χ at cut
  rw [←regular_kernel_indicator W P φ eP,one_mul] at cut
  have ml : Measurable Lf := angular_law_meas W.F I A P φ ha eP.meas loc.currency.meas
  have mid : |E Lf-E Tf| ≤ Real.exp (2*(motionCost G W.X r*(ε/r)))-1 :=
    expect_difference adm ml env (fun U=>(abs_sub_comm _ _).trans_le
      ((interior_orbit_price W adm.lawful branches dec beta pos hg hr hε fit B bcont rows φ loc.currency.meas zero_le_one bound U).trans_eq (mul_one _)))
  calc |E Kf-E φ| ≤ |E Kf-E Tf|+|E Tf-E φ| := abs_sub_le _ _ _
       _ ≤ (|E Kf-E Lf|+|E Lf-E Tf|)+4*χ := add_le_add (abs_sub_le _ _ _) cal
       _ ≤ _ := add_le_add (add_le_add cut mid) le_rfl
end YM.Integration.FVA1Physical.Wilson
