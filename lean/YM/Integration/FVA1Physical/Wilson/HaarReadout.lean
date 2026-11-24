import YM.Integration.FVA1Physical.Wilson.PureForest
import YM.Integration.FVA1Physical.Wilson.PostureMass
import YM.Integration.FVA1Physical.Wilson.ForestAverage

/-! The unrestricted normalized local reading against a single independent Wilson
bank, averaged over the physical forest conditional. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}
variable (W : ForestCell Q R out)
local notation "O" => represent (tint G (Exterior.Body 1 c) W.x)
local notation "I" => board W.F W.X
local notation "Y" => youth W.F W.Y
local notation "A" => hotel W.F W.X W.Y W.J O W.center W.a W.b
local notation "F₀" => woolModel W.F W.X W.J R W.Y W.source O W.center W.a W.b
local notation "κ" => twirl W.F I
local notation "copy" => chambers W.F W.Y W.J O W.center

theorem forest_haar_price {σ C δ Λ w τ Δ g flurry ε fee b χ : ℝ}
    (adm : Admitted O R Q σ C δ Λ w) (pos : ∀ U,0<R.eval U) (branches : Q.patch.Branches Q.kernel G)
    (dec : WilsonStartup.Decent R.clip R.p) (beta : 0≤R.beta) (arsenal : MergeProof.Menu.Arsenal R)
    (psalm : Psalm Q R τ Δ) (threshold : W.threshold≤τ) (paid : 0≤Δ) (B : Positions (Primary f G)→ℝ)
    (bcont : Continuous B) (hg : 0<g) (hw : 0<flurry) (fit : W.Fits g flurry) (hε : 0≤ε) (hfee : 0≤fee)
    (cost : silkRoad C σ δ Λ R.beta W.X.card W.M R.p W.d≤fee)
    (small : motionCost G W.X flurry*(ε/flurry)+fee≤1)
    (rows : ∀ z u : Positions (Primary f G),
      (∀ t∈Set.Icc (0:ℝ) 1,z+t • u∈Metric.closedBall 0 flurry) →
      |(Real.log (R.eval (palace (g • (z+u)))) - B (z+u)) -
       (Real.log (R.eval (palace (g • z)))-B z)|≤(∑ j,|u j|)*(ε/flurry))
    (tact : Tonic.Loan.Tact W.F W.X A F₀ Y R O b χ) (φ : Config G f→ℝ)
    (localφ : GaugeLocal Q Y φ) (φ₀ : 0≤φ) (φb : ∀ U,φ U ≤ b) :
    let ζ := Real.exp (Posture.wSize G R.p σ C δ Λ R.beta W.M W.Y.card W.X.card W.P W.bound W.b)/Posture.moss G W.radius (board W.F W.X).card
    let charge := Δ*(R.p.mass Y (ζ*b*2)*Real.exp ((youth W.F W.Y).card*w))
    let τ₀ := fun U=> B (chartLog g (copy U))
    let Z := Q.push R.beta R.eval O
    |(∫ θ : IV W.F I G,Q.push R.beta (fun U=> Rota.ghat F₀ θ φ A U *
      (R.eval (κ θ U)*Real.exp (τ₀ U-τ₀ (κ θ U)))) O/Z ∂fence W.F I G)-
      expect Q R O φ| ≤ charge+2*(motionCost G W.X flurry*(ε/flurry)+fee)*(b+χ+charge)+χ := by
  intro ζ charge τ₀ Z
  have hH : 0 ≤ motionCost G W.X flurry := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hw.le)
  have hmix := mul_nonneg zero_le_two (add_nonneg (mul_nonneg hH (div_nonneg hε hw.le)) hfee)
  have bought := Posture.harvest W.grant W.voice W.posture adm.lawful branches dec beta W.radius_le W.garden
  have mc := (informed W.F W.X W.Y W.J O W.center W.voice W.posture.extendsX).1
  have mτ : Measurable τ₀ := bcont.measurable.comp ((chartLog_meas g).comp mc)
  apply forest_average adm bought tact τ₀ mτ φ localφ φ₀ φb hmix
  intro θ
  have raw := posture_relative_readout W.F W.X W.Y W.J W.P W.x W.center W.voice W.posture W.source W.grant adm
    pos branches dec beta W.radius_le W.garden arsenal psalm threshold paid B bcont hg.ne' hw hε hH hfee cost
    small rows θ φ localφ φ₀ φb
  have eq := W.wilson_on_test B hg hw.le fit θ φ
  dsimp only at eq raw ⊢
  rw [eq] at raw
  unfold compass MSbar.Bulk.expect
  rw [←sub_div]
  exact raw
end YM.Integration.FVA1Physical.Wilson
