import YM.Integration.FVA1Physical.Wilson.MotionBank
import YM.MSbar.Cottage.Suns

/-! Actual high-probability forest recenterings: apply the signed exact-cover
credit and the independent Wilson chart together at one retained scale. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f}
variable (F : Forest S.ratio) (X Y : Support f) (J : Voice G) (P : Palisade)
variable (x : Positions (Primary c G)) (μ : Positions (Key F G))
local notation "V" => represent (tint G (Exterior.Body 1 c) x)
local notation "ω" => board F X
variable {a b v K σ C δ Λ w τ Δ rad flurry g H ε fee bnd : ℝ} {M d order : ℕ}
variable (voice : Clear G J) (post : Posture P J F a b v K M d X Y x μ R.p)
local notation "χ" => chambers F Y J V μ
local notation "I" => hotel F X Y J V μ a b

include voice post
/-- The true local twirl uses its full normalized conditional weight calculated
by `woolModel`. Both measured configurations have explicit clean chart copies
by `Posture.pose`; the gas is summed with `Psalm` at the actual outer field. -/
theorem posture_wilson_readout (i : S.Choices) (given : Grants i R F P order)
    (adm : Admitted V R S σ C δ Λ w) (positive : ∀ U,0<R.eval U)
    (branches : S.patch.Branches S.kernel G) (dec : WilsonStartup.Decent R.clip R.p)
    (beta : 0≤R.beta) (radius : rad ≤ 1) (garden : Posture.gardenCity P J K rad b)
    (arsenal : MergeProof.Menu.Arsenal R) (psalm : Psalm S R τ Δ) (threshold : v≤τ) (paid : 0≤Δ)
    (B : Positions (Primary f G)→ℝ) (bcont : Continuous B) (hg : g≠0) (hw : 0<flurry)
    (hε : 0≤ε) (hH : 0≤H) (hfee : 0≤fee)
    (cost : silkRoad C σ δ Λ R.beta X.card M R.p d≤fee) (small : H*(ε/flurry)+fee≤1)
    (rows : ∀ z u : Positions (Primary f G),
      (∀ t∈Set.Icc (0:ℝ) 1,z+t • u∈Metric.closedBall 0 flurry) →
      |(Real.log (R.eval (palace (g • (z+u)))) - B (z+u)) -
       (Real.log (R.eval (palace (g • z)))-B z)|≤(∑ j,|u j|)*(ε/flurry))
    (t : IV F ω G) (φ : Config G f→ℝ) (localφ : GaugeLocal S (youth F Y) φ)
    (φ₀ : 0≤φ) (φB : ∀ U, φ U≤bnd) :
    let κ := twirl F ω t
    let r := woolModel F X J R Y i V μ a b
    let q := Rota.ghat r t φ I
    let Z := S.push R.beta R.eval V
    let A := Real.exp (Posture.wSize G R.p σ C δ Λ R.beta M Y.card X.card P K b)/Posture.moss G rad (board F X).card*bnd
    let charge := Δ*(R.p.mass (youth F Y) (A*2)*Real.exp ((youth F Y).card*w))
    let bank := moveBank R χ κ B g flurry H
    |(S.push R.beta (fun U=>q U*(R.eval (κ U)*Real.exp (bank U))) V -
      S.push R.beta (fun U=>q U*R.eval U) V)/Z|≤charge + 2*(H*(ε/flurry)+fee)*(A+charge) := by
  intro κ r q Z A charge bank
  have bought := Posture.harvest given voice post adm.lawful branches dec beta radius garden
  have tr := Rota.existent bought t φ localφ bnd φ₀ φB
  have positiveQ := Rota.positive bought t φ bnd φ₀ φB
  have hm := (informed F X Y J V μ voice post.extendsX).1
  apply tracked_wilson_price V adm tr positiveQ arsenal psalm paid (voids post.folds threshold) bank
    (moveBank_meas R adm.lawful χ κ hm tr.live B bcont g flurry H)
    (add_nonneg (mul_nonneg hH (div_nonneg hε hw.le)) hfee) small
  intro U live
  have inside : U∈I := by
    by_contra absent; apply live
    change spec I U * (r (κ U)*φ (κ U))=0
    rw [show spec I U=0 from Set.indicator_of_notMem absent _,zero_mul]
  have rotated : κ U∈I := by
    by_contra absent; apply live
    change spec I U * (r (κ U)*φ (κ U))=0
    rw [show r (κ U)=0 from bought.ext _ absent,zero_mul,mul_zero]
  have geom := Posture.planT voice post t inside rotated
  have fixed := (Posture.pose voice post inside).2.2.2.1
  have twisted := (Posture.pose voice post rotated).2.2.2.1
  exact moveBank_price R adm.lawful positive hg hw hε hH hfee χ κ (Heath.canoe F) B post.bank post.stone
    dec beta cost rows (fun U=>Further.DenseMixedKernels.Throng.phase adm.lawful (F.foldAt U) U)
    geom.1 geom.2 fixed twisted

end YM.Integration.FVA1Physical.Wilson
