import YM.Integration.WilsonOlderFreshPointHistory

/-! A fixed tolerance and fixed native ranks cost an arbitrary small
power of the dated inverse coupling on the same point school. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointIncome
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)






open Asymptotics
private theorem restoration (K:ℝ)(k₀:1≤K){δ:ℝ}(positive:0<δ):
    ∀ᶠx:ℝ in atTop,∀z:ℝ,0≤z→Real.sqrt (Real.log x)*(1+K*(x^(δ/2)*z))≤x^δ*(1+z):=by
  have kp:0<K:=zero_lt_one.trans_le k₀
  have small:=(isLittleO_log_rpow_atTop (half_pos positive)).bound (inv_pos.mpr kp)
  filter_upwards [small,(tendsto_atTop.mp Real.tendsto_log_atTop 1),eventually_ge_atTop 1] with x bill logs x1
  have l₀:0≤Real.log x:=zero_le_one.trans logs
  have x₀:0<x:=zero_lt_one.trans_le x1
  let t:=x^(δ/2)
  have t₀:1≤t:=Real.one_le_rpow x1 (half_pos positive).le
  have sq:t*t=x^δ:=by unfold t;rw [←Real.rpow_add x₀];congr 1;ring
  have logfee:Real.log x≤K⁻¹*t:=by
    simpa only [Real.norm_eq_abs,abs_of_nonneg l₀,abs_of_nonneg (Real.rpow_nonneg x₀.le _)] using bill
  have used:Real.sqrt (Real.log x)*K≤t:=calc
    _ ≤ Real.log x*K:=mul_le_mul_of_nonneg_right (by
      have sqL:=Real.sq_sqrt l₀
      have gz:=Real.sqrt_nonneg (Real.log x)
      nlinarith) kp.le
    _ ≤ (K⁻¹*t)*K:=mul_le_mul_of_nonneg_right logfee kp.le
    _ = t:=by field_simp
  have enough:1≤K*t:=one_le_mul_of_one_le_of_one_le k₀ t₀
  intro z z0
  calc
    _ ≤ Real.sqrt (Real.log x)*(K*t*(1+z)):=mul_le_mul_of_nonneg_left (by nlinarith) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Real.log x)*K)*(t*(1+z)):=by ring
    _ ≤ t*(t*(1+z)):=mul_le_mul_of_nonneg_right used (mul_nonneg (zero_le_one.trans t₀) (by linarith))
    _ = _:=by rw [←mul_assoc,sq]

include simple in
theorem original {φ U:ℕ→ℕ}(I:Unit→Loan)(Q:ℕ)(level:(I ()).toll=d)(d0:0<d)
    (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ
       (WilsonOlderFreshGraphMatrixPrice.menu G I d Q level) simple (WilsonOlderFreshGraphMatrixPrice.jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (Lambda R.family.path.levels j))
    (o:Loc G 1)(old:WilsonPointChildWidthHistory.Income R L a depth o Q){δ:ℝ}(accuracy:0<δ):
    let M:=WilsonOlderFreshGraphMatrixPrice.menu G I d Q level
    let H:=roots M simple R.metals.p R.metals.K
    (∃books,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) books) ∧
    ∀ᶠj:ℕ in atTop,∀k:ℕ,k ≤ R.alloy.B.a.clock.J j→1 ≤ Burn.horizon k→
      d≤R.family.path.levels.clock.J (j+1)→
      let σ:=Agenda.seed H φ (Burn.horizon k) (R.family.path.levels.clock.J j)
      let β:=R.alloy.B.a.clock.hatBeta j
      ∀(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R j D),
        ∃T:WilsonOlderFreshGraphSlate.Copy G d Q σ,
          (∑r,T.fare r)≤β^δ*(1+‖p.2‖) ∧
          WilsonOlderFreshPointCommission.Published R L a depth j b p T:=by
  intro M H
  obtain ⟨past,buy⟩:=WilsonOlderFreshPointHistory.original R L a depth simple I Q level d0 law purchase
    slow o old (half_pos accuracy)
  have grow:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have one:(1:ℝ)≤(d+Q+1:ℕ):=by exact_mod_cast (show 1≤d+Q+1 by omega)
  refine ⟨past,?_⟩
  filter_upwards [buy,grow.eventually (restoration (d+Q+1:ℕ) one accuracy)] with j poster estimate
  intro k kr kp front σ β b p
  obtain ⟨T,fee,opened⟩:=poster k kr kp front b p
  exact ⟨T,fee.trans (estimate ‖p.2‖ (norm_nonneg _)),opened⟩

end YM.Integration.WilsonOlderFreshPointIncome
end
