import YM.Integration.WilsonVacuumPreResetDepositedRay

/-! Read the original two-variable Wilson group action at its authentic
translated fine field. The label table remains in the actual grant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedGeometric
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 Cumulants FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo
open WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam Marker Multi Stationary WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open AllOrder AllOrder.Floe
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetTorusDeposit
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)

include hm tag in
private theorem projection :
    saddle R N m p F = reveal G (step R m p) F *
      ((reveal G (step R m p) F).transpose * saddle R N m p F):=by
  have h:=(model R N m p hm).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N m p hm F tag] at h
  apply sweeps G (step R m p) F (prediction R N m p) (lower R N m)
    (isUnit_iff_ne_zero.mpr h.det_pos.ne')
  exact horizon_step (levels R) m N hm _ _ (step R m p).sizes

variable (Z:SeriesA G){T:Type}[DecidableEq T]{J:Census T}
    (Q:Bulk.Colors J G (fine R m p))(cash:BudgetPoint)(cap:ℕ){σ C:ℝ}
    (width:0<σ)(draw:Draw Z σ C)(low:∀ a∈Z,3 ≤ a.grade)(high:∀ a∈Z,a.grade ≤ cap)
    (x:fieldDir G (coarse R m p) 1)(z:Key F G→ℝ)

abbrev source := QuadraticLocal.Fk.grant (bank Z) (Step.tape cap) Q
abbrev profile := PhysicalForestRay.sample (step R m p) F x z

include cash width draw low high in
theorem germ :
    PhysicalForestRay.chartAction (step R m p) F (saddle R N m p F) (model R N m p hm)
      x z tag (source R m p Z Q cap) =ᶠ[𝓝 0]
    fun g:ℝ=>raw R N m p hm F Z (profile R m p F x z) g-
      g^2*jac R N m p hm F (g • profile R m p F x z):=by
  let v:=profile R m p F x z
  have h:=shape_area (step R m p) F (saddle R N m p F) (center R N m p hm F)
    (ratio R) (center R N m p hm F).contDiff.contDiffAt (map_zero _)
    R.alloy.B.ratio (projection R N m p hm F tag)
  have path:Tendsto (fun g:ℝ=>g • v) (𝓝 0) (𝓝 0):=by
    simpa using (show ContinuousAt (fun g:ℝ=>g • v) 0 by fun_prop).tendsto
  filter_upwards [path.eventually h] with g area
  let d:=(edgeM (shift R N m p hm F) (g • v)).det
  let a:=unhaar (ratio R) (slice R N m p F *ᵥ spider (shift R N m p hm F) (g • v))
  change d*Real.exp a=Real.exp (jac R N m p hm F (g • v)) at area
  have hd:d≠0:=by
    intro bad
    rw [bad,zero_mul] at area
    exact (Real.exp_pos _).ne' area.symm
  have logs:=congrArg Real.log area
  rw [Real.log_mul hd (Real.exp_pos _).ne',Real.log_exp,Real.log_exp] at logs
  dsimp only [PhysicalForestRay.chartAction,WilsonVacuumPreResetDepositedRay.raw,source]
  let w:=spider (shift R N m p hm F) (g • v)
  have absolute:=WilsonVacuumPreResetTorusDepositedGrant.absolute (step R m p) F
    (saddle R N m p F) (ratio R) (income R N m p).clip (income R N m p).path Q cash Z
    width draw low high g w
  calc
    _ = (FundedInteractingPeriod.potential (income R N m p).clip (income R N m p).path Z g
        (PhysicalForestAction.field (step R m p) F (saddle R N m p F) w)+
        jointPen G (step R m p) (pan R N m p F *ᵥ w)-g^2*a)-g^2*Real.log d :=
      congrArg (fun t:ℝ=>t-g^2*Real.log d) absolute
    _ = _ := by
      let cost:=FundedInteractingPeriod.potential (income R N m p).clip (income R N m p).path Z g
        (PhysicalForestAction.field (step R m p) F (saddle R N m p F) w)+
        jointPen G (step R m p) (pan R N m p F *ᵥ w)
      change cost-g^2*a-g^2*Real.log d = cost-g^2*jac R N m p hm F (g • v)
      rw [←logs]
      ring

include cash width draw low high in
theorem original (well:Bulk.Well (source R m p Z Q cap))(k:ℕ):
    let v:=profile R m p F x z
    let series:=X^2*retool (shift R N m p hm F)
        (unscaled (step R m p) F (prediction R N m p) (filed R N m p Z)) -
      X^2*relativeHaar R N m p hm F
    Assembly.jet (Bulk.geometric (model R N m p hm) F tag (source R m p Z Q cap)) k
      (Bulk.translated (model R N m p hm) F x z) =
      MvPolynomial.eval v (coeff k series):=by
  intro v series
  let a:=raw R N m p hm F Z v
  let j:=jac R N m p hm F
  have ha:=unscaled_read R N m p hm F Z v width draw
  have hj:Green j:=stamp_d (step R m p) F (center R N m p hm F) (ratio R)
    R.alloy.B.ratio (center R N m p hm F).contDiff.contDiffAt (map_zero _)
  have smooth:ContDiffAt ℝ ω (fun g:ℝ=>j (g • v)) 0:=
    ContDiffAt.comp (g:=j) (f:=fun g:ℝ=>g • v) 0 (by simpa only [zero_smul] using hj) (by fun_prop)
  have jt:ForestRaySeries.Reads v (jet j) (fun g:ℝ=>j (g • v)):=by
    exact ⟨smooth,
      OriginalRadialSeries.restriction v _ hj⟩
  have hb:=ForestRaySeries.mul (ForestRaySeries.powers v 2) jt
  let b:=fun g:ℝ=>g^2*j (g • v)
  have regular:ContDiffAt ℝ ω (a-b) 0:=ha.regular.sub hb.regular
  have integral:OriginalRadialSeries.observed v series=OriginalRadialSeries.scalar (a-b):=by
    rw [OriginalRadialSeries.sub ha.regular hb.regular]
    exact (map_sub _ _ _).trans (congrArg₂ (·-·) ha.read hb.read)
  have change:=germ R N m p hm F tag Z Q cash cap width draw low high x z
  rw [PhysicalForestRay.coefficient (step R m p) F (saddle R N m p F) (model R N m p hm)
    x z tag (source R m p Z Q cap) well (projection R N m p hm F tag),
    change.iteratedDeriv_eq k]
  exact (OriginalRadialSeries.numeric (a-b) regular k).symm.trans (congrArg (coeff k) integral).symm

end YM.Integration.WilsonVacuumPreResetDepositedGeometric
