import YM.Integration.WilsonPhysicalHistoryRetainedSpringGaussian
import YM.Integration.WilsonCoherentMayerCovarianceCalendar
import YM.Integration.WilsonVacuumPreResetRenderIncome

/-! Fixed powers of the incoming covariance and spatial width are paid
before the cutoff, period and chamber choices. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics
open Pressure Precision Exterior PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Physical MeasureTheory
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open WilsonRetainedStencilMoment
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

def speedScale (G : Gauge) (u : ℕ) : ℝ:=
  (1+G.colorScale*‖colorReader G‖)*(1+(Fintype.card G.ColorIndex:ℝ))*(1+unitMoment (u+1))

private theorem scale_pos (G : Gauge) (u : ℕ) : 0<speedScale G u:=by
  unfold speedScale
  have hc:=G.colorScale_pos
  have hm : 0≤unitMoment (u+1):=integral_nonneg fun z : ℝ=>by positivity
  positivity

private theorem log_width {G : Gauge} {V : Levels G} {m n : ℕ} {σ W : ℝ}
    (hs : 0<σ) (width : σ⁻¹≤zz V (m+1)) (stage : 1≤zz V (m+1))
    (o : Target.Order G W) (u : ℕ)
    (earned : WilsonCoherentMayerCovarianceCalendar.deviation G (V.clock.op m n).patch.L o ≤
      1+Real.log (betaF G (V.clock.hatBeta m) (V.clock.op m n).patch.L)) :
    2*speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample u /σ ≤
      (6*speedScale G u)*Real.exp (2*zz V (m+1)) := by
  let z:=zz V (m+1)
  let b:=V.clock.hatBeta (m+1)
  have lb : 0<Real.log b:=Real.log_pos (V.fits.delayed _)
  have hz : 0≤z:=zero_le_one.trans stage
  have expz : 1≤Real.exp z:=Real.one_le_exp hz
  have lw : Real.log b≤Real.exp z:=by
    rw [←Real.exp_log lb]
    apply Real.exp_le_exp.mpr
    change Real.log (Real.log b)≤1+Real.log (Real.log b)
    linarith
  have cap:=earned
  rw [←ConnectedActivityE6.Application.clock_next V m n] at cap
  have radial : speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample u≤
      speedScale G u*(3*Real.exp z) := by
    unfold speedPrice scalarPrice speedScale
    unfold WilsonCoherentMayerCovarianceCalendar.deviation at cap
    have lx : 1+Real.sqrt (payE o.eta o.gap o.ample (tubularPrice G (V.clock.op m n).patch.L)) ≤
        3*Real.exp z := by change _ ≤1+Real.log b at cap; linarith
    have hu : 0≤unitMoment (u+1):=integral_nonneg fun z : ℝ=>by positivity
    have hc:=G.colorScale_pos
    calc _ ≤ (1+G.colorScale*‖colorReader G‖)*(1+(Fintype.card G.ColorIndex:ℝ))*
          ((3*Real.exp z)*(1+unitMoment (u+1))) := by gcongr
      _ = _ := by ring
  have iw : σ⁻¹≤Real.exp z:=width.trans ((by linarith : z≤z+1).trans (Real.add_one_le_exp z))
  rw [div_eq_mul_inv]
  calc
    _ ≤ (2*(speedScale G u*(3*Real.exp z)))*Real.exp z := by gcongr; positivity [scale_pos G u]
    _ = (6*speedScale G u)*Real.exp (2*z) := by rw [two_mul z,Real.exp_add]; ring

theorem cofinal_speed (R : Run G) (simple : G.Simple) (u k d : ℕ) {ε η : ℝ}
    (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop, ∀ N n : ℕ, m<N → ∀ {σ W : ℝ},0<σ → σ⁻¹≤zz V (m+1) →
      ∀ o : Target.Order G W,
      WilsonCoherentMayerCovarianceCalendar.deviation G (V.clock.op m n).patch.L o≤
        1+Real.log (betaF G (V.clock.hatBeta m) (V.clock.op m n).patch.L) →
      (2:ℝ)^(d+1)*(2*speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample u/σ)^k ≤
        ε*(Pert.Asymptotics.regulatorRun R.family N n (m+1))^(-η) := by
  intro V
  let A:=(2:ℝ)^(d+1)*(6*speedScale G u)^k/ε
  have a0 : 0≤A:=by dsimp only [A]; positivity [scale_pos G u]
  let T : Credit:=⟨1,1+A+2*(k:ℝ),by linarith [Nat.cast_nonneg (α:=ℝ) k]⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (exp_at_band T V simple η hp),
    (tendsto_add_atTop_nat 1).eventually ((stamp_lim V simple).eventually_ge_atTop 1)]
      with m bound stage
  intro N n within σ W hs width o earned
  let z:=zz V (m+1)
  have quote:=log_width hs width stage o u earned
  have m0 : 0 ≤ speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample u:=(speed_price_pos ..).le
  have cash:=bound (R.family.path.β N n (m+1)) (R.makes.wilson.represents N n (m+1) within).band.1
  have price : A*Real.exp (2*(k:ℝ)*z) ≤ Real.exp (T.buy z):=by
    calc _ ≤ Real.exp A * Real.exp (2*(k:ℝ)*z) := by
              gcongr; linarith [Real.add_one_le_exp A]
      _ = Real.exp (A+2*(k:ℝ)*z) := (Real.exp_add ..).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change _≤(1+A+2*(k:ℝ))*z^1
        rw [pow_one]
        nlinarith [mul_nonneg a0 (sub_nonneg.mpr stage)]
  apply le_trans _ (mul_le_mul_of_nonneg_left (price.trans cash) ep.le)
  calc
    _ ≤ (2:ℝ)^(d+1)*((6*speedScale G u)*Real.exp (2*z))^k := by
      gcongr
    _ = ε*(A*Real.exp (2*(k:ℝ)*z)) := by
      rw [mul_pow,←Real.exp_nat_mul]
      dsimp only [A]
      rw [show (k:ℝ)*(2*z)=2*(k:ℝ)*z by ring]
      field_simp

end YM.Integration.OriginalMarkedRunAction
