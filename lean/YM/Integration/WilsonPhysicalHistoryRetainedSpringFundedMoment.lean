import YM.Integration.WilsonPhysicalHistoryRetainedSpringMomentOrder
import YM.Integration.WilsonPhysicalHistoryRetainedSpringChamberMoment

/-! The elected inlet buys each actual site at its engineering order,
uniformly in every later cutoff, period, forest, coordinate and site. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonStartup Pert.Asymptotics WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem funded_chamber_moment (R : Run G) (simple : G.Simple) (credit : Credit) (d K l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N n : ℕ,m<N →
      let S:=V.clock.op m n
      let s:=V.clock.hatBeta m
      let g:=regulatorRun R.family N n (m+1)
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ {σ W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
        {T : Tube G S} {Y : Rep G (R.family.side (m+1) n)},
      (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s → 0<σ → σ⁻¹≤zz V (m+1) →
      WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
      ∀ (Z : SeriesA G), Draw Z σ D → ∀ a∈Z,a.grade≤d → ∀ (p : ℝ),1/2≤p → p≤3/2 →
      ∀ (χ : Chi) (v : Finset (LocalLTE.Fan.Veil (R.family.side m n) (R.family.side (m+1) n)))
        (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G)
        (x : Site (R.family.side (m+1) n)),
      let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
      let β:=Integral.temperature g
      let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
      let q:=a.rise+K+1
      let D' (z : Air (R.family.side (m+1) n) G):=(w:ℂ)*
        ((sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
          siteTaylor a.cells x (angularSample (Greenbelt.allot i) z) q g)
      Integrable (fun z=>‖D' z‖^(l+1)) X.dice ∧
        (∫ z,‖D' z‖^(l+1) ∂X.dice)≤(ε*g^(((a.grade+K:ℕ):ℝ)-η))^(l+1) := by
  intro V
  filter_upwards [cofinal_moment_price R simple credit d K l ep hp] with m fees
  intro N n later S s g D σ W μ budget P Q o T Y H temp hs width paid Z filed a member cap p lo hi
    χ v i tag y x X β w q D'
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N n (m+1) later
  obtain ⟨integrable,estimate⟩:=chamber_power_moment H temp χ v i tag y Z hs filed a member x
    (a.rise+K) l g p gp lo hi
  have quoted:=fees N n later hs width o paid a cap
  have degree : a.grade-a.rise+(a.rise+K)=a.grade+K:=by have:=a.rankA; omega
  refine ⟨integrable,estimate.trans ?_⟩
  simp only [degree]
  have M:=(speed_price_pos G S.patch.L o.eta o.gap o.ample ((a.rise+K+2)*(l+1)-1)).le
  apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) filed.1)
    (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) M) hs.le) _)) (pow_nonneg gp.le _))
  apply (mul_le_mul_of_nonneg_right quoted (pow_nonneg gp.le (a.grade+K))).trans_eq
  rw [mul_assoc,←Real.rpow_natCast,←Real.rpow_add gp]
  congr 2
  ring

end YM.Integration.OriginalMarkedRunAction
