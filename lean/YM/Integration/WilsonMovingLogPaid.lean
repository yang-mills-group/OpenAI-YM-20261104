import YM.Integration.WilsonMovingLogMeasured
import YM.Integration.WilsonMovingLogRate

/-! The original signed short logarithm through the physical fine-coupling
order, on the earned fresh chart with every actual old regular row. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogPaid
open Function Filter Lattice RG Pressure Pressure.Testing Wilson Input Org
open Push Push.AbsoluteSums Push.Uniform Push.PriceCompiler Precision
open PhysicalNext PhysicalNext.Repeat Legato Boulevard Roost Sienna Pane Lapis
open Tree Further.PhysicalPeriodLimitF933.Mural Planned.JetPort AnalyticBridge VerifiedReset Collection Quotes RG.Shoot
open Juniper Juniper.Bright Juniper.Mulberry ConnectedActivityE6 Coat
open Push.SectorMeasure Fare Gauge Blaze Brush ThroughLaunch
open scoped Topology Classical
variable {G:Gauge}

theorem original (R:Run G) (simple:G.Simple) (lit:WilsonMovingLogForecast.Eligible R.kit)
    (r:ℕ) {a ε:ℝ} (order:8*a<7*(r+1:ℕ)) (positive:0≤a) (tender:0<ε) :
    ∀ᶠ m:ℕ in atTop, ∀ N per:ℕ, m<N →
      let J := R.alloy.B.a.clock.J (m+1)
      let I := R.alloy.B.a.clock.J m
      let x := R.alloy.B.a.clock.hatBeta m
      let L := R.rolls.L J
      let H := Lattice.Ratio.exact_size (R.alloy.B.a.S.oneStep m per)
      let S := Pane.panel R.alloy m H
      let T := WilsonVacuumPreResetColdInput.tube R N per m
      let Bf := R.family.path.levels.budget (m+1)
      let Bc := R.family.path.levels.budget m
      let β := R.family.path.β N per (m+1)
      let α := R.alloy.B.kin.alpha N m
      let u := (WilsonVacuumPreResetColdInput.rows (Rep.activities (R.family.path.rep N per (m+1))))
      let v := R.metals.p.profile J
      let k := RG.Stage.order (R.metals.p.profile I)
      let o := Mulberry.perchK r k + 1 + 2
    ∀ (F : Forest (S).ratio) (tags : (S).Choices)
    (_quilt : Quilt T F (widest R.rolls R.kit.target J I x))
    (_cash : Chartlet R.kit.shape R.alloy N m H (Pane.virgin T Bf β))
    (ρ : Bid.Dir G (R.family.side m per) → AxisChart G F)
    (_chart : (Mulberry.taste G (S).patch (S).kernel o v).Service F (T).high (T).up ρ)
    (_tilt : Tilt o (eaves G L x) (Delay.fineMonitor G L x ^ 2) (shadow G L x) 1
      (adjustment F ρ u))
    (w : Positions (Uniform.Primary (R.family.side m per) G))
    (_quiet : flags (Bc).threshold (Boulevard.actual w) = ∅)
    (_inside : ‖w‖ + 2*furl G L x < eaves G L x),
    0 < crestF T Bf β u w ∧
    Brush k (ε*(Pert.Asymptotics.regulatorRun R.family N per (m+1))^a) (eaves G L x)⁻¹
      (aura T Bf α β u - quasar T F R.metals.O tags ρ α u (blast r) β) w := by
  filter_upwards [WilsonMovingLogRate.physical R simple r order positive tender] with m earned
  intro N per live
  dsimp only
  intro F tags quilt cash ρ chart tilt w quiet inside
  have h:=WilsonMovingLogMeasured.original R lit live earned.1 F tags quilt cash ρ chart tilt w quiet inside
  exact ⟨h.1,h.2.climb (earned.2 N per live) le_rfl⟩

end YM.Integration.WilsonMovingLogPaid
end
