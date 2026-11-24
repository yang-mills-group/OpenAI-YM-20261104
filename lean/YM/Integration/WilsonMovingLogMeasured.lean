import YM.Integration.WilsonMovingLogForecast
import YM.Integration.WilsonMovingLogStation

/-! Real short-log derivatives for the original upper Wilson regular activities,
with their true single vacuum factor and remaining rejected configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogMeasured
open Function Filter Lattice RG Pressure Pressure.Testing Wilson Input Org
open Push Push.AbsoluteSums Push.Uniform Push.PriceCompiler Precision
open PhysicalNext PhysicalNext.Repeat Legato Boulevard Roost Sienna Pane Lapis
open Tree Further.PhysicalPeriodLimitF933.Mural Planned.JetPort AnalyticBridge VerifiedReset Collection Quotes RG.Shoot
open Juniper Juniper.Bright Juniper.Mulberry ConnectedActivityE6 Coat
open Push.SectorMeasure Fare Gauge Blaze Brush ThroughLaunch
open scoped Topology Classical
variable {G : Gauge} (R : Run G) {N m per r : ℕ}
local notation "J" => R.alloy.B.a.clock.J (m+1)
local notation "I" => R.alloy.B.a.clock.J m
local notation "x" => R.alloy.B.a.clock.hatBeta m
local notation "y" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "L" => R.rolls.L J
local notation "H" => Lattice.Ratio.exact_size (R.alloy.B.a.S.oneStep m per)
local notation "S" => Pane.panel R.alloy m H
local notation "T" => WilsonVacuumPreResetColdInput.tube R N per m
local notation "Bf" => R.family.path.levels.budget (m+1)
local notation "Bc" => R.family.path.levels.budget m
local notation "β" => R.family.path.β N per (m+1)
local notation "α" => R.alloy.B.kin.alpha N m
local notation "u" => (WilsonVacuumPreResetColdInput.rows (Rep.activities (R.family.path.rep N per (m+1))))
local notation "v" => R.metals.p.profile J
local notation "k" => RG.Stage.order (R.metals.p.profile I)
local notation "o" => Mulberry.perchK r k + 1 + 2

/-- At each admissible true period and submitted forest, preserve the actual
upper `E` and its slate and the old running coefficient on the same alloy. -/
theorem original (lit : WilsonMovingLogForecast.Eligible R.kit) (live : m<N)
    (grade : r≤J) (F : Forest (S).ratio) (tags : (S).Choices)
    (quilt : Quilt T F (widest R.rolls R.kit.target J I x))
    (cash : Chartlet R.kit.shape R.alloy N m H (Pane.virgin T Bf β))
    (ρ : Bid.Dir G (R.family.side m per) → AxisChart G F)
    (chart : (Mulberry.taste G (S).patch (S).kernel o v).Service F (T).high (T).up ρ)
    (tilt : Tilt o (eaves G L x) (Delay.fineMonitor G L x ^ 2) (shadow G L x) 1
      (adjustment F ρ u))
    (w : Positions (Uniform.Primary (R.family.side m per) G))
    (quiet : flags (Bc).threshold (Boulevard.actual w) = ∅)
    (inside : ‖w‖ + 2*furl G L x < eaves G L x) :
    0 < crestF T Bf β u w ∧
    Brush k (7*y^(aspiring J r)) (eaves G L x)⁻¹
      (aura T Bf α β u - quasar T F R.metals.O tags ρ α u (blast r) β) w := by
  have day := WilsonMovingLogForecast.day R lit m r grade
  have patch : (S).patch = Further.PhysicalPeriodLimitF933.Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (m+1)) := cash.laws.data.funds.patch rfl rfl
  have ht := PriceCompiler.beta_eq R.alloy.B.valid m
  have lo : R.alloy.B.a.clock.loopCap m ≤ ConnectedActivityE6.loopBill G L x :=
    (coverBill R.alloy.B.a m).2.trans (brace x day.1)
  have hi : R.alloy.B.a.clock.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G L x :=
    (coverBill R.alloy.B.a _).2.trans_eq (by unfold ConnectedActivityE6.loopBill Delay.fineMonitor; rw [← ht]; rfl)
  have caps : (T).up.Bounds (T).high (v).width (v).paths (ConnectedActivityE6.loopBill G L x) ∧
      (T).down.Bounds (T).low (R.metals.p.profile I).width (R.metals.p.profile I).paths (ConnectedActivityE6.loopBill G L x) := by
    rw [← params_eq R.alloy.B.valid (m+1), ← params_eq R.alloy.B.valid m]
    exact ⟨{ R.alloy.B.support.cap N (m+1) live with two := budget_loosen (R.alloy.B.support.cap _ _ live).two hi },
      { R.alloy.B.support.cap N m live.le with two := budget_loosen (R.alloy.B.support.cap _ _ live.le).two lo }⟩
  have original := WilsonVacuumPreResetColdInput.original R (per:=per) live
  have hρ := (WilsonMovingLogStation.classical R live F quilt _ ρ chart).1
  have result := day.2.2 _ _ S T F tags Bf Bc u (R.alloy.B.a.clock.adm _) patch R.alloy.B.valid.kernel
    quilt (congrArg RG.Stage.clip (params_eq R.alloy.B.valid _))
    (congrArg RG.Stage.clip (params_eq R.alloy.B.valid _)) caps.1 caps.2 ρ chart hρ rfl α
    (Boulevard.coupling R.alloy N m live) β _ cash
    (WilsonMovingLogStation.incoming R (per:=per) live)
    ⟨original.2.1,original.2.2.1⟩ tilt w quiet inside
  rw [R.kit.settles J I, ← ht] at result
  exact result

end YM.Integration.WilsonMovingLogMeasured
