import YM.Juniper.Mulberry.Table
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply
import YM.Integration.WilsonMovingLogCurrency

/-! Book the short-log estimates on the same register, alloy and factor that
issue the physical Wilson run. All future cutoffs use this one delay. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogForecast
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Input Supply Push.PriceCompiler ThroughLaunch Height Opera Roof Roost Next.Foundations
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Juniper
open scoped Classical Topology
variable {G : Gauge}

def Eligible : Prediction G := fun {_} {_} {A} K => Mulberry.Lanterns K.shape A.delay

theorem prepaid : FundedPredictionSupply.AllPrices (@Eligible G) := by
  intro s prices target expense charted programs wages baton wanting
  refine ⟨fun _ => 0, ?_⟩
  intro l _ D w U Z postages scouts θ requests post V _
  let M : Metals G := ⟨ThroughLaunch.raise s l, ThroughLaunch.raging s prices, chart G, chart_ok G⟩
  obtain ⟨W,later,lit⟩ := (Mulberry.sunshone G).buy (X:=M) Z post V
  refine ⟨W,later,?_⟩
  intro W' after bar wait tariff funded _alloy η q E X J K b sheltered working divides
  exact (Mulberry.sunshone G).mono lit after

/-- The registered table on the actual step, for all its tested forests, chart
choices, genuine bare-cash receipts and allowed incoming upper activities. -/
theorem day (R : Run G) (lit : Eligible R.kit) (m r : ℕ)
    (eligible : r ≤ R.alloy.B.a.clock.J (m+1)) :
    Mulberry.Day R.kit.target R.rolls R.kit.shape (R.alloy.B.a.clock.J (m+1))
      (R.alloy.B.a.clock.J m) r (R.alloy.B.a.clock.hatBeta m) :=
  lit.day _ _ (step_paid _ m) _ (R.alloy.B.valid.pays m) r eligible

end YM.Integration.WilsonMovingLogForecast
