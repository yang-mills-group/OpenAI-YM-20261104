import YM.Integration.WilsonReportingAbsoluteInletForecastCanonical
import YM.Integration.WilsonReportingAbsoluteInletFrozenRoster

/-! The original capped election purchases both the before-period kinetic course and
the signed susceptibility. Every reporting roster then uses the inverse book of its
submitted forest and tags at that run's measured coupling. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonReportingAbsoluteInletForecastElection
open Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Wine
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorLabels
open WilsonReportingAbsoluteInletForecastMarket
open WilsonReportingAbsoluteInletFrozenRoster
variable {G : Gauge}

def Bought (R : Run G) (u : G.ColorIndex) (κ : ℝ) : Prop :=
  ∀ (wood : ∀ j, Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch
      R.family.path.levels.clock.kernel n).Choices) {c : ℝ},
    1 < c → ∀ (P q : ℕ) (b : Roster G), Receipt R κ c P q b (price R u wood tags)

theorem on_run (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : MSbar.Heath.Voice G)
    (money : Terms u V R.kit) {κ : ℝ} (fund : WilsonReportingAbsoluteInletFundedRun.Reported R κ) :
    Bought R u κ := by
  intro wood tags c hc P q b
  obtain ⟨forward, capital⟩ :=
    WilsonReportingAbsoluteInletForecastCanonical.course R simple u V money wood tags
      (WilsonReportingAbsoluteInletCaptured.rank κ P q b + 2)
  exact WilsonReportingAbsoluteInletFrozenRoster.purchased R simple fund hc P q b (price R u wood tags) money.2.2.1 forward capital

end YM.Integration.WilsonReportingAbsoluteInletForecastElection

namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.RG05Preconstruction
open YM.Integration.WilsonLimitConstruction
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Campaign
open Boutique
open Daisy.Charity.RG12
universe v


open YM.Integration WilsonWindowJointPurchase

theorem selectRunWithIssuedAbsoluteForecast (cap : ℕ → ℕ) (mono : Monotone cap) (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ Ξ : Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL : EventuallyPaid Ξ)
    (hfinish : ∀ a, Ξ a → YM.Integration.NativeFVAPlateau.Funded a → Λ a)
    (Demand : Sheet G → Precision.MapPrices → Type v) (hDemand : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (u : G.ColorIndex) (V : MSbar.Heath.Voice G) (clear : MSbar.Heath.Clear G V)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R:Run G)(T:Campaign R), (∀ t,cap t≤(R.metals.p.profile t).order) ∧ prediction R.kit ∧ R.family.path.levels.clock.kernel.penalty=b ∧
      PostnumericPreselection Demand extra numeric postnumeric R ∧
      (∀ j, j ≤ (R.metals.p.profile j).order ∧
        j ≤ (R.metals.p.profile j).power) ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      YM.Integration.CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧ ReadoutPurchase R.b ∧
      WilsonWindowReportingPace.Slow R.kit ∧
      ∃Θ v,ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
      WilsonReportingAbsoluteInletForecastElection.Bought R u Θ.price := by
  obtain ⟨R, T, tall, ⟨other, money⟩, penalty, pre, orders, levels, treasury, period,
    pillars, funded, news, reading, slow, Θ, v, custody, sky, dates, report⟩ :=
    selectRunWithAbsoluteMarkedForecast cap mono Ω ℋ Δ b hb h hL hfinish Demand hDemand
      extra numeric postnumeric (@Together G (@prediction) (@WilsonReportingAbsoluteInletForecastMarket.Terms G u V))
      (WilsonReportingAbsoluteInletForecastMarket.joined h u V clear (@prediction) paid)
  exact ⟨R, T, tall, other, penalty, pre, orders, levels, treasury, period, pillars, funded,
    news, reading, slow, Θ, v, custody, sky, dates, report,
    WilsonReportingAbsoluteInletForecastElection.on_run R h u V money report⟩

end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint

