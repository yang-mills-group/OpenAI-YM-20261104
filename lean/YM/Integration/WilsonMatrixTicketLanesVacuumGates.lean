import YM.Integration.WilsonMovingCourseElection
import YM.Integration.WilsonMovingMentorOwnership
import YM.Integration.WilsonMatrixTicketLanesVacuumKeptOriginal

/-! The original Ward reporting date and column allowance on the signed moving physical course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumGates
open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMovingShadowPrices WilsonMovingStoredFactor
variable {G:Gauge}

/-- The two forecasts that are independent of the original moving factor's expense. -/
def Stock : Prediction G := @FundedPredictionSupply.Both G
  (@WilsonMatrixTicketLanesConnectedBudget.Paid G) (@WilsonMatrixTicketLanesReportedPrepaid.Paid G)

theorem stock : FundedPredictionSupply.AllPrices (@Stock G):=fun s cost=>
  FundedPredictionSupply.both (WilsonMatrixTicketLanesConnectedBudget.allPrices s cost)
    (WilsonMatrixTicketLanesReportedPrepaid.allPrices s cost)

def Dates : Prediction G := @FundedPredictionSupply.Both G (@WilsonWindowReportingPace.Slow G)
  (@WilsonReportColumnSubsidy.Eligible G)

/-- Both physical cutoff appointments are made before seeing the periods on this same charged factor. -/
theorem dates (ask:Ask) (slow:ℝ→ℝ) (simple:G.Simple):
    WilsonMovingCommonPrices.AllPrices ask slow (@OnMenu G (@Dates G)):=by
  intro s T rows E charts C v baton wanting wage
  refine ⟨0,?_⟩
  intro l hl earlier D w fees Z φ scouts θ p P V pocket cap
  obtain ⟨U,vu,offered⟩:=RG16.later D simple V (fun _=>0)
  obtain ⟨W,uw,subsidy⟩:=subsidize_feasible (G:=G) U
  refine ⟨W,vu.trans uw,?_⟩
  intro Y wy bar wait priced B light A η z E' X J K' b shelter works divides menu
  obtain ⟨plenty,pace⟩:=offered Y (uw.trans wy) wait B.a B.valid
  exact ⟨⟨plenty,fun m=>(le_max_left _ _).trans (pace m)⟩,subsidy Y wy wait B.a B.valid⟩

/-- The stronger original archive buyer can spend the same two appointments. -/
theorem on_archive (ask:Ask) (slow:ℝ→ℝ) (simple:G.Simple):
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Dates G)):=by
  intro s T rows E charts C v baton wanting wage
  obtain ⟨u,buy⟩:=dates ask slow simple s T rows E charts C v baton wanting wage
  refine ⟨u,?_⟩
  intro l hl earlier D w fees Z φ scouts θ p P V pocket cap
  obtain ⟨W,vw,use⟩:=buy l hl earlier D w fees Z φ scouts θ p P V pocket cap
  refine ⟨W,vw,?_⟩
  intro Y wy bar wait priced B light A η z E' X J K' b shelter works divides _ menu
  exact use Y wy bar wait priced B light η z E' X J K' b shelter works divides menu

end YM.Integration.WilsonMatrixTicketLanesVacuumGates
