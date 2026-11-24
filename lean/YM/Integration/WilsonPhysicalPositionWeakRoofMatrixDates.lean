import YM.Integration.WilsonPhysicalPositionWeakRoofMatrixRun
import YM.Integration.WilsonThermometerOrdinarySelection

/-! The same matrix-funded physical campaign carries the full original thermal Sky, every intervening date, and all original weak panels. -/
set_option autoImplicit false
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
set_option quotPrecheck false
open Boutique
open Daisy.Charity.RG12
universe v


open YM.Integration WilsonWindowJointPurchase

def ReporterRoofs.Admitted (ν:Side→ℕ→ℕ→ℝ) (R:Run G):Prop :=
  ReporterRoofs.Roofed R.kit ∧ RestoredBooking ν R.b

theorem ReporterRoofs.dates (ν:Side→ℕ→ℕ→ℝ) (hνpos:∀ L j d,0<ν L j d) (cap : ℕ → ℕ) (mono : Monotone cap) (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ Ξ : Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL : EventuallyPaid Ξ)
    (hfinish : ∀ a, Ξ a → YM.Integration.NativeFVAPlateau.Funded a → Λ a)
    (Demand : Sheet G → Precision.MapPrices → Type v) (hDemand : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    {claim : FundedCompanySelection.Prediction G} (supply:YM.Integration.WilsonMatrixTicketLengthsLender.Supply G (@claim))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R:Run G)(T:Campaign R), ReporterRoofs.Admitted ν R ∧ (∀ t,cap t≤(R.metals.p.profile t).order) ∧ (claim R.kit ∧ prediction R.kit) ∧ R.family.path.levels.clock.kernel.penalty=b ∧
      PostnumericPreselection Demand extra numeric postnumeric R ∧
      (∀ j, j ≤ (R.metals.p.profile j).order ∧
        j ≤ (R.metals.p.profile j).power) ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      YM.Integration.CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧ ReadoutPurchase R.b ∧
      WilsonWindowReportingPace.Slow R.kit ∧
      ∃Θ v,ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.OrdinaryDates R := by
  let grant:FundedCompanySelection.Prediction G:=Together (@prediction) (@WilsonWindowReportingPace.Slow G)
  have financial:WilsonFundedWindowMenu.AllPrices (@grant):=fun s M=>
    joint (paid s M) (WilsonWindowReportingPace.prepaid h s _)
  obtain ⟨R,T,tall,⟨⟨licensed,old,slow⟩,panels,roofs⟩,restored,penalty,pre,orders,levels,treasury,period,pillars,funded,news,reading,Θ,v,custody,sky⟩:=
    ReporterRoofs.matrixRun ν hνpos cap mono Ω ℋ Δ b hb h hL hfinish Demand hDemand extra numeric postnumeric supply (@grant) financial
  exact ⟨R,T,⟨roofs,restored⟩,tall,⟨licensed,old⟩,penalty,pre,orders,levels,treasury,period,pillars,funded,news,reading,slow,Θ,v,custody,sky,
    ⟨WilsonReportingAbsoluteInletLiveRun.on_run R h slow,panels⟩⟩
end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
