import YM.Integration.WilsonReportingAbsoluteInletCaptured
import YM.Integration.WilsonReportingAbsoluteInletLiveRun

/-! The originally elected capped run keeps the signed planted interpolation
on every mask of each entire submitted roster. One time threshold precedes
the masks, the upper dates and all periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletFundedRun
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift
open InletSusceptibility.Packet WilsonReportingAbsoluteInletNativeDates
open WilsonReportingAbsoluteInletNativeCoordinates WilsonReportingAbsoluteInletNativeInvoice
open scoped Classical BigOperators Topology
open WilsonReportingAbsoluteInletCaptured
variable {G:Gauge}

def Reported (R:Run G) (κ:ℝ) : Prop :=
  ∀{c:ℝ}, 1<c → ∀ (P q:ℕ) (b:Roster G) (h:ℕ→ℕ→ℕ→ℝ),
    InversePrice R (rank κ P q b) h → ∀{ε:ℝ},0<ε →
    ∀ᶠ k:ℕ in atTop,∀s:Finset (Fin b.length),s.Nonempty→∀u,ultraviolet R.family c k≤u →
      let t:=inlet R P u
      let N:=u+1
      ∃tu:t≤u,∀per,∀ T:Slices R.family.path.levels per,∀ (o:Fin b.length→Site (R.family.side N per)) i,i∈s→
        ∀ (z e:Site (R.family.side N per)) (part:Bool),
          let d:=traversal T (tu.trans u.le_succ)
          let x:=shifts R per t N
          let v:=finite R N per t (h N per)
          let δ:=x-v
          let g:=regulatorRun R.family N per N
          let β:=Descent.offset v g
          let φ:=WilsonReportFrozenTraversal.planted R b s o i z e part
          let A:=WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1-d.conditioned β φ 1
          (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤cost κ P b s/g^loss κ P b s) ∧
          (∃r∈Set.Ioo (0:ℝ) 1,A=∑j∈interior d,δ (WilsonUniformUnmarkedInletEnergySites.lag d j)*picture d β δ 1 φ r j) ∧
          |A|/g^engineering b s≤ε*g^(q+1)

end YM.Integration.WilsonReportingAbsoluteInletFundedRun

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

theorem selectRunWithAbsoluteMarkedForecast (cap : ℕ → ℕ) (mono : Monotone cap) (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ Ξ : Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL : EventuallyPaid Ξ)
    (hfinish : ∀ a, Ξ a → YM.Integration.NativeFVAPlateau.Funded a → Λ a)
    (Demand : Sheet G → Precision.MapPrices → Type v) (hDemand : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R:Run G)(T:Campaign R), (∀ t,cap t≤(R.metals.p.profile t).order) ∧ prediction R.kit ∧ R.family.path.levels.clock.kernel.penalty=b ∧
      PostnumericPreselection Demand extra numeric postnumeric R ∧
      (∀ j, j ≤ (R.metals.p.profile j).order ∧
        j ≤ (R.metals.p.profile j).power) ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      YM.Integration.CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧ ReadoutPurchase R.b ∧
      WilsonWindowReportingPace.Slow R.kit ∧
      ∃Θ v,ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price := by
  obtain ⟨R,T,tall,old,penalty,pre,orders,levels,treasury,period,pillars,
    funded,news,reading,slow,Θ,v,custody,sky,dates⟩:=
    selectRunWithAbsoluteInletDates cap mono Ω ℋ Δ b hb h hL hfinish Demand hDemand extra numeric postnumeric (@prediction) paid
  refine ⟨R,T,tall,old,penalty,pre,orders,levels,treasury,period,pillars,funded,news,reading,slow,Θ,v,custody,sky,dates,?_⟩
  intro c hc P q roster forecast income ε ep
  exact WilsonReportingAbsoluteInletCaptured.roster sky h slow.2 slow.1 hc P q roster forecast income ep
end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
