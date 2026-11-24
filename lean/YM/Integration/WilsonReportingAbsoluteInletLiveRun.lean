import YM.Integration.WilsonPhysicalMarkedDefectTallRun
import YM.Integration.WilsonWindowJointPurchase
import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonReportingAbsoluteInletNativeInvoice

/-! The original capped selection keeps its custody, its Sky and its sampled
prices while purchasing the actual input temperature path before each period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletLiveRun
open Function Filter Finset Real Lattice RG Wilson
open PhysicalNext.Repeat.Legato Pert.Asymptotics RGComparison.Core16
open WilsonReportingAbsoluteInletNativeDates
open WilsonReportingAbsoluteInletNativeCoordinates
open scoped Classical Topology BigOperators
open WilsonReportingAbsoluteInletNativeInvoice
variable {G:Gauge}

def Calendar (R:Run G):Prop :=
  ∀{c:ℝ},1<c→∀(P p:ℕ)(h:ℕ→ℕ→ℕ→ℝ),InversePrice R p h→∀{ε:ℝ},0<ε→
    ∀ᶠ k:ℕ in atTop,∀u,ultraviolet R.family c k≤u→
      let t:=inlet R P u
      let N:=u+1
      ∃tu:t≤u, k≤t ∧
        (N-t:ℕ)*log (3:ℝ)≤R.family.S.scale N-R.family.S.scale t ∧
        R.family.S.scale N-R.family.S.scale t≤(Nat.ceil (width P+2):ℝ)*log (R.family.path.levels.clock.hatBeta N) ∧
        ∀per,∀T:Slices R.family.path.levels per,
          let d:=traversal T (tu.trans u.le_succ)
          let x:=shifts R per t N
          let v:=finite R N per t (h N per)
          let g:=regulatorRun R.family N per N
          0<g ∧ g≤1 ∧ Descent.offset v g+(x-v)=line R.family.path per t N ∧ (x-v) d.depth=0 ∧
            ∀l, l≤d.depth→|(x-v) l| ≤ ε*g^p

theorem on_run (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit):Calendar R :=by
  intro c hc P p h financed ε ep
  exact WilsonReportingAbsoluteInletNativeInvoice.paid R simple slow.2 hc P p h financed ep
/-- The same elected Wilson clock pays both its inlet dates and its three
weak reflected panels before the cutoff and period are read. -/
structure PanelDates (R : Run G) : Prop where
  dates : Calendar R
  panels : R2I.RG05Joint.SmallPanels R.kit

end YM.Integration.WilsonReportingAbsoluteInletLiveRun

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

theorem selectRunWithAbsoluteInletDates (cap : ℕ → ℕ) (mono : Monotone cap) (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ Ξ : Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL : EventuallyPaid Ξ)
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
      ∃Θ v,ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R := by
  let grant:FundedCompanySelection.Prediction G:=Together (@prediction) (@WilsonWindowReportingPace.Slow G)
  have financial:WilsonFundedWindowMenu.AllPrices (@grant):=fun s M=>
    joint (paid s M) (WilsonWindowReportingPace.prepaid h s _)
  obtain ⟨R,T,tall,⟨⟨old,slow⟩,panels⟩,penalty,pre,orders,levels,treasury,period,pillars,funded,news,reading,Θ,v,custody,sky⟩:=
    selectRunAtCappedMenu cap mono Ω ℋ Δ b hb h hL hfinish Demand hDemand extra numeric postnumeric (@grant) financial true
  exact ⟨R,T,tall,old,penalty,pre,orders,levels,treasury,period,pillars,funded,news,reading,slow,Θ,v,custody,sky,
    ⟨WilsonReportingAbsoluteInletLiveRun.on_run R h slow,panels⟩⟩
end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
