import YM.Integration.WilsonPhysicalStationMixedSchurNamed
import YM.Integration.WilsonPhysicalStationGradedLowerPanel
import YM.Integration.WilsonPhysicalStationMixedSchurBoard
/-! The genuine named lower Wilson panel retains each source's own thermal leg count. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedEarnedSchur
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

open WilsonMovingForkReporterRankCourse (surplus)
open WilsonMovingForkReporterMixedBasis (Slot Posted ordered ranked flat measured)
open WilsonMovingForkReporterRankMarket (amount)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (votes reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
open WilsonPhysicalStationMixedBasisSale (fee Sold)
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonPhysicalStationMixedListener (value)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMixedChartCharge (wage)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationMixedMeasuredTicket (Reads rate)
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonPhysicalStationMixedSchurNamed (arms Return)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open WilsonPhysicalStationMixedSchurBoard (onLeft charge registered)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D D' h low depth:ℕ}(A:Vane R.family D)(B:Vane R.family D')
    (da:h<D+1)(db:h<D'+1)(ca:A.checked f H D)(cb:B.checked f H D')
    (book:Deck G)(e:ℕ)(dr:e<D+1)(K:Set (Points 2))(compact:IsCompact K)(sep:K⊆conf 2)
local notation "I₀"=>Glyph book e
local notation "F₀"=>R.family.labels.level h
local notation "F₁"=>R.family.labels.level e
local notation "AX"=>R.family.path.levels
local notation "t₀"=>(AX).clock.monitor A.k
local notation "M₀"=>Station.mag (AX) A.b A.k
local notation "M₁"=>Station.mag (AX) B.b B.k
local notation "d₁"=>(⟨h,db⟩:Fin (D'+1))
local notation "d₂"=>(⟨e,dr⟩:Fin (D+1))
def Row (low depth Q:ℕ)(c:I₀→ℂ)(roof:I₀→ℝ)(N:ℕ):Prop:=
  ∀p:ℕ,∀top:B.k<N,∀a:(F₀).Index,∀w:R.family.label h,
    (if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h low da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h low da db (p:=p) ca cb top a w)→
    ∀x:I₀→Points 2,(∀i,tested AX A.b A.k (x i)∈K)→(∀i,FitSky AX A.b A.k (x i))→
      let q:=rank R.family h a
      let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
      let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
      ‖(∑i,c i*WilsonPhysicalStationMixedListener.value R N p A.k (choose AX A.b A.k (x i)) Z
          (A.wheel.atCut (N,p) (d₂) (named R book e i)))-
        χ*∑i,c i*base R h (named R book e i) (tested AX A.b A.k (x i)) a‖*(t₀)^Q ≤
      (∑t:I₀×(F₁).Index,(roof t.1*‖coefficient R book e t.1 t.2‖)*
        charge R A (arms R book e K compact sep h) (h:=h) t depth q (x t.1))*(t₀)^q

open WilsonPhysicalStationGradedLowerPanel (metered frame cross right)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPositionProgramPublicWickGram (reading nodes)
open Trace.Terrace Trace.Over PhysMS OPE XSpace XSpace.Normalize
open scoped Matrix Matrix.Norms.Operator
variable {S:Table R.family.book}(J:Scaling S)(axis:Axis)
local notation "Uₐ"=>J.U A.k

theorem original (sold:Return R A B da db ca cb book e dr K compact sep low depth):
    ∃δ C:ℝ,0<δ ∧ 0<C ∧ ∀u:Points 2,
      ‖(fun i j:I₀=>metered book e t₀ (frame R Uₐ book e axis u) i j)-reading axis (nodes axis) (id:I₀→I₀)‖≤δ→
      ∀(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ),
        let c:=WilsonPhysicalStationGradedLowerPanel.charge R Uₐ book e axis u t₀ Q L
        (∑j:I₀,c j • ear R (e:=e) u (right R Uₐ book e j)=L) ∧
          ∀ᶠ N:ℕ in atTop,Row R A B da db ca cb book e dr K compact sep low depth Q c
            (fun _=>C*‖cross R Uₐ book e axis t₀ Q L‖) N:=by
  obtain ⟨δ,C,up,cp,grant⟩:=WilsonPhysicalStationGradedLowerPanel.original R Uₐ book e axis
  refine ⟨δ,C,up,cp,?_⟩
  intro u close Q L c
  obtain ⟨native,bound⟩:=grant u t₀ (Real.exp_pos _) close Q L
  refine ⟨native,?_⟩
  filter_upwards [sold] with N bought
  intro p top a w posted x inside fit
  apply bought p top a w posted x inside fit Q c _ (fun _=>mul_nonneg cp.le (norm_nonneg _))
  intro j
  exact (bound j).trans_eq (by ring)

end YM.Integration.WilsonPhysicalStationMixedEarnedSchur
end
