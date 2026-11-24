import YM.Integration.WilsonPhysicalStationThermalBookedAxes
import YM.Integration.WilsonPhysicalStationMeasuredEar
import YM.Integration.WilsonPhysicalStationThermalRawMenu
import YM.Integration.WilsonPhysicalStationThermalNominated

/-! Original all-axis Wilson and Wick reporting on the same appointed,
uniquely lower-corrected factory column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBookedEar
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open WilsonPhysicalStationThermalVotes (votes offered)
open WilsonPhysicalStationThermalPair (cell)
open scoped Topology BigOperators Classical
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Labels Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open Source Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal Next.Rank.Ribbon MergeProof.Accent Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickStretched (rates)
open WilsonReporterWeightedRankPrice (heats)
open scoped Topology BigOperators Classical
open WilsonPhysicalStationThermalBasisOffice (rank low plain)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalPortfolio (residual)

open Planned.GuardedAtom OPE Push.RelayDifference
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationThermalBookedAxes (owed)
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationSelectedLower (Receipt)
open WilsonPhysicalStationMeasuredEar (signed)
open PhysicalNext.Repeat.Legato Bandage Campaign
set_option quotPrecheck false

variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}
    {S:Table R.family.book}(fac:Facilities R.family f S){H:(Bel R.family.book).Hierarchy}
    {D D':ℕ}(h e:ℕ)(da:h < D+1)(db:h < D'+1)
local notation "C" => R.family
local notation "AX" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "d₀" => (⟨h,da⟩:Fin (D+1))
variable (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
variable {W:Bid.Worth}{u₀ ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m < N→GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
    (bnd:Binding R.family)(simple:G.Simple)
    (source:Scrim R.family W u₀ ψ φ δ (fly R.family.path.levels) r door)
    (O:HaarBudget G)(J:ChartRatio G)

include L fac simple source in
theorem original (a b:(F₀).Index)(weight:((F₀).grades a).1=h)(s:Signed)(side:Fin 2)
    (dep u θ:ℕ)(coin z roof:ℝ)(active:100*(h+1) ≤ dep)(shelf:100*(h+1) ≤ θ)
    (two:2 ≤ u)(wide:(dep:ℝ)+6 ≤ roof)(tax:∀i ≤ dep,generator G i ≤ z)(horizon:h=e+1)
    (off:∀x∈K,∀i,((F₀).grades i).2≠rank (C) h b→born R h x (probe (C) b s side) i=0):
    ∀ᶠ m:ℕ in atTop,∀P:Tapes.Panel dep,P.θ=θ→P.currency=coin→P.arc ≤ roof→
      ∀ (A:Vane (C) D)(B:Vane (C) D'),A.k=m→B.k=A.k+1→
      ∀ (ca:A.checked f H D)(cb:B.checked f H D'),
      WilsonMovingForkReporterNamedInk.Filed bnd R.makes O J P A u z→
      ((AX).params A.k).columns*err R A.k ≤ 1/2→4 ≤ (AX).clock.monitor A.k→
      ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k < N,∀U:R.family.label h,
       Receipt R A B h e da db (p:=p) ca cb top a U→
       ∀ ξ:Points 2, tested (AX) A.b A.k ξ∈K→FitSky (AX) A.b A.k ξ→
        signed R A B h da db (p:=p) cb top a U ξ (probe (C) b s side)
           (rank (C) h b) (owed (C) h K compact clear b s side) (1/(16*(u:ℝ))):=by
  filter_upwards [WilsonPhysicalStationThermalBookedAxes.original R (f:=f) (S:=H) (d₀) K compact clear
    bnd simple source O J b s side dep u θ coin z roof active shelf two wide tax] with m bought
  intro P th cash paid A B same dates ca cb files gate large
  filter_upwards [bought P th cash paid A same ca files] with N earnings
  intro p top U issued ξ inside fit
  have live:A.k < N:=by omega
  obtain ⟨positive,menu⟩:=earnings p live ξ inside fit
  have scale:(2:ℝ) ≤ u:=by exact_mod_cast two
  have small:1/(16*(u:ℝ)) ≤ 1/2:=by
    apply (div_le_div_iff₀ (by linarith) (by norm_num)).2
    linarith
  exact WilsonPhysicalStationMeasuredEar.original R L fac A B h e da db (p:=p) simple ca cb dates top horizon
    gate a weight U issued ξ (probe (C) b s side) (rank (C) h b) _ _ positive large small
    (fun i hi=>(menu i).1 hi) (fun i hi=>(menu i).2 hi) (off _ inside)

end YM.Integration.WilsonPhysicalStationBookedEar
end
