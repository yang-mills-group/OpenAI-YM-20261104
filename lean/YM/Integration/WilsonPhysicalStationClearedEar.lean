import YM.Integration.WilsonPhysicalStationFullEar
import YM.Integration.WilsonPhysicalStationMeasuredCash
import YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair
import YM.Integration.WilsonPhysicalStationMeasuredEar
import YM.Integration.WilsonPhysicalStationThermalRawMenu
import YM.Integration.WilsonPhysicalStationThermalNominated

/-! Original all-axis Wilson and Wick reporting on the same appointed,
uniquely lower-corrected factory column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationClearedEar
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

open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationRegisteredDiagonal (ratio)
open WilsonPhysicalStationThermalStart (entered)

def cleared (A:Vane R.family D)(B:Vane R.family D') {N p:ℕ}(cb:B.checked f H D')(top:B.k < N)
    (a:(F₀).Index)(W:R.family.label h)(x:Points 2)(z:(standard R.family).Field h)(Q:ℕ)(bill κ:ℝ):Prop:=
    let q:=((F₀).grades a).2
    let E:=aperture R A.k B.k h (Station.mag (AX) A.b A.k) (Station.mag (AX) B.b B.k)
    let Γ:=born R h (tested (AX) A.b A.k x) z
    let ρ:=rate R A.k B.k h
    let χ:ℂ:=signal R N p A.k B.k h q (Station.mag (AX) A.b A.k) (Station.mag (AX) B.b B.k)
    let y:=entered R B (⟨h,db⟩:Fin (D'+1)) (p:=p) cb top (Pi.single a 1)
    let actual:=WilsonPhysicalStationTableJump.pair R (⟨h,da⟩:Fin (D+1)) N p A.k (choose (AX) A.b A.k x)
      (y-(R.family.factory h N p).terminal W) (A.wheel.atCut (N,p) (⟨h,da⟩:Fin (D+1)) z)
    ‖actual-χ*Γ a‖ ≤ 2*E*6^q*
      (bill*4^Q*((AX).clock.monitor A.k)^(-κ)*((ratio R A.k)^q+Fintype.card (F₀).Index*ρ)+ρ*∑i,‖Γ i‖)

include L fac simple source in
theorem original (a b:(F₀).Index)(weight:((F₀).grades a).1=h)(ordered:rank (C) h a ≤ rank (C) h b)(s:Signed)(side:Fin 2)
    (dep u θ:ℕ)(coin z roof:ℝ)(active:100*(h+1) ≤ dep)(shelf:100*(h+1) ≤ θ)
    (two:2 ≤ u)(wide:(dep:ℝ)+6 ≤ roof)(tax:∀i ≤ dep,generator G i ≤ z)(horizon:h=e+1)
:
    ∀ᶠ m:ℕ in atTop,∀P:Tapes.Panel dep,P.θ=θ→P.currency=coin→P.arc ≤ roof→
      ∀ (A:Vane (C) D)(B:Vane (C) D'),A.k=m→B.k=A.k+1→
      ∀ (ca:A.checked f H D)(cb:B.checked f H D'),
      WilsonMovingForkReporterNamedInk.Filed bnd R.makes O J P A u z→
      ((AX).params A.k).columns*err R A.k ≤ 1/2→4 ≤ (AX).clock.monitor A.k→
      ((AX).params B.k).columns*err R B.k ≤ 1/2→
      ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k < N,∀U:R.family.label h,
       Receipt R A B h e da db (p:=p) ca cb top a U→
       ∀ ξ:Points 2, tested (AX) A.b A.k ξ∈K→FitSky (AX) A.b A.k ξ→
        cleared R h da db A B (p:=p) cb top a U ξ (probe (C) b s side)
           (rank (C) h b) (owed (C) h K compact clear b s side) (1/(16*(u:ℝ))):=by
  filter_upwards [WilsonPhysicalStationFullEar.original R L fac h e da db K compact clear bnd simple source O J
    a b weight s side dep u θ coin z roof active shelf two wide tax horizon,
    WilsonIndependentRegisteredActuators.original R simple] with m office clock
  intro P th currency fits A B same dates ca cb auth gate large next
  filter_upwards [office P th currency fits A B same dates ca cb auth gate large] with N charges
  intro p top U stamped ξ inside fit
  have heat:=((clock.2.2 N p (show m < N by omega)).1)
  have close:Next.Rank.Price.shrink R.family A.k N p ≤ 6*Next.Rank.Price.shrink R.family B.k N p:=by
    simpa [dates,same] using heat
  have positive:0 ≤ owed R.family h K compact clear b s side:=
    Finset.sum_nonneg (fun i _=>add_nonneg (abs_nonneg _) (abs_nonneg _))
  exact WilsonPhysicalStationMeasuredCash.original R A B h da db (p:=p) cb dates top a U ξ (probe (C) b s side)
    (rank (C) h b) ordered _ _ positive large next close (charges p top U stamped ξ inside fit)

end YM.Integration.WilsonPhysicalStationClearedEar
end
