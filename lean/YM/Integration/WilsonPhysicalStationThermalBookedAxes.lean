import YM.Integration.WilsonPhysicalStationThermalBasisOffice
import YM.Integration.WilsonPhysicalStationThermalRawMenu
import YM.Integration.WilsonPhysicalStationThermalNominated

/-! All projected and null raw axes at a genuine pair of sites,
purchased on the original Wilson program before any cutoff or filing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalBookedAxes
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h:ℕ}(d:Fin (h+1))
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels
set_option quotPrecheck false
local notation "I"=>(R.family.labels.level d).Index
variable (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)

def owed (C₀:Family G)(j:ℕ)(K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
    (b:(C₀.labels.level j).Index)(s:Signed)(side:Fin 2):ℝ:=
  ∑a, (|low C₀ j K compact clear b s side a|+|plain C₀ j K compact clear b s side a|)

variable {W:Bid.Worth}{u₀ ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m<N→GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
    (B:Binding R.family)(simple:G.Simple)
    (source:Scrim R.family W u₀ ψ φ δ (fly R.family.path.levels) r door)
    (O:HaarBudget G)(J:ChartRatio G)

include simple source
theorem original (b:(R.family.labels.level d).Index)(s:Signed)(side:Fin 2)(D u θ:ℕ)(e z roof:ℝ)(active:100*(d.val+1)≤D)(shelf:100*(d.val+1)≤θ)
    (two:2≤u)(wide:(D:ℝ)+6≤roof)(tax:∀i≤D,generator G i≤z):
    ∀ᶠ k:ℕ in atTop,∀P:Tapes.Panel D,P.θ=θ→P.currency=e→P.arc≤roof→
      ∀V:Vane C h,V.k=k→∀checked:V.checked f S h,WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z→
      ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:V.k<N,∀ξ:Points 2,tested AX V.b V.k ξ∈K→FitSky AX V.b V.k ξ→
      let T:=(AX).clock.monitor V.k
      let eps:=T^(-(1/(16*(u:ℝ))))
      let bill:=owed C d K compact clear b s side
      let err:=fun a:I=>residual R V d (p:=p) checked fine V.k
        (choose AX V.b V.k ξ) (tested AX V.b V.k ξ) (Pi.single a 1) (probe C b s side)
      0≤bill ∧ ∀a:I,
        (rank C d a≤rank C d b→‖err a‖*T^(rank C d b)≤bill*T^(rank C d a)*eps) ∧
        (rank C d b<rank C d a→‖err a‖≤bill):=by
  filter_upwards [WilsonPhysicalStationThermalBasisOffice.original C d K compact clear B R.makes simple
      source O J b s side D u θ e z roof active shelf two wide tax] with k issued
  intro P th ec fits V same checked ink
  have receipts:=issued P th ec fits
  rw [←same] at receipts
  have pairs:=WilsonPhysicalStationThermalRawMenu.original R B O J V d checked P (probe C b s side) (rank C d b) two ink
    (low C d K compact clear b s side) (plain C d K compact clear b s side)
    (fun a ordered=>(receipts a).1 ordered) (fun a _=>(receipts a).2)
  filter_upwards [pairs.2] with N money
  exact fun p fine ξ live fit=>⟨pairs.1,money p fine ξ live fit⟩

end YM.Integration.WilsonPhysicalStationThermalBookedAxes
end
