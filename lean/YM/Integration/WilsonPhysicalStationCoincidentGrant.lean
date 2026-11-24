import YM.Integration.WilsonPhysicalStationCoincidentObserved
import YM.Integration.WilsonPhysicalStationCoincidentLower
import YM.Integration.WilsonPhysicalStationFullEar

/-! The earned physical two-colour Wilson measurement for two distinct filings at the same date. Every reflected detector sees the same original lower removal. -/


set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentGrant
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationThermalPair (cell)
open WilsonPhysicalStationTableJump (pair)
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Rise Alarm Paint Next.Rank.Station Glimmer
open Ward MergeProof.Accent Next.Rank.Ribbon
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h  <  D+1) (db:h  <  D'+1)
local notation "a₀" => (⟨h,da⟩:Fin (D+1))
local notation "b₀" => (⟨h,db⟩:Fin (D'+1))
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "μ" => (F₀).coeffSize
local notation "P₀" => Columns.low (F₀) e
local notation "K₀" => R.family.factory h N p
local notation "C₀" => ((L₀).params A.k).columns
local notation "C₁" => ((L₀).params B.k).columns
local notation "δ₀" => barunit (R.family.S.block A.k)
local notation "D₀" => (F₀).scaled (ratio R A.k)

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


local notation "t₀" => (shrink R.family A.k N p)⁻¹
local notation "t₁" => (shrink R.family B.k N p)⁻¹



open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationCoincidentLower (Receipt)
open WilsonPhysicalStationCoincidentEntry (rent)
open WilsonPhysicalStationMeasuredCash (aperture)
local notation "T₀" => (L₀).clock.monitor A.k

def signed (cb:B.checked f H D') (top:B.k < N) (a:(F₀).Index) (W:R.family.label h)
    (x:Points 2)(z:(standard R.family).Field h)(Q:ℕ)(J κ:ℝ):Prop:=
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let q:=((F₀).grades a).2
    let χ:ℂ:=aperture R A.k B.k h (M₀) (M₁)
    let Γ:=born R h (tested (L₀) A.b A.k x) z
    let ρ:=rent R A.k
    (1-err R B.k)*‖WilsonPhysicalStationTableJump.pair R (a₀) N p A.k (choose (L₀) A.b A.k x) (y-(K₀).terminal W)
        (A.wheel.atCut (N,p) (a₀) z)-χ*Γ a‖*(t₀)^Q ≤
        purse R N p A.k B.k h q (M₀) (M₁)*
          (J*4^Q*(T₀)^(-κ)*(1+Fintype.card (F₀).Index*ρ)+ρ*∑ i,‖Γ i‖)

include fac in
theorem mounted (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h)
    (W:R.family.label h) (issued:Receipt R A B h e da db (p:=p) ca cb top a W)
    (x:Points 2) (z:(standard R.family).Field h) (Q:ℕ)
    (J κ:ℝ) (bill:0 ≤ J)(large:4 ≤ T₀)(small:κ ≤ 1/2)
    (low:∀i, ((F₀).grades i).2 ≤ Q →
       ‖cell R A (a₀) (p:=p) ca (show A.k < N by omega) A.k (choose (L₀) A.b A.k x) (Pi.single i 1) z-
           born R h (tested (L₀) A.b A.k x) z i‖*(T₀)^Q  ≤  J*(T₀)^((F₀).grades i).2*(T₀)^(-κ))
    (high:∀i, Q < ((F₀).grades i).2 →
       ‖cell R A (a₀) (p:=p) ca (show A.k < N by omega) A.k (choose (L₀) A.b A.k x) (Pi.single i 1) z-
           born R h (tested (L₀) A.b A.k x) z i‖ ≤ J)
    (off:∀i, ((F₀).grades i).2≠Q→born R h (tested (L₀) A.b A.k x) z i=0):
    signed R A B h da db (p:=p) cb top a W x z Q J κ:=by
  obtain ⟨v,lower,clean,_,heard⟩:=WilsonPhysicalStationCoincidentObserved.original R fac A B h e da db (p:=p)
     ca cb dates top horizon gate a weight x z Q J κ bill large small low high off
  have same:=WilsonPhysicalStationSelectedLower.unique R fac A h e da (p:=p) ca (by omega) (by omega)
    gate _ v W lower issued.lower clean issued.clear
  subst v
  exact heard

end YM.Integration.WilsonPhysicalStationCoincidentGrant
end


set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentGrant
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
open WilsonPhysicalStationCoincidentLower (Receipt)
open WilsonPhysicalStationCoincidentEntry (rent)
open WilsonPhysicalStationMeasuredCash (aperture)

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

include fac simple source in
theorem original (a b:(F₀).Index)(weight:((F₀).grades a).1=h)(s:Signed)(side:Fin 2)
    (dep u θ:ℕ)(coin z roof:ℝ)(active:100*(h+1) ≤ dep)(shelf:100*(h+1) ≤ θ)
    (two:2 ≤ u)(wide:(dep:ℝ)+6 ≤ roof)(tax:∀i ≤ dep,generator G i ≤ z)(horizon:h=e+1)
:
    ∀ᶠ m:ℕ in atTop,∀P:Tapes.Panel dep,P.θ=θ→P.currency=coin→P.arc ≤ roof→
      ∀ (A:Vane (C) D)(B:Vane (C) D'),A.k=m→B.k=A.k→
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
  exact mounted R fac A B h e da db (p:=p) ca cb dates top horizon
    gate a weight U issued ξ (probe (C) b s side) (rank (C) h b) _ _ positive large small
    (fun i hi=>(menu i).1 hi) (fun i hi=>(menu i).2 hi) (fun i off=>WilsonMeasuredPublicEntranceThermalRankPair.original R.family i b s side _ off)

end YM.Integration.WilsonPhysicalStationCoincidentGrant
end
