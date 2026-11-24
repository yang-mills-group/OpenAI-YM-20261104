import YM.Integration.WilsonPhysicalStationMixedMeasuredTicket
import YM.Integration.WilsonPhysicalStationMixedDualCash
import YM.Integration.WilsonMovingForkReporterMixedHouses
/-! Spend the genuine common booked mixed panel on one signed, thermally weighted physical
right functional. All its components use one subtracted field chosen before this functional. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedSchurBoard
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D D' h e depth:ℕ}(A:Vane R.family D)(B:Vane R.family D')
    (da:h<D+1)(db:h<D'+1)(ca:A.checked f H D)(cb:B.checked f H D')
    {I:Type*}[Fintype I](v:I→Slot R.family)(dr:∀i,(v i).right<D+1)
local notation "C₀"=>R.family
local notation "AX"=>R.family.path.levels
local notation "F₀"=>R.family.labels.level h
local notation "t₀"=>(AX).clock.monitor A.k
local notation "M₀"=>Station.mag (AX) A.b A.k
local notation "M₁"=>Station.mag (AX) B.b B.k
local notation "d₁"=>(⟨h,db⟩:Fin (D'+1))
local notation "d₂" i=>(⟨(v i).right,dr i⟩:Fin (D+1))
local notation "z₂" i=>probe R.family (v i).dual (v i).turn (v i).arm
local notation "q₂" i=>rank R.family (v i).right (v i).dual

def onLeft {C:Family G}(h:ℕ)(s:Slot C):Slot C:={s with left:=h}
def referenceRow (i:I)(x:Points 2)(a:(F₀).Index):ℂ:=base R h (z₂ i) (tested AX A.b A.k x) a
def charge (i:I)(depth q:ℕ)(x:Points 2):ℝ:=wage R q (q₂ i) (rate R (onLeft h (v i)) depth)
  (∑a,‖referenceRow R A v (h:=h) i x a‖) A.k h
def registered (N p:ℕ)(y:R.family.label h)(i:I)(x:Points 2):ℂ:=
  WilsonPhysicalStationMixedListener.value R N p A.k (choose AX A.b A.k x) y (A.wheel.atCut (N,p) (d₂ i) (z₂ i))

def Billed (e depth:ℕ):Prop:=
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k<N,∀a:(F₀).Index,∀w:R.family.label h,
    (if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h e da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h e da db (p:=p) ca cb top a w)→
    ∀x:I→Points 2,(∀i,tested AX A.b A.k (x i)∈(v i).site)→(∀i,FitSky AX A.b A.k (x i))→
    ∀Q:ℕ,∀c:I→ℂ,∀roof:I→ℝ,(∀i,0≤roof i)→(∀i,‖c i‖*(t₀)^Q≤roof i*(t₀)^(q₂ i))→
      let q:=rank R.family h a
      let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
      let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
      ‖(∑i,c i*registered R A v dr N p Z i (x i))-χ*∑i,c i*referenceRow R A v (h:=h) i (x i) a‖*(t₀)^Q
        ≤(∑i,roof i*charge R A v (h:=h) i depth q (x i))*(t₀)^q

theorem original (heard:∀i,Reads R A B (onLeft h (v i)) da db (dr i) ca cb e depth):
    Billed R A B da db ca cb v dr e depth:=by
  classical
  filter_upwards [Filter.eventually_all.mpr heard] with N read
  intro p top a w stamped x location fit Q c roof rp paid q Z χ
  exact WilsonPhysicalStationMixedDualCash.signed q Q (fun i=>q₂ i) (Real.exp_pos _).le c
    (fun i=>registered R A v dr N p Z i (x i)) (fun i=>referenceRow R A v i (x i) a) χ roof
    (fun i=>charge R A v (h:=h) i depth q (x i)) rp paid
    (fun i=>read i p top a w stamped (x i) (location i) (fit i))

theorem purchased (bind:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)(price:ℕ→ℝ)(qty:ℕ→ℕ)
    (menu:∀D,Fin (qty D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O J H price qty menu P A)
    (pick:I→Fin (qty depth))(record:∀i,menu depth (pick i)=onLeft h (v i))
    (admitted:∀i,100*(max h (v i).right+1)≤depth)
    (dates:B.k=A.k ∨ B.k=A.k+1)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k h (M₀) (M₁)≤1):
    Billed R A B da db ca cb v dr e depth:=by
  obtain ⟨_,ink,ripe,coverage⟩:=house
  apply original
  intro i
  apply WilsonPhysicalStationMixedMeasuredTicket.funded R A B (onLeft h (v i)) da db (dr i) ca cb
    bind O J P ink ripe _ dates warm window
  have visit:=coverage (pick i)
  rw [record i] at visit
  exact visit (admitted i)

end YM.Integration.WilsonPhysicalStationMixedSchurBoard
end
