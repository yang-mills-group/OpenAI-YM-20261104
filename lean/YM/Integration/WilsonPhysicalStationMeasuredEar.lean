import YM.Integration.WilsonPhysicalStationSelectedLower
import YM.Integration.WilsonPhysicalStationObservedEntry
import YM.Integration.WilsonPhysicalStationResidualWallet
import YM.Integration.WilsonPhysicalStationDetectorCurrency

/-! A common original lower subtraction can be heard by every actual signed detector. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMeasuredEar
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
open WilsonPhysicalStationSelectedLower (Receipt)
local notation "T₀" => (L₀).clock.monitor A.k

def signed (cb:B.checked f H D') (top:B.k < N) (a:(F₀).Index) (W:R.family.label h)
    (x:Points 2)(z:(standard R.family).Field h)(Q:ℕ)(J κ:ℝ):Prop:=
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let q:=((F₀).grades a).2
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    let Γ:=born R h (tested (L₀) A.b A.k x) z
    let ρ:=rate R A.k B.k h
    (1-err R B.k)*‖WilsonPhysicalStationTableJump.pair R (a₀) N p A.k (choose (L₀) A.b A.k x) (y-(K₀).terminal W)
        (A.wheel.atCut (N,p) (a₀) z)-χ*Γ a‖*(t₀)^Q ≤
        purse R N p A.k B.k h q (M₀) (M₁)*
          (J*4^Q*(T₀)^(-κ)*((ratio R A.k)^q+Fintype.card (F₀).Index*ρ)+ρ*∑ i,‖Γ i‖)

include L fac in
theorem original (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (top:B.k < N) (horizon:h=e+1)
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
  obtain ⟨v,lower,clean,_,heard⟩:=WilsonPhysicalStationObservedEntry.original R L fac A B h e da db (p:=p)
     hg ca cb dates top horizon gate a weight x z Q J κ bill large small low high off
  have same:=WilsonPhysicalStationSelectedLower.unique R fac A h e da (p:=p) ca (by omega) (by omega)
    gate _ v W lower issued.lower clean issued.clear
  subst v
  exact heard

end YM.Integration.WilsonPhysicalStationMeasuredEar
end
