import YM.Integration.WilsonPhysicalStationMixedNamedAmounts
import YM.Integration.WilsonPhysicalStationMixedSchurBoard
/-! The genuine named lower Wilson panel retains each source's own thermal leg count. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedSchurNamed
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
def slot (h:ℕ)(b:(F₁).Index):Slot R.family:=⟨h,e,b,1,0,K,compact,sep⟩
def arms (h:ℕ)(t:I₀×(F₁).Index):Slot R.family:=slot R e K compact sep h t.2

def Return (low depth:ℕ):Prop:=
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k<N,∀a:(F₀).Index,∀w:R.family.label h,
    (if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h low da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h low da db (p:=p) ca cb top a w)→
    ∀x:I₀→Points 2,(∀i,tested AX A.b A.k (x i)∈K)→(∀i,FitSky AX A.b A.k (x i))→
    ∀Q:ℕ,∀c:I₀→ℂ,∀roof:I₀→ℝ,(∀i,0≤roof i)→(∀i,‖c i‖*(t₀)^Q≤roof i*(t₀)^i.2.1.val)→
      let q:=rank R.family h a
      let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
      let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
      ‖(∑i,c i*WilsonPhysicalStationMixedListener.value R N p A.k (choose AX A.b A.k (x i)) Z
          (A.wheel.atCut (N,p) (d₂) (named R book e i)))-
        χ*∑i,c i*base R h (named R book e i) (tested AX A.b A.k (x i)) a‖*(t₀)^Q ≤
      (∑t:I₀×(F₁).Index,(roof t.1*‖coefficient R book e t.1 t.2‖)*
        charge R A (arms R book e K compact sep h) (h:=h) t depth q (x t.1))*(t₀)^q

theorem original (fund:WilsonPhysicalStationMixedSchurBoard.Billed R A B da db ca cb
    (arms R book e K compact sep h) (fun _=>dr) low depth):
    Return R A B da db ca cb book e dr K compact sep low depth:=by
  classical
  filter_upwards [fund] with N paid
  intro p top a w stamped x inside fit Q c roof rp earned q Z χ
  have spend:=paid p top a w stamped (fun t=>x t.1) (fun t=>inside t.1) (fun t=>fit t.1) Q
    (fun t=>c t.1*coefficient R book e t.1 t.2) (fun t=>roof t.1*‖coefficient R book e t.1 t.2‖)
    (fun t=>mul_nonneg (rp _) (norm_nonneg _))
    (fun t=>WilsonPhysicalStationMixedNamedProbe.restored R book e Q c roof earned t.1 t.2)
  rw [WilsonPhysicalStationMixedNamedAmounts.registered R book e A dr N p A.k (fun i=>choose AX A.b A.k (x i)) Z c,
      WilsonPhysicalStationMixedNamedAmounts.wick R book e (fun i=>tested AX A.b A.k (x i)) a c]
  exact spend

theorem purchased (bind:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)(price:ℕ→ℝ)(qty:ℕ→ℕ)
    (menu:∀D,Fin (qty D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O J H price qty menu P A)
    (pick:(F₁).Index→Fin (qty depth))(record:∀b,menu depth (pick b)=slot R e K compact sep h b)
    (admitted:100*(max h e+1)≤depth)
    (dates:B.k=A.k ∨ B.k=A.k+1)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k h (M₀) (M₁)≤1):
    Return R A B da db ca cb book e dr K compact sep low depth:=by
  apply original
  exact WilsonPhysicalStationMixedSchurBoard.purchased R A B da db ca cb _ (fun _=>dr)
    bind O J price qty menu P house (fun t=>pick t.2) (fun t=>record t.2) (fun _=>admitted) dates warm window

end YM.Integration.WilsonPhysicalStationMixedSchurNamed
end
