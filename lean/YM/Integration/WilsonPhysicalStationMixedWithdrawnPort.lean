import YM.Integration.WilsonPhysicalStationMixedEarnedSchur
import YM.Integration.WilsonPhysicalStationGradedLowerPanel
import YM.Integration.WilsonPhysicalStationMixedSchurBoard
/-! The genuine named lower Wilson panel retains each source's own thermal leg count. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWithdrawnPort
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
open WilsonPhysicalStationMixedEarnedSchur (Row)
open WilsonPhysicalStationMixedSchurBoard (referenceRow)
variable (v:Slot R.family)(dv:v.right<D+1)
local notation "q₁"=>rank R.family v.right v.dual
local notation "rail"=>(fun _ : Unit=>v)
local notation "ear₁"=>WilsonPhysicalStationMixedSchurBoard.registered R A rail (fun _=>dv)
local notation "free₁"=>referenceRow R A rail (h:=h)
local notation "wage₁"=>charge R A rail (h:=h)
def Read (low depth:ℕ)(c:I₀→ℂ)(roof:I₀→ℝ)(N:ℕ):Prop:=
  ∀p:ℕ,∀top:B.k<N,∀a:(F₀).Index,∀w:R.family.label h,
    (if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h low da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h low da db (p:=p) ca cb top a w)→
    ∀u:Points 2,tested AX A.b A.k u∈v.site→FitSky AX A.b A.k u→
    ∀x:I₀→Points 2,(∀i,tested AX A.b A.k (x i)∈K)→(∀i,FitSky AX A.b A.k (x i))→
      let q:=rank R.family h a
      let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
      let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
      ‖(ear₁ N p Z () u - ∑i,c i*WilsonPhysicalStationMixedListener.value R N p A.k (choose AX A.b A.k (x i)) Z
          (A.wheel.atCut (N,p) (d₂) (named R book e i)))-
        χ*(free₁ () u a - ∑i,c i*base R h (named R book e i) (tested AX A.b A.k (x i)) a)‖*(t₀)^(q₁) ≤
      (wage₁ () depth q u + ∑t:I₀×(F₁).Index,(roof t.1*‖coefficient R book e t.1 t.2‖)*
        charge R A (arms R book e K compact sep h) (h:=h) t depth q (x t.1))*(t₀)^q


private theorem subtract (z a w b χ:ℂ){t p c d:ℝ}(pos:0≤t)(hi:‖z-χ*a‖*t≤c*p)(lo:‖w-χ*b‖*t≤d*p):
    ‖(z-w)-χ*(a-b)‖*t≤(c+d)*p:=by
  rw [show (z-w)-χ*(a-b)=(z-χ*a)-(w-χ*b) by ring,add_mul]
  exact (mul_le_mul_of_nonneg_right (norm_sub_le _ _) pos).trans ((add_mul ..).trans_le (add_le_add hi lo))

theorem original (c:I₀→ℂ)(roof:I₀→ℝ)
    (upper:Reads R A B (onLeft h v) da db dv ca cb low depth)
    (lower:∀ᶠN:ℕ in atTop,Row R A B da db ca cb book e dr K compact sep low depth (q₁) c roof N):
    ∀ᶠN:ℕ in atTop,Read R A B da db ca cb book e dr K compact sep v dv low depth c roof N:=by
  filter_upwards [upper,lower] with N high earlier
  intro p top a w sold u located fits x inside fit q Z χ
  exact subtract _ _ _ _ χ (pow_nonneg (Real.exp_pos _).le _) (high p top a w sold u located fits)
    (earlier p top a w sold x inside fit)

end YM.Integration.WilsonPhysicalStationMixedWithdrawnPort
end
