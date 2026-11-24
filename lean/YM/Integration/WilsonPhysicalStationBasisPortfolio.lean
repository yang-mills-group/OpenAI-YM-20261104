import YM.Integration.WilsonPhysicalStationBasisWindow
import YM.Integration.WilsonPhysicalStationFullVote
/-! Signed sums of the physical, lower-subtracted recorded earnings on one original two-post arrangement. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisPortfolio
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

open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterBasisRows (Sold)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationBasisIncome (price)
open Next.Rank.Configuration Next.Rank.Atlas
open WilsonPhysicalStationFullVote (Head principal)
open WilsonPhysicalStationBasisRoof (amount)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
variable {G:Gauge} (R:Run G)
def column {h:ℕ}(a:Head R.family h)(b:(R.family.labels.level h).Index)(s:Signed)(v:Fin 2)
    (legal:rank R.family h a.val ≤ rank R.family h b)(K:Set (Points 2))(compact:IsCompact K)(separated:K ⊆ conf 2):
    Axes R.family:=⟨h,a.val,b,s,v,legal,K,compact,separated⟩

variable {T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
  (fac:Facilities R.family f S){H:(Bel R.family.book).Hierarchy}{D D' step:ℕ}
  {h e:ℕ}(da:h < D+1)(db:h < D'+1)(A:Vane R.family D)(B:Vane R.family D')
  {I:Type*}[Fintype I](a:I→Head R.family h)(b:(R.family.labels.level h).Index)(s:Signed)(v:Fin 2)
  (eligible:∀i,rank R.family h (a i).val ≤ rank R.family h b)(K:Set (Points 2))(compact:IsCompact K)(separated:K ⊆ conf 2)
local notation "X" => fun i=>column R (a i) b s v (eligible i) K compact separated
local notation "z₀" => probe R.family b s v
local notation "M₀" => Station.mag R.family.path.levels A.b A.k
local notation "M₁" => Station.mag R.family.path.levels B.b B.k

include L fac in
theorem original (hg:G.Simple)(ca:A.checked f H D)(cb:B.checked f H D')(dates:B.k=A.k ∨ B.k=A.k+1)
    (horizon:h=e+1)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k h (M₀) (M₁) ≤ 1)(sold:∀i,Sold R A ((X) i) (by dsimp [column];omega) step ca)
    (w:Head R.family h→(ℕ×ℕ)→R.family.label h):
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k < N,
    (∀i,WilsonPhysicalStationBasisWindow.Filed R ((X) i) da db A B (e:=e) (p:=p) ca cb top (w (a i) (N,p)))→
    ∀ξ:Points 2,tested R.family.path.levels A.b A.k ξ∈K→FitSky R.family.path.levels A.b A.k ξ→∀ μ:I→ℂ,
      let o:=Station.choose R.family.path.levels A.b A.k ξ
      let z:=A.wheel.atCut (N,p) ⟨h,da⟩ z₀
      let Γ:=born R h (tested R.family.path.levels A.b A.k ξ) z₀
      let χ (i:I):ℂ:=signal R N p A.k B.k h (rank R.family h (a i).val) (M₀) (M₁)
      ‖(∑i,μ i*principal R B db (per:=p) cb top w A.k o z (a i))-
        ∑i,μ i*(χ i*Γ (a i).val)‖ ≤ ∑i,‖μ i‖*amount R ((X) i) step A.k:=by
  have seen:=fun i=>WilsonPhysicalStationBasisWindow.original R L fac ((X) i) da db A B hg ca cb dates
    horizon (a i).property warm window (sold i)
  filter_upwards [eventually_all.mpr seen] with N ear
  intro p top posted ξ inside fit μ o z Γ χ
  let Y (i:I):=principal R B db (per:=p) cb top w A.k o z (a i)
  have paid (i:I):‖Y i-χ i*Γ (a i).val‖ ≤ amount R ((X) i) step A.k:=
    ear i p top (w (a i) (N,p)) (posted i) ξ inside fit
  change ‖(∑i,μ i*Y i)-(∑i,μ i*(χ i*Γ (a i).val))‖ ≤ _
  rw [←Finset.sum_sub_distrib]
  simp only [←mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum; intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (paid i) (norm_nonneg _)

end YM.Integration.WilsonPhysicalStationBasisPortfolio
end
