import YM.Integration.WilsonMovingForkReporterRankCourse
import YM.Integration.WilsonPhysicalStationThermalFiledPair

/-! Observe the genuinely issued raw basis and physically projected second field on one selected Wilson table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterPostedRanks
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

open WilsonMovingForkReporterFixedRanks (Axes test)
open WilsonMovingForkReporterRankCourse (reached surplus)
open WilsonPhysicalStationThermalRanks (probe)
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D:ℕ} (V:Vane R.family h)
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels

def paid (A:Axes R.family) (small:A.weight≤h) (checked:V.checked f S h) (D:ℕ) : Prop :=
  let d:Fin (h+1) := ⟨A.weight,by omega⟩
  let output:=probe C A.dual A.turn A.arm
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:V.k<N,∀ x:Points 2,
    tested AX V.b V.k x∈A.site → FitSky AX V.b V.k x →
      ((D:ℝ)+1)*((AX).clock.monitor V.k)^(((test A).rank 1-(test A).rank 0:ℕ):ℝ) *
        ‖cell R V d (p:=p) checked fine V.k (choose AX V.b V.k x) (Pi.single A.raw 1) output -
          (standard C).classMoment (standard C) (fun _:Fin 2=>d.val) (tested AX V.b V.k x)
             ![(standard C).project d (Pi.single A.raw 1),output]‖ ≤ WilsonMovingForkReporterRankMarket.amount (test A)

theorem original (A:Axes R.family) (small:A.weight≤h) (checked:V.checked f S h)
    (P:Tapes.Panel D) {z:ℝ} (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V (MergeProof.East.trays D) z)
    (bought:reached R B R.makes O J A P V.k z) (ripe:(D:ℝ)+1≤((AX).clock.monitor V.k)^(surplus D)) :
    paid R V A small checked D := by
  let d:Fin (h+1):=⟨A.weight,by omega⟩
  let output:=probe C A.dual A.turn A.arm
  have income:=WilsonPhysicalStationThermalFiledPair.original R B O J V d checked (K:=A.site) P
    (Pi.single A.raw 1) output (test A).rank ink bought
  filter_upwards [income] with N heard p fine x loc fit
  have price:=heard p fine x loc fit
  rw [Real.rpow_add (show 0<(AX).clock.monitor V.k from Real.exp_pos _)] at price
  calc _ ≤ ((AX).clock.monitor V.k)^(surplus D) * ((AX).clock.monitor V.k)^(((test A).rank 1-(test A).rank 0:ℕ):ℝ) * _ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ripe (Real.rpow_nonneg (Real.exp_pos _).le _)) (norm_nonneg _)
    _ ≤ _ := by rwa [mul_comm (((AX).clock.monitor V.k)^(surplus D))]

end YM.Integration.WilsonMovingForkReporterPostedRanks
end
