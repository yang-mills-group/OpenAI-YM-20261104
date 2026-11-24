import YM.Integration.WilsonMovingForkReporterRankCourse
import YM.Integration.WilsonPhysicalStationThermalBasisOffice

/-! Every original raw input for each of the selected finite reflected detectors. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBasisTariff
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
open WilsonPhysicalPositionWeakRoofSchedule WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterHeatedCourse (fits ceiling)
open WilsonMovingForkReporterRankMarket (amount)
variable (R : Run G) (B : Binding R.family) (H : R.family.Makes) (O : HaarBudget G) (J : ChartRatio G)
variable {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
  {L : ∀ N p m : ℕ, m < N → GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
variable {F : Extraction.Order} {S : Table R.family.book} (U : Final R.family F S)
  (a : (Cells.standard R.family).Hierarchy)
variable (simple : G.Simple) (fund : Scrim R.family W u ψ φ δ (fly R.family.path.levels) r L)

open WilsonPhysicalPositionWeakRoofCourse (earned)


open WilsonPhysicalStationThermalBasisOffice (rank requested low plain)

def Booked {D:ℕ} (A:Axes R.family) (P:Tapes.Panel D) (k:ℕ) (z:ℝ) : Prop :=
  ∀a:(R.family.labels.level A.weight).Index,
      (rank R.family A.weight a≤rank R.family A.weight A.dual→WilsonReporterWeightedRankEpoch.Result B H O J (u:=MergeProof.East.trays D) (K:=A.site)
          (requested R.family A.weight A.dual A.turn A.arm a) P ![rank R.family A.weight a,rank R.family A.weight A.dual] k (low R.family A.weight A.site A.compact A.separated A.dual A.turn A.arm a) z) ∧
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=MergeProof.East.trays D) (K:=A.site)
          (requested R.family A.weight A.dual A.turn A.arm a) P (fun _=>0) k (plain R.family A.weight A.site A.compact A.separated A.dual A.turn A.arm a) z

include simple fund in
theorem original (d:ℕ) {n:ℕ} (roster:Fin n→Axes R.family) (z upper:ℝ)
    (wide:(d:ℝ)+6≤upper) (band:∀i,i≤d → generator G i≤z) (P:ℝ→Fin 3→Tapes.Panel d) :
    ∃ k₀:ℕ,∀k≥k₀, ∀j:Fin 3,∀s:Fin n,100*((roster s).weight+1)≤d → ∀pan:Tapes.Panel d,
        pan.θ=(P 0 j).θ → pan.currency=(P 0 j).currency → pan.arc≤upper →
          Booked R B H O J (roster s) pan k z := by
  classical
  let Seats:={s:Fin n // 100*((roster s).weight+1)≤d}
  have funds (j:Fin 3) (s:Seats) :
      ∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel d,pan.θ=(P 0 j).θ → pan.currency=(P 0 j).currency →
        pan.arc≤upper → Booked R B H O J (roster s.1) pan k z := by
    exact WilsonPhysicalStationThermalBasisOffice.original R.family (roster s.1).weight (roster s.1).site
      (roster s.1).compact (roster s.1).separated B H simple fund O J (roster s.1).dual (roster s.1).turn
      (roster s.1).arm d (MergeProof.East.trays d) (P 0 j).θ (P 0 j).currency z upper s.2
      (s.2.trans (P 0 j).enough) (Nat.le_add_left ..) wide band
  obtain ⟨k₀,gate⟩:=eventually_atTop.mp (eventually_all.mpr (fun j=>eventually_all.mpr (funds j)))
  exact ⟨k₀,fun k hk j s hs=>gate k hk j ⟨s,hs⟩⟩

end YM.Integration.WilsonMovingForkReporterBasisTariff
end
