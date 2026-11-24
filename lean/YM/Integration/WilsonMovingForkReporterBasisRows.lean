import YM.Integration.WilsonMovingForkReporterBasisTariff
import YM.Integration.WilsonMovingForkReporterPostedRanks

/-! Read the complete original row, including inputs above the detector rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBasisRows
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



open WilsonPhysicalStationThermalBasisOffice (rank low plain)

def fare (A:Axes C) (a:(R.family.labels.level A.weight).Index) : ℝ :=
  if rank C A.weight a≤rank C A.weight A.dual then
    low C A.weight A.site A.compact A.separated A.dual A.turn A.arm a
  else plain C A.weight A.site A.compact A.separated A.dual A.turn A.arm a

def Sold (A:Axes C) (hs:A.weight≤h) (D:ℕ) (check:V.checked f S h) : Prop :=
  let d:Fin (h+1):=⟨A.weight,by omega⟩
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:V.k<N,∀x:Points 2,tested AX V.b V.k x∈A.site→FitSky AX V.b V.k x→
    ∀a:(R.family.labels.level A.weight).Index,
      ((D:ℝ)+1)*(AX).clock.monitor V.k^((rank C A.weight A.dual-rank C A.weight a:ℕ):ℝ)*
        ‖cell R V d (p:=p) check fine V.k (choose AX V.b V.k x) (Pi.single a 1) (probe C A.dual A.turn A.arm) -
          (standard C).classMoment (standard C) (fun _:Fin 2=>A.weight) (tested AX V.b V.k x)
          ![(standard C).project d (Pi.single a 1),probe C A.dual A.turn A.arm]‖ ≤ fare R A a

theorem original (P:Tapes.Panel D) (A:Axes C) (hs:A.weight≤h) (check:V.checked f S h) {z:ℝ}
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V (MergeProof.East.trays D) z)
    (ripe:(D:ℝ)+1 ≤ (AX).clock.monitor V.k^(surplus D))
    (rows:WilsonMovingForkReporterBasisTariff.Booked R B R.makes O J A P V.k z) : Sold R V A hs D check := by
  let d:Fin (h+1):=⟨A.weight,by omega⟩
  let q (a:(R.family.labels.level A.weight).Index) : Fin 2→ℕ :=
    if rank C A.weight a≤rank C A.weight A.dual then ![rank C A.weight a,rank C A.weight A.dual] else fun _=>0
  have bought (a:(R.family.labels.level A.weight).Index) :
      WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=MergeProof.East.trays D) (K:=A.site)
        (votes R d (Pi.single a 1) (probe C A.dual A.turn A.arm)) P (q a) V.k (fare R A a) z := by
    by_cases ok:rank C A.weight a≤rank C A.weight A.dual
    · simpa only [q,fare,if_pos ok,WilsonPhysicalStationThermalBasisOffice.requested,WilsonPhysicalStationThermalRanks.fields,votes,d] using (rows a).1 ok
    · simpa only [q,fare,if_neg ok,WilsonPhysicalStationThermalBasisOffice.requested,WilsonPhysicalStationThermalRanks.fields,votes,d] using (rows a).2
  have deg (a:(R.family.labels.level A.weight).Index) :
      q a 1-q a 0=rank C A.weight A.dual-rank C A.weight a := by
    by_cases ok:rank C A.weight a≤rank C A.weight A.dual
    · simp only [q,if_pos ok];rfl
    · simp [q,ok,Nat.sub_eq_zero_of_le (Nat.lt_of_not_ge ok).le]
  have heard:=Filter.eventually_all.mpr (fun a=>WilsonPhysicalStationThermalFiledPair.original R B O J V d check P
    (Pi.single a 1) (probe C A.dual A.turn A.arm) (q a) ink (bought a))
  filter_upwards [heard] with N port p fine x loc fit a
  have price:=port a p fine x loc fit
  rw [deg a,Real.rpow_add (show 0<(AX).clock.monitor V.k from Real.exp_pos _)] at price
  calc _ ≤ ((AX).clock.monitor V.k)^(surplus D)*((AX).clock.monitor V.k)^((rank C A.weight A.dual-rank C A.weight a:ℕ):ℝ)*_ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ripe (Real.rpow_nonneg (Real.exp_pos _).le _)) (norm_nonneg _)
    _ ≤ _ := by rwa [mul_comm (((AX).clock.monitor V.k)^(surplus D))]

end YM.Integration.WilsonMovingForkReporterBasisRows
end
