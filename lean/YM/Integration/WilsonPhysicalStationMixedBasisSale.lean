import YM.Integration.WilsonMovingForkReporterMixedBasis
import YM.Integration.WilsonPhysicalStationMixedBilledPort
import YM.Integration.WilsonPhysicalStationBasisIncome
/-! A purchase on the very mixed original panel at either station keeps every prior raw
coordinate, its native curvature count and the one physical graded probe on the right. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedBasisSale
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
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
  {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D:ℕ}(V:Vane R.family h)
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels

def fee (A:Slot C)(a:(R.family.labels.level A.left).Index):ℝ:=
  if ok:ordered A a then amount (ranked A a ok) else flat A a

def Sold (A:Slot C)(hl:A.left<h+1)(hr:A.right<h+1)(D:ℕ)(checked:V.checked f S h):Prop:=
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:V.k<N,∀x:Points 2,tested AX V.b V.k x∈A.site→FitSky AX V.b V.k x→
    ∀a:(R.family.labels.level A.left).Index,
      ((D:ℝ)+1)*(AX).clock.monitor V.k^((rank C A.right A.dual-rank C A.left a:ℕ):ℝ)*
        ‖cell R V ⟨A.left,hl⟩ ⟨A.right,hr⟩ (p:=p) checked fine V.k (choose AX V.b V.k x) (Pi.single a 1)
          (probe C A.dual A.turn A.arm) - reference C (Pi.single a (1:ℂ)) (probe C A.dual A.turn A.arm)
            (tested AX V.b V.k x)‖≤fee R A a

theorem original (A:Slot C)(hl:A.left<h+1)(hr:A.right<h+1)(checked:V.checked f S h)
    (P:Tapes.Panel D){z:ℝ}(ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V (MergeProof.East.trays D) z)
    (ripe:(D:ℝ)+1 ≤(AX).clock.monitor V.k^(surplus D))(posted:Posted B R.makes O J A P V.k z):
    Sold R V A hl hr D checked:=by
  let dl:Fin (h+1):=⟨A.left,hl⟩
  let dr:Fin (h+1):=⟨A.right,hr⟩
  let q (a:(R.family.labels.level A.left).Index):Fin 2→ℕ:=
    if ordered A a then ![rank C A.left a,rank C A.right A.dual] else fun _=>0
  have bought (a:(R.family.labels.level A.left).Index):
      WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=MergeProof.East.trays D) (K:=A.site)
        (d:=grades dl dr) (votes C (Pi.single a 1) (probe C A.dual A.turn A.arm)) P (q a) V.k (fee R A a) z:=by
    by_cases ok:ordered A a
    · simp only [q,if_pos ok,fee,dif_pos ok]
      exact (posted a).1 ok
    · simp only [q,if_neg ok,fee,dif_neg ok]
      exact (posted a).2
  have deg (a:(R.family.labels.level A.left).Index):
      q a 1-q a 0=rank C A.right A.dual-rank C A.left a:=by
    by_cases ok:ordered A a
    · simp only [q,if_pos ok];rfl
    · have bad:rank C A.right A.dual<rank C A.left a:=lt_of_not_ge ok
      simp [q,ok,Nat.sub_eq_zero_of_le bad.le]
  have heard:=Filter.eventually_all.mpr (fun a=>WilsonPhysicalStationMixedWickPair.original R B O J V dl dr checked P
    (Pi.single a 1) (probe C A.dual A.turn A.arm) (q a) ink (bought a))
  filter_upwards [heard] with N port p fine x loc fit a
  have price:=port a p fine x loc fit
  rw [deg a,Real.rpow_add (show 0<(AX).clock.monitor V.k from Real.exp_pos _)] at price
  calc _≤((AX).clock.monitor V.k)^(surplus D)*((AX).clock.monitor V.k)^((rank C A.right A.dual-rank C A.left a:ℕ):ℝ)*_ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ripe (Real.rpow_nonneg (Real.exp_pos _).le _)) (norm_nonneg _)
       _≤_:=by rwa [mul_comm (((AX).clock.monitor V.k)^(surplus D))]

end YM.Integration.WilsonPhysicalStationMixedBasisSale
end
