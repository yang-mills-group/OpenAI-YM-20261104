import YM.Integration.WilsonPhysicalStationObservedEntry
import YM.Integration.WilsonPhysicalStationResidualWallet
import YM.Integration.WilsonPhysicalStationDetectorCurrency

/-! A compact ceiling on the original free reflected rows, uniform before both Wilson regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationWickCeiling
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

open WilsonPhysicalStationObservedEntry (born)
variable {G:Gauge}(R:Run G)(h:ℕ)(z:(standard R.family).Field h)
theorem smooth (a:(R.family.labels.level h).Index):
    ContinuousOn (fun x:Points 2=>born R h x z a) (conf 2):=by
  let d:Caps 2:=fun _=>h
  let row:∀j:Fin 2,(standard R.family).Field (d j):=![(standard R.family).project h (Pi.single a 1),z]
  let v:=fun j=>(standard R.family).representative (d j) (row j)
  change ContinuousOn (fun x=>(standard R.family).value d x v) (conf 2)
  exact ((Maxwell.table_smooth R.family.labels).on_conf d v).continuousOn

theorem original (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2):
    ∃ C:ℝ,0 ≤ C ∧ ∀x∈K,∑a:(R.family.labels.level h).Index,‖born R h x z a‖ ≤ C:=by
  classical
  have bounded (i:(R.family.labels.level h).Index):∃ u:ℝ,∀x∈K,‖born R h x z i‖ ≤ u:=by
    obtain ⟨u,cap⟩:=compact.bddAbove_image ((smooth R h z i).norm.mono clear)
    exact ⟨u,fun x hx=>cap ⟨x,hx,rfl⟩⟩
  choose u cap using bounded
  refine ⟨∑a,|u a|,Finset.sum_nonneg (fun _ _=>abs_nonneg _),?_⟩
  exact fun x hx=>Finset.sum_le_sum (fun i _=>(cap i x hx).trans (le_abs_self _))
end YM.Integration.WilsonPhysicalStationWickCeiling
end
