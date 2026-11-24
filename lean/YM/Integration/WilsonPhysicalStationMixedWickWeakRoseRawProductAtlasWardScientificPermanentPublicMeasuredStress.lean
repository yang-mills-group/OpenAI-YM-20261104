import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredMarks
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicGramAccount
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredStress
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


open scoped Matrix


open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
theorem reference {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))
    (P:I→Survey C)(v:(Bel C.book).Field 4):
    (fun i j=>free (P i) (B j)) *ᵥ (fun j=>B.repr v j)=(fun i=>free (P i) v):=by
  funext i
  have word:=congrArg (free (P i)) (B.sum_repr v)
  simp only [map_sum,map_smul,smul_eq_mul] at word
  change (∑j,free (P i) (B j)*B.repr v j)=_
  calc
    _=∑j,B.repr v j*free (P i) (B j):=by apply Finset.sum_congr rfl;intro j _;ring
    _=free (P i) v:=word

theorem original {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))
    (P:I→Survey C)(dual:IsUnit (Matrix.det (fun i j=>free (P i) (B j))))
    (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)(a b:Axis):
    Tendsto (fun k:ℕ=>fun j=>B.repr (born F X k a b) j) atTop
      (𝓝 (fun j=>B.repr (Pert.freeStress C.labels a b) j)) ∧
    ∃V:ℝ,0<V ∧ ∀ᶠ k in atTop,(∑j,‖B.repr (born F X k a b) j‖)≤V:=by
  let A:Matrix I I ℂ:=fun i j=>free (P i) (B j)
  let Ak:ℕ→Matrix I I ℂ:=fun k i j=>mean (P i) X k (B j)
  let y:ℕ→I→ℂ:=fun k i=>raw (P i) X k (physical F X k a b)
  let c:I→ℂ:=fun j=>B.repr (Pert.freeStress C.labels a b) j
  have gram:Tendsto Ak atTop (𝓝 A):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have paid:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredMarks.unmarked F X first (dims (P i)) (seats (P i) (B j)) (P i).spot (P i).separate
    simpa only [reader,freeRead] using paid
  have stress:Tendsto y atTop (𝓝 (A *ᵥ c)):=by
    change Tendsto y atTop (𝓝 ((fun i j=>free (P i) (B j)) *ᵥ (fun j=>B.repr (Pert.freeStress C.labels a b) j)))
    rw [reference]
    apply tendsto_pi_nhds.mpr
    intro i
    have paid:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredMarks.original F X first (tickets (P i) 0) (fun i=>decide (i=0)) (fun _=>(a,b)) (P i).spot (P i).separate
    simpa only [WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.observed,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.underlying] using paid
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicGramAccount.original A c Ak y (fun k j=>B.repr (born F X k a b) j) dual gram stress
    (Eventually.of_forall fun k=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.original B P F X k a b)

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredStress
end
