import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
theorem unmarked (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    {n:ℕ}(d:Caps n)(v:MaxwellSlots C d)(j:ℕ){K:Set (Points n)}
    (compact:IsCompact K)(inside:K⊆conf n):
    TendstoUniformlyOn (fun k:ℕ=>iteratedFDeriv ℝ j (measured F none (X.U k) v (X.r k)))
      (iteratedFDeriv ℝ j (WickGoal v)) atTop K:=by
  let q:Pert.Slots n→(Maxwell.freeTable C.labels).Tag:=fun i=>⟨d i,v i⟩
  let ab:Pert.Slots n→Axis×Axis:=fun _=>(0,0)
  have physical (k:ℕ): (fun z=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q (fun _=>false) ab) (X.r k • z))=
      measured F none (X.U k) v (X.r k):=by
    rfl
  have free: Ward.disc (Pert.freeWithStress C.labels q (fun _=>false) ab)=WickGoal v:=by
    rfl
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε pos
  have bound:=first.jets n j q (fun _=>false) ab compact inside (half_pos pos)
  filter_upwards [bound] with k paid x hx
  have close:=paid x hx
  rw [physical,free] at close
  rw [dist_comm,dist_eq_norm]
  exact lt_of_le_of_lt close (half_lt_self pos)

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)(J:ℝ→PhysMS.tower S)
    (grant:Leading F J):
    (∀k:ℕ,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.splice X J (X.r k)=X.U k) ∧ Leading F (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.splice X J):=by
  refine ⟨WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.selected X J,?_⟩
  constructor
  · intro d
    exact (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.original X J (fun _ U=>Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (U d)) (grant.equivariant d) (first.fit.hsym d)).2
  · intro d e h
    exact (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.original X J (fun _ U=>∀v,U e ((Maxwell.Free.scheme C.labels).rise h v)=F.sector.derivatives.rise h (U d v)) (grant.raised h) (first.fit.rises d e h)).2
  · intro d
    exact (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.original X J (fun _ U=>U d ((Bel C.book).unit d)=S.unit d) (grant.unit d) (first.fit.units d)).2
  · intro n d v j K compact inside
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε pos
    have whole:=Metric.tendstoUniformlyOn_iff.mp (grant.lead n d v j K compact inside) ε pos
    have observed:=Metric.tendstoUniformlyOn_iff.mp (unmarked F X first d v j compact inside) ε pos
    exact (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.original X J (fun s U=>∀x∈K,dist (iteratedFDeriv ℝ j (WickGoal v) x)
      (iteratedFDeriv ℝ j (measured F none U v s) x)<ε) whole observed).2

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading
end
