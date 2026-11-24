import YM.OPE.Compatible.Maestro.Lanes
import YM.Integration.WilsonMatrixTicketLanesQuota
import YM.Integration.WilsonMatrixTicketLanesObservation

/-! The two physical quotient estimates of the compatible construction give
the logarithmic matrix ticket on any common ultrafilter of that construction. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanes
open Filter OPE
open scoped Topology

variable {G : Gauge} {C : Family G} {F : Extraction.Order}
  {S : Table C.book} {P : DiffPlan S}

/-- Choosing the common ultrafilter precedes the horizon, the field and the
UV level. The representative and its convergent constant sequence may depend
on the level, as permitted by the retained matrix ticket. -/
theorem on_ultrafilter (lanes : Lanes (F := F) P) (U : Ultrafilter (ℕ × ℕ))
    (below : (U : Filter (ℕ × ℕ)) ≤ F.fuse) :
    Log.MatrixTicket (C := C) S P (U : Filter (ℕ × ℕ)) := by
  constructor
  · intro d x
    obtain ⟨p, levels⟩ := lanes.toInward.allowed d x
    refine ⟨p, ?_⟩
    filter_upwards [levels] with k hk
    exact WilsonMatrixTicketLanesQuota.inlet U x (hk U U.neBot below)
  · intro d w L hw lower
    obtain ⟨p, levels⟩ := lanes.toOutward.paper d w hw L (fun e he _ v => lower e he v)
    refine ⟨p, ?_⟩
    filter_upwards [levels] with k hk
    intro u nonempty refines q x z charge converges
    exact WilsonMatrixTicketLanesQuota.outlet (C := C)
      (hk u nonempty (refines.trans below) q x z converges charge)

/-- A previously selected common comparison filter can be refined once before
requesting any of the inlet or outlet rows. -/
theorem under (lanes : Lanes (F := F) P) (f : Filter (ℕ × ℕ)) [f.NeBot]
    (below : f ≤ F.fuse) :
    ∃ U : Ultrafilter (ℕ × ℕ), (U : Filter (ℕ × ℕ)) ≤ f ∧
      Log.MatrixTicket (C := C) S P (U : Filter (ℕ × ℕ)) := by
  obtain ⟨U, refines⟩ := Ultrafilter.exists_le f
  exact ⟨U, refines, on_ultrafilter lanes U (refines.trans below)⟩

/-- On the original retained layout, the quota and its dual use the same
field projections, derivatives, observing filter and chart matrices. -/
theorem original (simple : G.Simple) {Z : Spec.Final C F S} (L : RG17.Layout Z)
    (lanes : Lanes (F := F) Z.sector.derivatives) :
    Log.MatrixTicket (C := C) S Z.sector.derivatives L.lens := by
  letI := L.notbot
  obtain ⟨U, refines, ticket⟩ := under lanes L.lens L.certified
  exact WilsonMatrixTicketLanesObservation.on_layout simple L refines ticket

end YM.Integration.WilsonMatrixTicketLanes
