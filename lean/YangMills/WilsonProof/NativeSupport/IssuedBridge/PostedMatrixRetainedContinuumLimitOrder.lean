import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7MacroscopicRetainedMatrixInput
import YM.SignedWilsonExpansion.Homes.Universal
import YM.FullVolume.Finale.Program
import YM.Integration.WilsonOriginalOpticalSchedule
import YM.Integration.WilsonMatrixTicketFuelLanes

set_option autoImplicit false
noncomputable section
universe u
namespace IssuedBridge.PostedMatrixRetainedContinuumLimitOrder
open YM YM.Integration
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)

open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule

/-- Full-volume order and the original matrix-priced physical appointment use the same daughter. -/
def OrderedWithFirst (cohort:Ultrafilter (ℕ×ℕ)→Prop):Prop:=
  ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)
    (F:Final R.family (v.refine w) S)(L:EveryPhase.Almanac F)
    (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (X:Scaling S),
    FullVolume.PositionsUV R.family Extraction.Sequence.full ∧
    (SignedWilsonExpansion.Homes.track (v.refine w)).Ordered R.family S ∧
    Pert.FirstExtension F X ∧
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
    ∃(Y:(Bel R.family.book).Hierarchy)(Z:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))
      (_bliss:Bliss F l Z Y)(P P':ℝ→Spin.change S 4)(J:ℝ→PhysMS.tower S)
      (φ:E4→ℝ)(a d e:ℝ→ℝ), (∀ᶠr in trail,J r 4=P' r) ∧
      Trace.Target.XScheme F simple Y l P P' φ ∧ Trace.Target.FieldComparison F Y Z P P' a d e ∧
      Leading F J ∧ (∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d) ∧
      (l:Filter (ℕ×ℕ)) ≤ (v.refine w).fuse ∧ cohort l ∧
      Log.MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter (ℕ×ℕ)) ∧
      LogTrace F Q.port

theorem ordered {T:Campaign R} (W:Campaign.Pillars R T) {κ:ℝ}
    (fund:FundedOriginalProperties.{u} simple κ W)
    (physical:WilsonMatrixTicketFuelPrice.FromStrongBin R.family)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (issued:∀(f:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤f.fuse→cohort l):
    OrderedWithFirst.{u} R simple cohort:=by
  intro v
  obtain ⟨w, S, F, L, Q, X, packet⟩ :=
    PhysicalMatching.H7MacroscopicRetainedMatrixVision.retained.{u} R simple W fund physical cohort issued v
  obtain ⟨_, _, _, _, _, _, _, _, _, whole, _⟩ := fund.2.1.refine v
  have horder : (SignedWilsonExpansion.Homes.track (v.refine w)).Ordered R.family S :=
    YM.FullVolume.Final.from_spec (R := R) (v.refine w) ⟨F⟩ whole
  exact ⟨w, S, F, L, Q, X, whole, horder, packet⟩

/-- The paid original school supplies the physical matrix and the full-volume control. -/
theorem original {a : Axis} {ε : ℝ} {s : WilsonOriginalAllOrderCourse.Schedule G}
    {T : Campaign R} {W : Campaign.Pillars R T}
    (paid : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (issued : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
      (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) :
    OrderedWithFirst.{u} R simple cohort := by
  have funded : FundedOriginalProperties.{u} simple ε W := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩ := paid.originalSchool
    exact h
  have physical : WilsonMatrixTicketFuelPrice.FromStrongBin R.family :=
    WilsonMatrixTicketFuelPrice.lanes R
      (by norm_num [OPE.Stroke.epsilonR]) (by norm_num [OPE.Stroke.epsilonR]) paid.nested.1
  exact ordered.{u} R simple W funded physical cohort issued

end IssuedBridge.PostedMatrixRetainedContinuumLimitOrder
