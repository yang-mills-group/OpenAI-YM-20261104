import YM.SignedWilsonExpansion.Homes.ReStaff
import YM.Integration.WilsonPositivePursePosition
/-! hold fixed the stock Y and track full
 EveryPhase on full? track uses different f; phase installed on f. Limits restrict track when needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.Election
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot SignedWilsonExpansion.Homes
open WilsonPhysicalWeakWallStaff.ReStaff
open Function Filter Lattice Finset
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{R:Run G} (h:G.Simple)

structure PRAY (R:Run G)(h:G.Simple) where
  f : Extraction.Order
  S:Table R.family.book
  last:Final R.family f S
  TrackU :FullVolume.PositionsUV R.family Extraction.Sequence.full
  trackP : (track f).Ordered R.family S
  pillar:OPE.Facilities R.family f S
  H:(Bel R.family.book).Hierarchy
  Y: Ultrafilter (ℕ×ℕ)
  Z: Arch R.family
  bliss:Bliss last Y Z H
  staff:ℝ→ Day R.family S
  rises:Tendsto (fun r=>(staff r).1) Trace.Pilot.trail atTop
  roomy:∀ᶠr in Trace.Pilot.trail, Roomy h last (Y:=Y) H (staff r) r
  L: EveryPhase.Almanac last
  P: OPE.Orbits.Reader last.sector.derivatives last.sector.turns last.room.kernel.spin
  phase: EveryPhase.Completed last L
  foundation: OPE.Orbits.Foundation last P

namespace PRAY
variable {h} (M:PRAY R h) (S:XSpace.Normalize.Store G)
noncomputable abbrev J := preframe M.staff
noncomputable abbrev W := WilsonPositionPrescribedFrame.positioned M.last M.J S
lemma VFrame : ( ∀d, ∀ᶠr in Trace.Pilot.trail, PhysMS.Frame.obedient M.last M.H (M.J r) d ) ∧ PhysMS.Leading M.last M.J := masterPV h M.last M.H _ M.rises M.roomy
lemma trackV : (track M.f).PointLimits R.family M.S := SignedWilsonExpansion.Homes.whole M.TrackU M.last.room.generic
lemma WFrame : PhysMS.Leading M.last (M.W S) := WilsonPositivePursePosition.leading M.last M.J S M.VFrame.2 M.VFrame.1
lemma marked (d:ℕ): ∀ᶠ r in Trace.Pilot.trail,
      (S.measure d).D (WilsonPositionPrescribedScreen.hierarchy M.last (M.W S) d r)=(S.measure d).D (XSpace.Normalize.reference G d) := WilsonPositionPrescribedFrame.original M.last M.J S M.VFrame.2 d
end PRAY
end YM.Integration.Election
