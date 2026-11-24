import YM.Integration.WilsonLongContactUnaryHousing
import YM.MergeProof.Trio

/-! The occupied singleton in the original marked integrand at arbitrary other activities. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactUnaryRegister
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {R : Rep G f} {T : Tube G S}
open Census Itinerary ConnectedActivityE6.Coat SliceRows Matter
variable {F : Forest S.ratio} (M : Leaf R) (V : Config G c) (p : Molecule S) (owns : M.turn.badge S∈p)

include owns in
theorem ticked : tick (address M) p={0} := by
  ext j
  have eq : j=0:=Subsingleton.elim _ _
  subst j
  rw [ticking]
  simp [address,owns]

include owns in
theorem signs : ((town T M).hire p V).signs={M.turn.badge S} := by
  change ((town T M).tune V|>.seat (tick (address M) p)).signs=_
  rw [Quartet.hei,ticked M p owns,Finset.map_singleton]
  rfl

include owns in
theorem charge (X : Coat T F) (a : ℝ) (d : Directions G f) :
    ((town T M).hire p V).paidU X a d=M.paidU X a d := by
  change ((town T M).tune V|>.seat (tick (address M) p)).paidU X a d=_
  rw [Township.quota_any,ticked M p owns,Finset.prod_singleton]
  rfl

include owns in
theorem income (X : Coat T F) (W a : ℝ) (Ñ : ChartRatio G) (k : Finset ℕ) (l : ℕ)
    (z : Air f G) (s : Molecule S) :
    ((town T M).hire p V).premium X W a Ñ k l z s=M.premium X W a Ñ k l z s := by
  unfold Faction.premium Leaf.premium
  rw [signs M V p owns,charge M V p owns]
  simp only [Finset.singleton_subset_iff,Finset.sdiff_singleton_eq_erase]

end YM.PhysicalNext.Repeat.WilsonLongContactUnaryRegister
