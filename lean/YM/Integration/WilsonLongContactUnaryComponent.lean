import YM.Integration.WilsonLongContactUnaryRegister
import YM.Integration.WilsonLongContactUnaryBloom

/-! The same original one-letter integral on the occupied registered finite roster. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactUnaryComponent
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


open WilsonLongContactUnaryRegister WilsonLongContactUnaryBloom
include owns in
theorem tithe (X : Coat T F) (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G)
    (l : ℕ) (s : Molecule S) :
    ((town T M).hire p V).tithe X k W a Ñ l s=M.tithe X k W a Ñ l s := by
  unfold Faction.tithe Leaf.tithe
  apply integral_congr_ae
  filter_upwards with z
  exact income M V p owns (X.wrapY z.1) W a Ñ k l z.2 s

include owns in
theorem bloom (X : Coat T F) (W a : ℝ) (Ñ : ChartRatio G) (l : ℕ) (s : Molecule S) :
    ((town T M).hire p V).bloom X W a Ñ l s=M.bloom X W a Ñ l s := by
  unfold Faction.bloom Leaf.bloom
  split
  · unfold Faction.steep Leaf.steep
    exact agree (fun tag=>tithe M V p owns _ _ W a Ñ l s)
  · rfl

include owns in
theorem original (x : ℝ) (χ : Chi) (K W a : ℝ) (Ñ : ChartRatio G) (l : ℕ)
    (U : Config G c) (s : Molecule S) :
    ((town T M).hire p V).lotus T x χ K W a Ñ l U s=M.lotus T x χ K W a Ñ l U s := by
  unfold Faction.lotus Leaf.lotus
  exact agree (fun r=>bloom M V p owns (prism T x χ K U (allot r)) W a Ñ l s)

end YM.PhysicalNext.Repeat.WilsonLongContactUnaryComponent
