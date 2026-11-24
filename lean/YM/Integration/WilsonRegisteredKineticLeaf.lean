import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskGram
import YM.Integration.WilsonCoherentMayerOldSlots
import YM.RG01Estimate.CensusStep
import YM.Integration.LocalComparisonInterface
import YM.Next.WARD_BIN.Wheels

/-! Enter each true signed term in the filed kinetic action on the same
earlier carrier. The Gram address contains both original ordered walks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonRegisteredKineticLeaf
open Function Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory
open ConnectedActivityE6 Precision Exterior Shell Channel Next.Scheduling WilsonStartup
open Work.E03 RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato AnalyticBridge.VerifiedReset RG01Estimate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus Progress.DirectedRecipe
open scoped Topology Classical BigOperators
variable {G : Gauge} {f : Side}

def address (K : PathData G) (p : BudgetPoint) (d : Low) (s : Signed) (o : Site f) :
    RegularAddress f :=
  ⟨affine s 0 o, (d.home K p o).image (affine s 0),
    Finset.mem_image_of_mem _ (d.small_home K p o)⟩

def reading (K : PathData G) (B : Clip) (d : Low) (s : Signed) (o : Site f) (a : ℝ) :
    Config G f → ℝ :=
  (fun U => (a*d.mark K B)*d.plain K o U) ∘ pull s 0

def income (K : PathData G) (B : Clip) (p : BudgetPoint) (d : Low) (a : ℝ) : ℝ :=
  WardBin.Wheels.tariff p * (|a*d.mark K B| *((faceCost G p+rowCost G p (d.length K))*p.threshold^2))

theorem licensed (K : PathData G) (B : Clip) (p : BudgetPoint) (issued : Decent B p)
    (d : Low) (s : Signed) (o : Site f) (a : ℝ) :
    let loc := address K p d s o
    p.Regular loc.support (reading K B d s o a) ∧
      p.supBounds loc.site loc.support (reading K B d s o a) (income K B p d a) := by
  intro loc
  have budget := Bill.mul_left (a*d.mark K B) (d.plain_bill K B o issued)
  have reg : p.Regular (d.home K p o) (fun U => (a*d.mark K B)*d.plain K o U) :=
    reg_bill budget (continuous_const.mul (d.plain_cont K o)).measurable
      (fun U V agree => by rw [d.plain_local K p issued.radius o U V agree])
      (fun T U => by rw [d.plain_gauge K o T U])
  exact ⟨WardBin.Wheels.regular_carry s 0 reg,
    WardBin.Wheels.carry_bound s 0 reg (budget.sup (fun _ h => h))⟩

theorem seated (R : Run G) {k N per eo ep : ℕ} {α : ℝ} (live : k<N)
    (Q : Rep G (R.family.side k per)) (record : LocalComparison.NormAt R.family k Q.p eo ep α)
    (d : Low) (s : Signed) (o : Site (R.family.side k per)) (a : ℝ)
    (old : Team (QLocalInheritedRegularSlots.carrier Q)) :
    let K := (R.family.path.rep N per k).path
    let B := (R.family.path.levels.params k).clip
    let loc := address K Q.p d s o
    ∃ (b : Leaf (QLocalInheritedRegularSlots.carrier Q))
      (W : Team (QLocalInheritedRegularSlots.carrier Q)), b∈W.own ∧ old.own⊆W.own ∧
      W.weight=old.weight*income K B Q.p d a ∧ b.crest=loc.support ∧
      ∀ U, b.ingredient U = masked Q.p.threshold loc.support (reading K B d s o a) U := by
  classical
  intro K B loc
  have src := CensusStep.decent R.kit (N := N) live
  have decent : Decent B Q.p := ⟨src.direct, by rw [record.block]; exact src.radius,
    by rw [record.block, record.threshold]; exact src.cut⟩
  obtain ⟨reg, rate⟩ := licensed K B Q.p decent d s o a
  obtain ⟨tag, free⟩ := WilsonCoherentMayerOldSlots.room Q loc old
  let b := ManuscriptQLocalOrdinaryLeaf.leaf Q loc (reading K B d s o a) reg rate tag
  let W := WilsonCoherentMayerOldSlots.booked Q loc old tag free (reading K B d s o a) reg rate
  exact ⟨b,W, WilsonCoherentMayerOldSlots.entered Q loc old tag free (reading K B d s o a) reg rate⟩

end YM.Integration.WilsonRegisteredKineticLeaf
