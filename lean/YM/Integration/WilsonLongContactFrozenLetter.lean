import YM.Integration.WilsonLongContactFrozenGaussian

/-! The one-letter Gaussian expression on the concrete registered township. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Gaussian Tablet Quill Baffle Polar Prism Brim
open WardBin.Lies Push.PriceCompiler Foramen Gate Lotus Township Finset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {U : Config G c} {j n : ℕ} {L : Side}
variable {d A t C' w M N Q v δ K b' ζ β W k ε y₀ J' L₀ X' : ℝ}
open YM.Integration.WilsonLongContactTown

variable {R : RG.Rep G f}

def solitary (S : StepData c f) (M : Leaf R) : Molecule S :=
  ({0} : Finset (Fin 1)).map (registry S (address M))

theorem occupied (M : Leaf R) : tick (address M) (solitary S M) = {0} := by
  ext i
  simp [solitary,tick]

theorem measured (X : Coat T F) (aidx : ℕ) (M : Leaf R) (source : M.turn=.logKey aidx)
    {I : Type} [Fintype I] [DecidableEq I] (a : Museum F X.x (bareStores S) (R.activities.reg aidx).support Y I)
    (hp : Scrim X a)
    (room : Room P S T X.x) (W ζ : ℝ) (V : Config G c) (Γ : ChartRatio G) (l : ℕ)
    (positive : (Pond.circuit (podium S G Y X.B) (vary X V).relating).PosDef) :
    (town T M).cinema (vary X V) (solitary S M) W ζ Γ l (podium S G Y X.B) =
      ∫ s, creates X ζ (peanuts X a V R.beta s) *
        M.ingredient (strip6 X a V (peanuts X a V R.beta s)) ∂Gaussian.cloud (lamp6 X a V) := by
  have paid := singleton (ζ:=ζ) (τ:=address M) X aidx R a hp (0 : Fin 1)
    (by change M.turn.support R=(R.activities.reg aidx).support; rw [source]; rfl)
  rw [freezes X aidx R a ∅ (town T M) {0} hp paid room V (solitary S M) (occupied M) rfl Γ l positive]
  unfold deal
  rw [show scans R (town T M) {0} V=M.ingredient from frozen T M V]
  simp only [purse6, Finset.prod_empty, mul_one]

end YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
