import YM.Integration.SignedMarkedChartGerm
import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! Each frozen numerical socket of the original fixed-date physical basis is the
registered finite jet on its own displaced nonlinear forest chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseChart
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped Classical ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open PhysicalNext.Repeat.Legato Source Labels ActualRunCurvaturePackets
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds IndependentSourcePathFamily

variable {G : Gauge} (R : Run G) {V : Type} (d : V→ℕ)
    {D : V→ℕ} (knob : (j:V)→Knob (D j)) (p : V→Chamber)
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→AxisChart G F)
local notation "B" => WilsonReceivedCanonicalVerseBasis.basis R d knob p

theorem original (j : V) (b : Choice R d j) (z : Site f)
    (hM : M=reveal G S F*((reveal G S F).transpose*M))
    (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    let e := B j b
    let T := OriginalMarkedSourceComet.colour e.path e.color e.weight e.quadrant
    (X:Ink (Active G F ⊕ Woods G c))^e.rank * retool (shore S F M ρ)
      (loom (camSlice G S F M) (Blue.flash (sprig (meter T z) e.rank))) =
      jet (fun u : Sloc S F G =>
        (raw R d (entry R d j b)).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ u)) z) := by
  dsimp only
  rw [SignedMarkedChartGerm.atom S F M ρ _ z hM hρ h0]
  simp_rw [WilsonReceivedCanonicalVerseBasis.field R d knob p]

theorem filed [Fintype V][DecidableEq V] (q:(j:V)→Choice R d j)(x:V → Cover)(j:V):
    let a:=B j (q j)
    WilsonReceivedCanonicalVerseRegister.start R d knob p q x {j} =
      OriginalMarkedSourceComet.source D j (OriginalMarkedSourceComet.colour a.path a.color a.weight a.quadrant)
        a.knob a.point a.head (x j) :=by
  dsimp only
  unfold WilsonReceivedCanonicalVerseRegister.start
  rw [IndependentSourcePathFamily.singleton]
  unfold IndependentSourcePathFamily.single
  rw [Fintype.sum_unique]
  rfl

end YM.Integration.WilsonReceivedCanonicalVerseChart
