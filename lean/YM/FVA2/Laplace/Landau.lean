import YM.FVA2.Laplace.Bare
import YM.FVA2.Orbit.Sectors
import YM.FVA2.Slice.Source
/-!
# Wilson series from the canonical real tree, evaluated in MS Landau Slice

Including marks and determinant, at the even-inversion regulator. Regular bare probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Metric MeasureTheory Measure PertExtension Series Radial Series.Tested GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge MultiGauge.Splice
open Wilson Lattice Wick MS MS.Native.Chart MS.Native YM.FVA2.Orbit MS.Cylinder MS.Book Convolve MS.Plane MS.Orbit MS.Swirl MS.Swirl.Near FiniteOrbit
open PowerSeries
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n:Side} {A J:Type} [Fintype J][DecidableEq J]
local notation "E" => Transverse G n
variable (a:Axes G n A J)
local notation "K" => W G n
local notation "F" => Slice.haar G n
variable (ev:Even n.val)
local notation "S" => land G ev
lemma price_land : (S).price= W G n:= by funext x; unfold W Screen.price; rw [landed ev]
lemma height : a.relative = Laplace.sink (S).weight (S).price:= by
 rw [ Laplace.sink, price_land, Axes.relative, mul_assoc]; refine congr_arg (Stack.exponential (Stack.advancing K) * ·) ?_; rw [Laplace.dreaming (S).weight (FiniteOrbit.sectors a ev)]; refine Eq.symm (Stack.rise_mul ?_ ?_); exact (show MS.Cylinder.Taylor.germ (Real.exp ∘ Slice.haar G n) from Real.contDiff_exp.contDiffAt.comp 0 (haar_smooth G n)).of_le le_top; exact (Wick.Gem.det_germ a.acceptable).of_le le_top
include ev
lemma fall (μ:Measure E)[μ.IsAddHaarMeasure] {O:Wilson.Config G n→ℝ} (h:PertExtension.Orb.PreTest O): a.sumBody μ (Stack.rise ((O ∘ nation) ∘ includeA G n)) = PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= by
 unfold Axes.sumBody; rw [ ← (S).genuine ev μ h,height a ev, show ((O∘nation) ∘ includeA G n)=(S).play O from funext fun x=> by rw [Screen.play,landed];rfl]; symm; apply (S).realization ev μ _ _ h; rw [price_land]; exact Slice.gaussian_kernel.symm
-- literal primitive `PhysicalSum` equality at bare parameters (`before`).
lemma entered [Fintype A][DecidableEq A](μ:Measure E)[μ.IsAddHaarMeasure] {O:Wilson.Config G n→ℝ} (h:PertExtension.Orb.PreTest O)
 (x:Wick.Formal.Table (FixedMode G n)) (hx:x∈Wick.Formal.OK σbranch) (hv: promote (Wick.pull a.R) x = Wick.Boson.bills a.X (Stack.rise ((O ∘ nation) ∘ includeA G n))) : Endμ (Master G n true) σbranch (before G n) x (Slice.record (PowerSeries.mk (Orb.diag (Orb.restrictedO O)))):= by
    rw [← fall a ev μ h]; exact a.End_sumBody μ _ _ hx hv
end YM.FVA2.Slice
