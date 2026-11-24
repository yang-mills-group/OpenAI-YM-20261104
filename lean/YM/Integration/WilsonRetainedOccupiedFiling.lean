import YM.Integration.WilsonRetainedOccupiedWick
import Mathlib.Algebra.MvPolynomial.Funext

/-! Equality of the rooted register and the independent torus filing before contraction. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical

open WilsonCoeffUV.Blue PowerSeries
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- The real free-link tests determine even complex marked polynomials. -/
theorem forest_ext (X : Coat T F) {p q : Normal.poly (Eye X)}
    (same : ∀ z : Air f G, Cloud.paint (fun i => z (tube X i)) p=Cloud.paint (fun i => z (tube X i)) q) : p=q := by
  apply MvPolynomial.funext_set (fun _ : Eye X => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro v hv
  have pre (i : Eye X) : ∃ a : ℝ, (a : ℂ)=v i := hv i (Set.mem_univ i)
  choose w hw using pre
  let z : Air f G := WithLp.toLp 2 (Function.extend (tube X) w (fun _ => 0))
  have atSlot (i : Eye X) : ((z (tube X i) : ℝ):ℂ)=v i := by
    change ((Function.extend (tube X) w (fun _ => 0) (tube X i) : ℝ):ℂ)=v i
    rw [(tube X).injective.extend_apply, hw]
  have vEq : (fun i => ((z (tube X i):ℝ):ℂ))=v := funext atSlot
  have read := same z
  change MvPolynomial.eval (fun i => ((z (tube X i):ℝ):ℂ)) p = MvPolynomial.eval (fun i => ((z (tube X i):ℝ):ℂ)) q at read
  rwa [vEq] at read

theorem rooted_vanish (X : Coat T F) (a : PrismA G) {σ D : ℝ} (hs : 0<σ)
    (filed : Commission a.cells σ D a.grade) (x : Site f) (r : ℕ) (low : r<a.rise+2) :
    WilsonCoherentMayerRootPortfolio.deposit X a.cells x r=0 := by
  apply forest_ext X
  intro z
  rw [(WilsonCoherentMayerRootPortfolio.original X a.cells hs filed.toll x r).2.2 z,
    (site_initial a.cells hs filed.toll x (angularSample F z)).2 r low, map_zero]
  rfl

theorem filed_rooted_coefficient (X : Coat T F) (a : PrismA G) {σ D : ℝ} (hs : 0<σ)
    (filed : Commission a.cells σ D a.grade) (r : ℕ) :
    (∑ x : Site f, WilsonCoherentMayerRootPortfolio.deposit X a.cells x r) =
      forestPolynomial X (coeff (a.grade-a.rise+r) (PowerSeries.X^2*flash (Mosaic.surf a f))) := by
  apply forest_ext X
  intro z
  rw [map_sum, forest_read, filed_vertex a hs filed (angularSample F z) r, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => (WilsonCoherentMayerRootPortfolio.original X a.cells hs filed.toll x r).2.2 z

theorem filed_occupied {I : Type*} [Fintype I] [DecidableEq I] (X : Coat T F) (Z : SeriesA G)
    {σ D : ℝ} (hs : 0<σ) (draw : Draw Z σ D) (a : I → PrismA G) (enrolled : ∀ j, a j ∈ Z)
    (K : ℕ) (g p : ℝ) (B : Normal.poly (Eye X)) :
    (∑ x : I → Site f, occupiedPolynomial X a x K g p B) =
      B*filedPolynomial X a (fun j => (a j).rise+K+1) g p := by
  apply forest_ext X
  intro z
  rw [map_sum, map_mul, filed_read X Z hs draw a enrolled, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [occupiedPolynomial, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact rooted_site_read X (a j) hs (draw.2 (a j) (enrolled j)) (x j) K g p z

end YM.Integration.OriginalMarkedRunAction

