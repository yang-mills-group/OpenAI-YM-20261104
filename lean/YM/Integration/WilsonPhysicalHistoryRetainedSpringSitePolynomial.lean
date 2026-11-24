import YM.Integration.WilsonCoherentMayerRootPortfolio
import YM.Integration.WilsonPhysicalHistoryRetainedSpringInitial

/-! A rooted filed list of valence h first contributes at angular degree h.
Its finite polynomial keeps the original signed entries and their joint rises. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoherentMayerHearing Dict06.Series
open PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs WilsonCoherentMayerRootPortfolio
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {h : ℕ}

def sitePortfolio (X : Coat T F) (A : ℕ→Atom G h) (x : Site f) (K : ℕ) (g : ℝ) : Normal.poly (Eye X):=
  ∑ j∈range K,MvPolynomial.C ((g:ℂ)^(h+j))*deposit X A x (h+j)

def sitePortfolioPrice (G : Gauge) (σ D : ℝ) (h K : ℕ) (g : ℝ) : ℝ:=
  ∑ j∈range K,|g|^(h+j)*(D*WilsonCoherentMayerRootTariff.price G σ h (h+j))

theorem site_portfolio (X : Coat T F) (A : ℕ→Atom G h) (pos : 0<h) {σ D : ℝ} (hs : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) D) (x : Site f) (K : ℕ) (g : ℝ) :
    (sitePortfolio X A x K g).totalDegree≤h-1+K ∧
    Rise.coin (sitePortfolio X A x K g)≤ sitePortfolioPrice G σ D h K g ∧
    ∀ z : Air f G,Cloud.paint (fun u=>z (tube X u)) (sitePortfolio X A x K g)=
      siteTaylor A x (angularSample F z) (h-1+K) g := by
  have orig:=WilsonCoherentMayerRootPortfolio.original X A hs paid x
  refine ⟨?_,?_,?_⟩
  · unfold sitePortfolio
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply (MvPolynomial.totalDegree_mul ..).trans
    rw [MvPolynomial.totalDegree_C,zero_add]
    have bounds:=mem_range.mp hj
    exact (orig (h+j)).1.trans (by omega)
  · unfold sitePortfolio sitePortfolioPrice
    apply (Rise.collect 0 zero_le_one _ _).trans
    apply sum_le_sum
    intro j _
    apply (Rise.funds 0 zero_le_one _ _).trans
    rw [Rise.pay_C,norm_pow,Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (orig (h+j)).2.1 (pow_nonneg (abs_nonneg _) _)
  · intro z
    let view (j : ℕ):=(g:ℂ)^j*Cloud.paint (fun u=>z (tube X u)) (deposit X A x j)
    have zero : ∑ j∈range h,view j=0:=by
      have low:=WilsonCoherentMayerRootPortfolio.measured X A hs paid x (h-1) g z
      rw [flat_site_polynomial A x (angularSample F z) (by omega : h-1<h) g,
        show h-1+1=h by omega] at low
      exact low.symm
    rw [WilsonCoherentMayerRootPortfolio.measured X A hs paid x (h-1+K) g z,
      show h-1+K+1=h+K by omega]
    change _=∑ j∈range (h+K),view j
    rw [sum_range_add,zero,zero_add]
    simp only [sitePortfolio,view,map_sum,map_mul,Cloud.paint,MvPolynomial.aeval_C]
    rfl

end YM.Integration.OriginalMarkedRunAction
