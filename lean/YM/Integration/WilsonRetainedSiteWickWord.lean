import YM.Integration.WilsonRetainedJointVertexPolynomial
import YM.Integration.WilsonCoherentMayerRootPortfolio
import YM.Integration.WilsonPhysicalHistoryRetainedSpringPowers

/-! The earlier Wilson action at one actual root. Only the originally permitted
angular ranks enter its Wick polynomial and each term keeps its coupling grade. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def siteWeight (a : PrismA G) (g p : ℝ) : ℝ :=
  Comparison.RG02.Integral.temperature g*p*(g/Real.sqrt p)^(a.grade-a.rise)

def rootedSite (X : Coat T F) (a : PrismA G) (x : Site f) (K : ℕ) (g p : ℝ) : Normal.poly (Eye X) :=
  ∑ j ∈ range K, MvPolynomial.C ((siteWeight a g p*g^(a.rise+2+j) : ℝ) : ℂ) *
    WilsonCoherentMayerRootPortfolio.deposit X a.cells x (a.rise+2+j)

def rootedSiteMass (a : PrismA G) (σ D : ℝ) (K : ℕ) (g : ℝ) : ℝ :=
  2^(a.grade-a.rise+1)*g^a.grade * ∑ j ∈ range K, g^j *
    (D*WilsonCoherentMayerRootTariff.price G σ (a.rise+2) (a.rise+2+j))

theorem rooted_site_read (X : Coat T F) (a : PrismA G) {σ D : ℝ} (hs : 0<σ)
    (filed : Commission a.cells σ D a.grade) (x : Site f) (K : ℕ) (g p : ℝ) (z : Air f G) :
    Cloud.paint (fun u => z (tube X u)) (rootedSite X a x K g p) =
      (siteWeight a g p : ℂ)*siteTaylor a.cells x (angularSample F z) (a.rise+K+1) g := by
  rw [WilsonCoherentMayerRootPortfolio.measured X a.cells hs filed.toll]
  have low (j : ℕ) (hj : j∈range (a.rise+2)) :
      Cloud.paint (fun u => z (tube X u)) (WilsonCoherentMayerRootPortfolio.deposit X a.cells x j)=0 := by
    rw [(WilsonCoherentMayerRootPortfolio.original X a.cells hs filed.toll x j).2.2 z,
      (site_initial a.cells hs filed.toll x (angularSample F z)).2 j (mem_range.mp hj)]
    rfl
  have split : a.rise+K+1+1=(a.rise+2)+K := by omega
  rw [split, Finset.sum_range_add]
  have vanish : ∑ j ∈ range (a.rise+2), (g:ℂ)^j * Cloud.paint (fun u => z (tube X u))
      (WilsonCoherentMayerRootPortfolio.deposit X a.cells x j)=0 := by
    exact Finset.sum_eq_zero fun j hj => by rw [low j hj, mul_zero]
  rw [vanish, zero_add, Finset.mul_sum]
  have scalar (d : ℂ) : Cloud.paint (fun u => z (tube X u)) (MvPolynomial.C d)=d := by simp [Cloud.paint]
  simp only [rootedSite, map_sum, map_mul, scalar, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

theorem rooted_site_degree (X : Coat T F) (a : PrismA G) {σ D : ℝ} (hs : 0<σ)
    (filed : Commission a.cells σ D a.grade) (x : Site f) (K : ℕ) (g p : ℝ) :
    (rootedSite X a x K g p).totalDegree ≤ a.rise+K+1 := by
  unfold rootedSite
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  have small := mem_range.mp hj
  exact (WilsonCoherentMayerRootPortfolio.original X a.cells hs filed.toll x _).1.trans (by omega)

theorem rooted_site_price (X : Coat T F) (a : PrismA G) {σ D : ℝ} (hs : 0<σ)
    (filed : Commission a.cells σ D a.grade) (x : Site f) (K : ℕ) (g p : ℝ)
    (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2) :
    Rise.coin (rootedSite X a x K g p) ≤ rootedSiteMass a σ D K g := by
  unfold rootedSite rootedSiteMass
  apply (Rise.collect 0 zero_le_one _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let coeff := WilsonCoherentMayerRootPortfolio.deposit X a.cells x (a.rise+2+j)
  let tariff := D*WilsonCoherentMayerRootTariff.price G σ (a.rise+2) (a.rise+2+j)
  have price : Rise.coin coeff ≤ tariff := (WilsonCoherentMayerRootPortfolio.original X a.cells hs filed.toll x _).2.1
  have pos : 0≤tariff := (show 0≤Rise.coin coeff from by rw [Rise.metal]; positivity).trans price
  have raw := weighted_power hg lo hi (show (0:ℝ)≤1 from zero_le_one) pos (a.grade-a.rise) (a.rise+j)
  have alignment : a.grade-a.rise+(a.rise+j)=a.grade+j := by have rank := a.rankA; omega
  have power : a.rise+j+2=a.rise+2+j := by omega
  simp only [one_mul, one_pow, mul_one, alignment, power] at raw
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hg.le _)]
  calc
    _ ≤ (|siteWeight a g p| * g^(a.rise+2+j))*tariff :=
      mul_le_mul_of_nonneg_left price (mul_nonneg (abs_nonneg _) (pow_nonneg hg.le _))
    _ = |siteWeight a g p| * (tariff*g^(a.rise+2+j)) := by ring
    _ ≤ 2^(a.grade-a.rise+1)*tariff*g^(a.grade+j) := raw
    _ = _ := by rw [pow_add]; ring

end YM.Integration.OriginalMarkedRunAction

