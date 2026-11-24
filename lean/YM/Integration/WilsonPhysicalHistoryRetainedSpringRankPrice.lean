import YM.Integration.WilsonPhysicalHistoryRetainedSpringSitePolynomial
import YM.Integration.WilsonCoherentMayerRootGrowth

/-! Shrinking the original rooted path width gives a finite, period-independent
coefficient expense at the true angular valuation of each deposited row. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def siteRankPower (h K : ℕ) := ((h+K)*2)*h+(Fintype.card Axis)*(h+K)
def siteRankPaper (G : Gauge) (h K : ℕ) : ℝ :=
  ∑ j∈range K,|WilsonCoherentMayerRootTariff.price G 1 h (h+j)|

theorem site_narrow {h : ℕ} (A : ℕ→Atom G h) {t σ D : ℝ} (sub : t≤σ)
    (paid : SumBudget (fun i=>(A i).budget σ) D) :
    SumBudget (fun i=>(A i).budget t) D := by
  apply Push.AbsoluteSums.budget_mono paid
  · intro i
    exact mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (Real.exp_pos _).le
  · intro i
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right sub (Nat.cast_nonneg _))) (sum_nonneg fun _ _=>abs_nonneg _)

theorem site_rank_price (G : Gauge) (h K : ℕ) {σ D g : ℝ} (hs : 0<σ) (hd : 0≤D)
    (hg : 0≤g) (g1 : g≤1) :
    sitePortfolioPrice G (min σ 1) D h K g≤
      g^h*D*(max 1 σ⁻¹)^siteRankPower h K*siteRankPaper G h K := by
  let t:=min σ 1
  let u:=max 1 σ⁻¹
  have ht : 0<t:=lt_min hs zero_lt_one
  have hu : 1≤u:=le_max_left .. 
  have inv : t⁻¹≤u:=by
    by_cases h : σ≤1
    · simpa only [t,min_eq_left h] using (le_max_right (1:ℝ) σ⁻¹)
    · simpa only [t,min_eq_right (le_of_not_ge h),inv_one] using hu
  unfold sitePortfolioPrice siteRankPaper
  rw [mul_sum]
  apply sum_le_sum
  intro j mem
  let a:=WilsonCoherentMayerRootTariff.price G 1 h (h+j)
  have hj : h+j≤h+K:=by have m:=mem_range.mp mem;omega
  have degree : ((h+j)*2)*h+(Fintype.card Axis)*(h+j)≤ siteRankPower h K:=by
    exact Nat.add_le_add (Nat.mul_le_mul_right h (Nat.mul_le_mul_right 2 hj)) (Nat.mul_le_mul_left _ hj)
  have paid:=WilsonCoherentMayerRootGrowth.purchased G h (h+j) ht (min_le_right σ 1)
  have price : WilsonCoherentMayerRootTariff.price G t h (h+j)≤|a| *u^siteRankPower h K:=by
    apply paid.trans
    apply mul_le_mul (le_abs_self a) _ (pow_nonneg (inv_nonneg.mpr ht.le) _) (abs_nonneg a)
    exact (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) inv _).trans (pow_le_pow_right₀ hu degree)
  rw [abs_of_nonneg hg,pow_add]
  calc
    _ ≤ (g^h*g^j)*(D*(|a| *u^siteRankPower h K)):=mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left price hd) (mul_nonneg (pow_nonneg hg _) (pow_nonneg hg _))
    _ ≤ (g^h*1)*(D*(|a| *u^siteRankPower h K)):=mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_one₀ hg g1) (pow_nonneg hg _))
          (mul_nonneg hd (mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans hu) _)))
    _ = _:=by ring

theorem site_root_price (X : Coat T F) {h : ℕ} (A : ℕ→Atom G h) (positive : 0<h)
    {σ D g : ℝ} (hs : 0<σ) (paid : SumBudget (fun i=>(A i).budget σ) D)
    (x : Site f) (K : ℕ) (hg : 0≤g) (g1 : g≤1) :
    Rise.coin (sitePortfolio X A x K g)≤g^h*D*(max 1 σ⁻¹)^siteRankPower h K*siteRankPaper G h K :=
  (site_portfolio X A positive (lt_min hs zero_lt_one) (site_narrow A (min_le_left σ 1) paid) x K g).2.1.trans
    (site_rank_price G h K hs ((tsum_nonneg paid.1).trans paid.2.2) hg g1)

end YM.Integration.OriginalMarkedRunAction
