import YM.Integration.WilsonPhysicalHistoryRetainedSpringPolynomialRun
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankPrice

/-! The three bare blocks and every member of the original corrected list
carry their full fieldwise coefficient masses on the shared rooted coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Comparison.RG02
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def facePaper (G : Gauge) (K : ℕ) : ℝ:=(Fintype.card PlaqAxes:ℝ)*∑ j∈range K,faceRankPrice G (j+2)
theorem face_paper_nonneg (G : Gauge) (K : ℕ) : 0≤facePaper G K:=
  mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _=>sum_nonneg fun _ _=>abs_nonneg _)
theorem face_root_price (X : Coat T F) (x : Site f) (K : ℕ) {g : ℝ} (hg : 0≤g) (g1 : g≤1) :
    Rise.coin (facePortfolio X x K g)≤g^2*facePaper G K := by
  apply (face_portfolio X x K g).2.1.trans
  unfold facePaper
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold faceGermPrice
  rw [mul_sum];apply sum_le_sum
  intro j _
  rw [abs_of_nonneg hg,pow_add]
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _=>abs_nonneg _)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hg g1 (n:=j)) (sq_nonneg g)

theorem site_root_factor (X : Coat T F) {h : ℕ} (A : ℕ→Atom G h) (pos : 0<h)
    {σ D g E : ℝ} (hs : 0<σ) (paid : SumBudget (fun i=>(A i).budget σ) D)
    (x : Site f) (K : ℕ) (hg : 0≤g) (g1 : g≤1)
    (fee : D*((max 1 σ⁻¹)^siteRankPower h K*siteRankPaper G h K)≤E) :
    Rise.coin (sitePortfolio X A x K g)≤g^h*E := by
  apply (site_root_price X A pos hs paid x K hg g1).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left fee (pow_nonneg hg h)

theorem gram_rank_fee (G : Gauge) {D Z H E : ℝ} (hd : 0≤D) (path : D≤Z) (quote : 0≤H)
    (spent : Z^2*H≤E) : Stationary.gramCost G D*H≤ Stationary.gramCost G 1*E := by
  have id : Stationary.gramCost G D=Stationary.gramCost G 1*D^2:=by unfold Stationary.gramCost;ring
  rw [id,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by unfold Stationary.gramCost;positivity)
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd path 2) quote).trans spent

theorem rooted_currency {E : Type*} [DecidableEq E] (r : ℝ) (P : Normal.poly E) {A : ℝ} (paid : Rise.coin P≤A) :
    Rise.coin (MvPolynomial.C (r:ℂ)*P)≤|r| * A := by
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left paid (abs_nonneg _)

theorem graded_packet (X : Coat T F) (a : PrismA G) (d : ℕ) (low : 3≤a.grade) (high : a.grade≤d)
    (x : Site f) (K : ℕ) {g p E : ℝ} (hg : 0<g) (g1 : g≤1) (lo : 1/2≤p) (hi : p≤3/2) (ep : 0≤E)
    (paid : Rise.coin (sitePortfolio X a.cells x K g)≤g^(a.rise+2)*E) :
    Rise.coin (MvPolynomial.C (((Integral.temperature g*p*(g/Real.sqrt p)^(a.grade-a.rise)):ℝ):ℂ)*
      sitePortfolio X a.cells x K g)≤(2:ℝ)^(d+1)*g^3*E := by
  apply (rooted_currency _ _ paid).trans
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ ep
  have actual:=weighted_power hg lo hi (K:=1) (D:=1) (by norm_num) (by norm_num) (a.grade-a.rise) a.rise
  rw [one_mul,one_pow,one_mul,mul_one,mul_one,Nat.sub_add_cancel a.rankA] at actual
  apply actual.trans
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
    (pow_le_pow_of_le_one hg.le g1 low) (pow_nonneg hg.le _) (by positivity)

end YM.Integration.OriginalMarkedRunAction
