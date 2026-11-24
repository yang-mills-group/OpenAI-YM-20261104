import YM.Integration.WilsonCapturedPointedClockBudget
import YM.Integration.WilsonCapturedSourceAngularRoof
import YM.Integration.WilsonOlderFreshGraphInvoiceOrder

/-! Literal pointed clock salary on the paid source strip, including the large-strip exponential
in the original position census. Every degree dependence is outside the inverse-coupling power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedNativeClockFare
open Lattice Wilson RG Stationary Finset Filter WilsonCoeffUV.Bank WilsonOriginalSuspendedTensor
open WilsonCapturedCoveredSourceWage WilsonCapturedSourceAngularRoof WilsonCapturedClockRankProjection
open scoped Classical BigOperators

theorem basin {σ μ:ℝ}(positive:0<μ)(smaller:μ≤σ):
    UVNext.PricedKernels.basin (σ/4)≤UVNext.PricedKernels.basin (μ/4):=by
  have ps:0<σ/4:=by linarith
  have pm:0<μ/4:=by linarith
  unfold UVNext.PricedKernels.basin
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Summable.tsum_le_tsum _ (Next.Scheduling.decay_summable 4 _ ps) (Next.Scheduling.decay_summable 4 _ pm)
  intro i
  unfold Next.Scheduling.decay
  gcongr

theorem tensor (G:Gauge){σ μ:ℝ}(pos:0<μ)(smaller:μ≤σ)(r:ℕ):
    fee G σ r ≤ fee G μ r * Real.exp (σ/4):=by
  let A:=2*(G.colorScale*(WilsonOriginalGroupInkDirections.weight G*r))
  have sp:0<σ:=pos.trans_le smaller
  have cover:max 1 (A/σ) ≤ max 1 (A/μ):=by
    by_cases h:0≤A
    · gcongr
    · exact (max_eq_left (le_trans (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) sp.le) zero_le_one)).le.trans (le_max_left ..)
  have div:2/(σ/2)≤2/(μ/2):=by gcongr
  have pr:=WilsonMarkedAngularTestInvoice.fee_nonnegative r r
  have mx:1 ≤ Real.exp (μ/2/2):=Real.one_le_exp (by positivity)
  have ex:Real.exp (σ/2/2)≤Real.exp (μ/2/2)*Real.exp (σ/4):=by
    rw [show σ/2/2=σ/4 by ring];exact le_mul_of_one_le_left (Real.exp_pos _).le mx
  unfold fee WilsonOriginalResidentAngles.fare WilsonOriginalSuspendedWord.price
  change _*(_*_*((max 1 (A/σ))^r))≤_*(_*_*((max 1 (A/μ))^r))*_
  calc
    _≤(((Fintype.card (Loc G 1)+1:ℕ):ℝ)^r*(2/(μ/2))^(4*r)*((4*r).factorial:ℝ)*
        (Real.exp (μ/2/2)*Real.exp (σ/4)))*
        (WilsonMarkedAngularTestInvoice.fee r r*(max 1 (r:ℝ))^r*(max 1 (A/μ))^r):=by gcongr
    _=_:=by ring

theorem fare (G:Gauge)(k r:ℕ){σ C β:ℝ}(pos:0<σ)(pc:0≤C)(paid:Real.exp ((min 1 σ)⁻¹^2) ≤ β):
    WilsonCapturedCoveredSourceWage.fare G k r σ C ≤
      (Real.exp (σ/4)*C)*(roof G k r 1*β):=by
  let μ:=min 1 σ
  let L:ℝ:=(k.factorial:ℝ)⁻¹*(Fintype.card (Fin r ↪ Fin k):ℝ)
  have pm:0<μ:=lt_min one_pos pos
  have bσ:0≤UVNext.PricedKernels.basin (σ/4):=by
    unfold UVNext.PricedKernels.basin
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg;intro t;unfold Next.Scheduling.decay;positivity
  have order:=basin pm (min_le_right 1 σ)
  have bμ:=bσ.trans order
  have good:=WilsonOriginalSuspendedTensor.nonnegative G pos k
  have small:=tensor G pm (min_le_right 1 σ) k
  have raw:=WilsonCapturedSourceAngularRoof.original G k r pm (min_le_left ..) (δ:=1) one_pos paid
  rw [Real.rpow_one] at raw
  calc
    _≤L*(UVNext.PricedKernels.basin (μ/4)*(fee G μ k*Real.exp (σ/4)*C)):=by
      unfold WilsonCapturedCoveredSourceWage.fare;dsimp only [L];gcongr
    _= (Real.exp (σ/4)*C)*WilsonCapturedCoveredSourceWage.fare G k r μ 1:=by
      unfold WilsonCapturedCoveredSourceWage.fare;dsimp only [L];ring
    _≤_:=mul_le_mul_of_nonneg_left raw (mul_nonneg (Real.exp_pos _).le pc)

theorem logs {H:ℝ}(hot:Real.exp 1≤H)(D:ℕ):
    (max 1 |1+Real.log (Real.log H)|)^D ≤ (2:ℝ)^D*D.factorial*H:=by
  have ph:0<H:=(Real.exp_pos _).trans_le hot
  have small:1≤Real.log H:=by simpa using Real.log_le_log (Real.exp_pos 1) hot
  have pos:0<Real.log H:=zero_lt_one.trans_le small
  have deep:0≤Real.log (Real.log H):=Real.log_nonneg small
  have wt:max 1 |1+Real.log (Real.log H)|≤2*Real.log H:=by
    rw [abs_of_nonneg (by linarith)]
    apply max_le <;> linarith [Real.log_le_sub_one_of_pos pos]
  calc
    _≤(2*Real.log H)^D:=pow_le_pow_left₀ ((le_max_left ..).trans' zero_le_one) wt _
    _=(2:ℝ)^D*(Real.log H)^D:=mul_pow .. 
    _≤(2:ℝ)^D*(H*D.factorial):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have t:=Real.pow_div_factorial_le_exp (Real.log H) pos.le D
      rw [Real.exp_log ph] at t
      exact (div_le_iff₀ (by positivity)).mp t
    _=_:=by ring

end YM.Integration.WilsonCapturedNativeClockFare
