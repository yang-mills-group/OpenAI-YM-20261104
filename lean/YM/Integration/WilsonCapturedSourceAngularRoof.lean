import YM.Integration.WilsonCapturedCoveredSourceWage
import YM.Integration.WilsonThermometerUnitFilingMomentSale

/-! A single before-cutoff polynomial price for all finite thermal roots.
The center sum costs five inverse powers of the purchased strip. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedSourceAngularRoof
open Finset Lattice RG Wilson Stationary UVNext.PricedKernels WilsonCapturedCoveredSourceWage
open WilsonThermometerUnitFilingMomentSale WilsonOriginalSuspendedTensor
open scoped Classical BigOperators
def spatial : ℝ:=16*(16^4*24*Real.exp 1)*9

private theorem geometric {μ:ℝ} (pos:0<μ) (small:μ≤1):
    (1-Real.exp (-(μ/8)))⁻¹≤9*μ⁻¹:=by
  let A:=Real.exp (μ/8)
  have a:0<A:=Real.exp_pos _
  have surplus:μ/8≤A-1:=by dsimp [A];linarith only [Real.add_one_le_exp (μ/8)]
  have gt:0<A-1:=lt_of_lt_of_le (by positivity) surplus
  have eq:(1-A⁻¹)⁻¹=1+(A-1)⁻¹:=by field_simp;ring
  rw [Real.exp_neg,eq]
  have bound:(A-1)⁻¹≤(μ/8)⁻¹:=inv_anti₀ (by positivity) surplus
  rw [inv_div,div_eq_mul_inv] at bound
  have one:1≤μ⁻¹:=(one_le_inv₀ pos).mpr small
  linarith

theorem centers {μ:ℝ} (hp:0<μ) (hs:μ≤1) :
    UVNext.PricedKernels.basin (μ/4) ≤ spatial*(μ⁻¹)^5:=by
  let q:=Real.exp (-(μ/8))
  have q0:0≤q:=(Real.exp_pos _).le
  have q1:q<1:=Real.exp_lt_one_iff.mpr (by linarith)
  have s:0<μ/4:=by positivity
  have sm:μ/4≤1:=by linarith
  have per (n:ℕ): Next.Scheduling.decay 4 (μ/4) n ≤ positionCost 4 (μ/4)*q^n:=by
    have tally:=WilsonThermometerUnitFilingMomentSale.position s sm n 4
    unfold Next.Scheduling.decay
    have bound:((n:ℝ)+1)^4≤(1+2*(n:ℝ))^4:=pow_le_pow_left₀ (by positivity) (by linarith only [Nat.cast_nonneg (α:=ℝ) n]) _
    calc
      _ ≤ (positionCost 4 (μ/4)*Real.exp ((μ/4)*n/2))*Real.exp (-(μ/4)*n):=by gcongr;exact bound.trans tally
      _ = _:=by
        rw [mul_assoc,←Real.exp_add]
        dsimp [q]
        rw [←Real.exp_nat_mul]
        congr 2;ring
  have total:Summable (fun n:ℕ=>positionCost 4 (μ/4)*q^n):=(summable_geometric_of_lt_one q0 q1).mul_left _
  have stock:=Summable.tsum_le_tsum per (Next.Scheduling.decay_summable 4 _ s) total
  rw [tsum_mul_left,tsum_geometric_of_lt_one q0 q1] at stock
  have fee:positionCost 4 (μ/4)=16^4*24*Real.exp 1*(μ⁻¹)^4:=by
    unfold positionCost
    norm_num
    ring
  unfold UVNext.PricedKernels.basin
  calc
    _ ≤ 16*(positionCost 4 (μ/4)*(1-q)⁻¹):=by linarith
    _ ≤ 16*(positionCost 4 (μ/4)*(9*μ⁻¹)):=by
      have non:0≤positionCost 4 (μ/4):=by unfold positionCost;positivity
      gcongr
      exact geometric hp hs
    _ = _:=by rw [fee];unfold spatial;ring

def roof (G:Gauge) (k r:ℕ) (δ:ℝ):ℝ:=
  (k.factorial:ℝ)⁻¹*(Fintype.card (Fin r ↪ Fin k):ℝ)*spatial*fee G 1 k*
    (((5+(4*k+k)).factorial:ℝ)/δ^(5+(4*k+k)))

theorem original (G:Gauge) (k r:ℕ) {μ β δ:ℝ} (hp:0<μ)(hs:μ≤1)(δp:0<δ)
    (paid:Real.exp ((μ⁻¹)^2) ≤ β):fare G k r μ 1≤roof G k r δ*β^δ:=by
  let L:ℝ:=(k.factorial:ℝ)⁻¹*(Fintype.card (Fin r ↪ Fin k):ℝ)
  have l:0≤L:=by dsimp [L];positivity
  have root:0≤ spatial:=by unfold spatial;positivity
  have f:0≤fee G 1 k:=nonnegative G one_pos k
  have v:=centers hp hs
  have w:=window G k hp hs
  have good:=power hp hs δp paid (5+(4*k+k))
  unfold WilsonCapturedCoveredSourceWage.fare
  rw [mul_one]
  change L*(_*_)≤_
  calc
    _ ≤ L*((spatial*(μ⁻¹)^5)*(fee G 1 k*(μ⁻¹)^(4*k+k))):=by
      apply mul_le_mul_of_nonneg_left _ l
      exact mul_le_mul v w (nonnegative G hp k) (by positivity)
    _ = (L*spatial*fee G 1 k)*(μ⁻¹)^(5+(4*k+k)):=by rw [pow_add];ring
    _ ≤ (L*spatial*fee G 1 k)*(((5+(4*k+k)).factorial:ℝ)/δ^(5+(4*k+k))*β^δ):=
      mul_le_mul_of_nonneg_left good (by positivity)
    _ = _:=by unfold roof;dsimp only [L];ring

end YM.Integration.WilsonCapturedSourceAngularRoof
