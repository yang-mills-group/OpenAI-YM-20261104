import YM.Integration.WilsonCapturedPrimaryWeakTrialSocketRoom
import YM.Integration.WilsonOriginalSparseDatedFinance

/-! Buy the true axial aperture and the fixed sparse decoder tariffs before the cutoff and the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusSparseFareCalendar
open Filter Finset Wilson RG Lattice WilsonLimitConstruction
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Advent.Oak PhysicalNext.Repeat.Legato FVA1Physical.TwoReset
open Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonOriginalSparseFiledOpening (near)
open scoped Topology

private theorem tail {p T:ℕ}{H β C:ℝ}(pos:0<H)(band:H/2≤β)(one:(Real.sqrt β)⁻¹≤1)
    (enough:2*(p+1)≤T)(cash:3*(abs C)*2^(p+1)≤H):
    C*((Real.sqrt β)⁻¹)^T ≤ (H^p)⁻¹/3:=by
  have hot:0<β:=(half_pos pos).trans_le band
  have gp:0≤(Real.sqrt β)⁻¹:=(inv_pos.mpr (Real.sqrt_pos.mpr hot)).le
  have square:((Real.sqrt β)⁻¹)^2 ≤ 2/H:=by
    rw [inv_pow,Real.sq_sqrt hot.le,←one_div]
    exact (div_le_div_iff₀ hot pos).mpr (by linarith)
  have amount:(abs C)*2^(p+1)/H ≤ 1/3:=by apply (div_le_iff₀ pos).mpr;linarith
  calc
    _ ≤ (abs C)*((Real.sqrt β)⁻¹)^T:=mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg gp _)
    _ ≤ (abs C)*(((Real.sqrt β)⁻¹)^2)^(p+1):=by
      rw [←pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp one enough) (abs_nonneg _)
    _ ≤ (abs C)*(2/H)^(p+1):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) square _) (abs_nonneg _)
    _ = ((abs C)*2^(p+1)/H)/(H^p):=by rw [div_pow,pow_succ H];ring
    _ ≤ (1/3)/(H^p):=div_le_div_of_nonneg_right amount (pow_nonneg pos.le _)
    _ = _:=by ring

private theorem precision {H:ℝ}(h:3≤H)(p:ℕ):(H^(p+1))⁻¹ ≤ (H^p)⁻¹/3:=by
  have pos:0<H:=by linarith
  have unit:H⁻¹ ≤ 1/3:=by rw [←one_div];exact one_div_le_one_div_of_le (by norm_num) h
  rw [pow_succ,mul_inv,div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by simpa using unit) (inv_nonneg.mpr (pow_nonneg pos.le _))

variable {G:Gauge}(R:Run G)(simple:G.Simple)(tube:LinkTube G)(pieces rank hit bill pole target p:ℕ)
  (order delay:Bool→ℕ)(C:ℝ)

include simple in
/-- Each term uses the actual physical temperature on all allowed period and cutoff choices. -/
theorem original (enough:2*(p+1)≤target):
    ∀ᶠ i:ℕ in atTop,∀(N per:ℕ),i≤N→∀W:RG.Rep G (R.family.side i per),
      W.p=R.family.path.levels.budget i→W.beta=R.family.path.β N per i→
      let H:=R.family.path.levels.clock.hatBeta i
      let g:=(Real.sqrt W.beta)⁻¹
      let w:=WilsonEmittedCubeRoom.width R.family.path.levels tube i
      Room W.p (R.family.side i per) tube W.p.B w ∧ 0≤w ∧ w≤2*g^(1/2:ℝ) ∧
      WilsonOriginalSparseFiledOpening.starts G hit bill (near (p+1) pole 1)≤H ∧ groupPrice tube 0≤H^1 ∧
      WilsonOriginalCensusTariffDate.Begun tube pieces rank (3*hit) hit order delay H ∧
      (H^(p+1))⁻¹≤(H^p)⁻¹/3 ∧ C*g^target≤(H^p)⁻¹/3:=by
  have rise:=RG01.Physical.hats simple R.family.path.levels
  filter_upwards [WilsonCapturedPrimaryWeakTrialSocketRoom.original R simple tube rank hit order delay,
    rise.eventually_ge_atTop (WilsonOriginalSparseFiledOpening.starts G hit bill (near (p+1) pole 1)),
    rise.eventually_ge_atTop (groupPrice tube 0),rise.eventually_ge_atTop 3,
    rise.eventually_ge_atTop (3*(abs C)*2^(p+1)),
    rise.eventually (WilsonOriginalCensusTariffDate.original tube pieces rank (3*hit) hit order delay)]
    with i room gate reader late cash begun N per live W atBudget heat H g w
  have stock:=room N per live W atBudget heat
  have pos:0<H:=zero_lt_one.trans (R.alloy.B.a.fits.delayed i)
  exact ⟨stock.1,stock.2.1,stock.2.2.1,gate,by simpa only [pow_one] using reader,begun,precision late p,
    tail pos stock.2.2.2.1 (stock.2.2.2.2.2.1.trans (by norm_num)) enough cash⟩

end YM.Integration.WilsonOriginalCensusSparseFareCalendar
end
