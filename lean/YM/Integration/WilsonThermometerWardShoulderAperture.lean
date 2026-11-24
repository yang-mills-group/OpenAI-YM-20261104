import YM.Integration.WilsonThermometerWardBareAperture
import YM.Integration.WilsonOriginalThermometerTollBudget

/-! Physical source tuition on a finite relative interval of the elected course. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardShoulderAperture
open Function Filter Finset Lattice Wilson RG Labels Source Push Extraction RG12 RG17 Climb Trace.Pilot
open MergeProof Next.Extract PhysicalNext.Repeat.Legato PhysicalNext.Repeat Legato Bandage
open RG05Readout RG05Readout.Address WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "fam" => R.family

private theorem ratio (m N:ℕ): (fam).S.a m/(fam).S.a N=Real.exp ((fam).S.scale N-(fam).S.scale m):=by
  rw [Real.exp_sub,Schedule.scale,Schedule.scale,Real.exp_log (inv_pos.mpr ((fam).S.a_pos N)),
    Real.exp_log (inv_pos.mpr ((fam).S.a_pos m))]
  simp only [div_eq_mul_inv,inv_inv,mul_comm]

/-- The maximal exponent is chosen from the field grade and the physical length before the internal Taylor order. -/
theorem original:∀ᶠ k:ℕ in atTop,∀{n N p:ℕ}(d:Fin n→ℕ)(sites:Fin n→Site ((fam).side N p))
    (S:Shelf (N:=N) (p:=p) R k d sites)(live:k≤N)(_ref:∀i,(fam).ref (d i)≤N)(y:(i:Fin n)→Palette (fam) (d i))
    (g:ℝ)(_gp:0<g)(T:ℕ)(_span:(fam).S.scale N-(fam).S.scale k≤T*Real.log g⁻¹)(i:Fin n),
    ((fam).labels.level (d i)).coeffSize (Next.Rank.Price.awake (fam) (d i) N N p (exposed R d sites S live y i))≤
       (g⁻¹)^(T*(d i+1))*size (y i):=by
  filter_upwards [WilsonThermometerWardBareAperture.band R 1 zero_lt_one] with k bought
  intro n N p d sites S live ref y g gp T span i
  let D:=(fam).S.scale N-(fam).S.scale k
  have ratioBound:(fam).S.a k/(fam).S.a N≤g⁻¹^T:=by
    calc
      _=Real.exp D:=ratio R k N
      _≤Real.exp (T*Real.log g⁻¹):=Real.exp_le_exp.mpr span
      _=g⁻¹^T:=by rw [Real.exp_nat_mul,Real.exp_log (inv_pos.mpr gp)]
  have e:Real.exp D≤g⁻¹^T:=(ratio R k N).symm.trans_le ratioBound
  have paid:=bought d sites S live ref y i
  rw [one_mul] at paid
  calc
    _≤((fam).S.a k/(fam).S.a N)^(d i)*(Real.exp D*size (y i)):=paid
    _≤(g⁻¹^T)^(d i)*((g⁻¹^T)*size (y i)):=mul_le_mul
      (pow_le_pow_left₀ (div_nonneg ((fam).S.a_pos k).le ((fam).S.a_pos N).le) ratioBound _)
      (mul_le_mul_of_nonneg_right e (size_ge _)) (mul_nonneg (Real.exp_pos _).le (size_ge _))
      (pow_nonneg (pow_nonneg (inv_pos.mpr gp).le _) _)
    _=_:=by rw [←mul_assoc,←pow_succ,←pow_mul]

end YM.Integration.WilsonThermometerWardShoulderAperture
