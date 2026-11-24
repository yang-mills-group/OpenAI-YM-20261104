import YM.Integration.WilsonReportingUpperChartPrice
import YM.Extra.MULTISOURCE_BOUNDS.Columns

/-! The supremum on the entire physical group field, before the period is
selected, for a genuine primary registered at a fixed reporting scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingTopEnvelope
open Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Multi.BasisCost
open scoped Topology Classical
variable {G:Gauge} {C:Family G} (h:C.Makes) {d m N per:ℕ}
local notation "β" i => C.path.levels.clock.hatBeta i

private theorem threshold (i:ℕ) : (β i)⁻¹ ≤ C.path.levels.clock.threshold i := by
  have one:1 ≤ β i:=(C.path.levels.fits.delayed i).le
  have pos:0 < β i:=zero_lt_one.trans_le one
  have sq:Real.sqrt (β i) ≤ β i:=(Real.sqrt_le_left pos.le).2
    (by nlinarith only [mul_nonneg pos.le (sub_nonneg.mpr one)])
  exact (inv_anti₀ (Real.sqrt_pos.mpr pos) sq).trans
    (le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.one_le_exp (sq_nonneg _)))

theorem field (aged:C.ref d ≤ m) (live:m ≤ N) (z:C.label d) (o:Site (C.side N per))
    (X:Config G (C.side N per)) :
    ‖(C.S.a m:ℂ)^d*C.O N per (atK C h d m (N,per) z) o X‖ ≤
      price (C.localSection d)*(C.S.a m/C.S.a N)^(d+1)*(β N)^slots (C.labels.level d)*mass C d z := by
  let v:=(C.factory d N per).terminal.symm (atK C h d m (N,per) z)
  let r:=C.S.a m/C.S.a N
  have rp:0 ≤ r:=(div_pos (C.S.a_pos _) (C.S.a_pos _)).le
  have one:1 ≤ β N:=(C.path.levels.fits.delayed N).le
  have pos:0 < β N:=zero_lt_one.trans_le one
  have entry:=full_scaled (C.localSection d) v o (inv_pos.mpr pos) (threshold N)
    ((inv_le_one₀ pos).mpr one) X
  rw [inv_inv] at entry
  have as_field:(C.S.a m:ℂ)^d*C.O N per (atK C h d m (N,per) z) o X =
      ((r^d:ℝ):ℂ)*(C.localSection d).places
        ((C.labels.level d).scaled (C.path.levels.clock.threshold N)⁻¹ v) o X := by
    change (C.S.a m:ℂ)^d*(((C.S.a N:ℂ)^d)⁻¹*_)=((r^d:ℝ):ℂ)*_
    have factor:((r^d:ℝ):ℂ)=(C.S.a m:ℂ)^d/(C.S.a N:ℂ)^d := by
      change ((((C.S.a m/C.S.a N)^d):ℝ):ℂ)=_
      rw [Complex.ofReal_pow,Complex.ofReal_div,div_pow]
    rw [factor,div_eq_mul_inv,mul_assoc]
  rw [as_field,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg rp _)]
  calc
    _ ≤ r^d*(price (C.localSection d)*(β N)^slots (C.labels.level d)*mass C d v) :=
      mul_le_mul_of_nonneg_left entry (pow_nonneg rp _)
    _ ≤ r^d*(price (C.localSection d)*(β N)^slots (C.labels.level d)*(r*mass C d z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (WilsonReportingUpperChartPrice.bare h aged live z)
        (mul_nonneg (zero_le_one.trans (price_pos _)) (pow_nonneg pos.le _))) (pow_nonneg rp _)
    _ = _ := by change _=price (C.localSection d)*r^(d+1)*(β N)^slots (C.labels.level d)*mass C d z
                rw [pow_succ]; ring

theorem moment (aged:C.ref d ≤ m) (live:m ≤ N) (z:C.label d) (o:Site (C.side N per)) :
    ‖(C.S.a m:ℂ)^d*Wilson.moment (C.beta N per) (C.O N per (atK C h d m (N,per) z) o)‖ ≤
      price (C.localSection d)*(C.S.a m/C.S.a N)^(d+1)*(β N)^slots (C.labels.level d)*mass C d z := by
  unfold Wilson.moment
  rw [←integral_const_mul]
  simpa using norm_integral_le_of_norm_le_const (μ:=law G (C.side N per) (C.beta N per))
    (Eventually.of_forall (field h aged live z o))

theorem near (aged:C.ref d ≤ m) (live:m ≤ N) (z:C.label d) (o:Site (C.side N per))
    (u e:ℕ) (gap:C.S.a m/C.S.a N ≤ (β m)^u) (heat:(β N) ≤ 2*β m)
    (filed:mass C d z ≤ (β m)^e) :
    ‖(C.S.a m:ℂ)^d*Wilson.moment (C.beta N per) (C.O N per (atK C h d m (N,per) z) o)‖ ≤
      price (C.localSection d)*2^slots (C.labels.level d)*(β m)^(u*(d+1)+slots (C.labels.level d)+e) := by
  let k:=slots (C.labels.level d)
  have pos(i:ℕ):0 ≤ β i:= zero_le_one.trans (C.path.levels.fits.delayed i).le
  have ratio:0 ≤ C.S.a m/C.S.a N:=(div_pos (C.S.a_pos _) (C.S.a_pos _)).le
  have c:0 ≤ price (C.localSection d):=zero_le_one.trans (price_pos _)
  have hm:=pos m
  have hn:=pos N
  have cash:0 ≤ mass C d z:=coeff_nonneg z
  apply (moment h aged live z o).trans
  calc
    _ ≤ price (C.localSection d)*((β m)^u)^(d+1)*(2*β m)^k*(β m)^e := by
      gcongr
    _ = _ := by rw [←pow_mul,mul_pow,pow_add,pow_add]; ring

end YM.Integration.WilsonReportingTopEnvelope
