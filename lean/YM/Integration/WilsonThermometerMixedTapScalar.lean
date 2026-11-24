import YM.Integration.WilsonThermometerMixedEndpoint
import YM.Integration.WilsonThermometerUnitFilingRawSum
import YM.Integration.WilsonThermometerMixedRefund

/-! The two complete auxiliary readings share the filed bank. Their normalized
  difference recovers the previously mixed source under each original older kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedTapScalar
open Filter Finset MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato Marker
open WilsonThermometerMixedAmplitude WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per b j:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" => Config G (R.family.side b per)

theorem purchase {g W B F y:ℝ} (gp:0<g) (F₀:0 ≤ F) (d:ℕ)
    (salary:g^d*W ≤ B)(price:y ≤ W*(g⁻¹)^87*F) :
    g^(d+87)*y ≤ B*F:=by
  have factor:g^(d+87)*(W*(g⁻¹)^87*F)=g^d*W*F:=by
    rw [pow_add,inv_pow]
    field_simp [gp.ne']
  exact ((mul_le_mul_of_nonneg_left price (pow_nonneg gp.le _)).trans_eq factor).trans
    (mul_le_mul_of_nonneg_right salary F₀)

theorem subtract (z v:X→ℂ)(hz:Integrable z (prior G _))(hv:Integrable v (prior G _))(jb:j ≤ b):
    WilsonThermometerUnitFilingCoarse.reading R (N:=N) (z-v) j jb =
      WilsonThermometerUnitFilingCoarse.reading R (N:=N) z j jb -
      WilsonThermometerUnitFilingCoarse.reading R (N:=N) v j jb:=by
  have eqn:z-v=z+(-1:ℂ) • v:=by ext t; simp [sub_eq_add_neg]
  rw [eqn,WilsonThermometerUnitFilingRaw.add R z _ hz (hv.smul _) jb,
    WilsonThermometerUnitFilingRawSum.scaled R (-1) v hv jb]
  ring

theorem original (Q:Poly J) (A Y F:X→Poly J)(N₀:X→ℂ){g:ℝ}(gp:0<g)(p d:ℕ)
    (line:∀U,Line ((g:ℂ)^(p+d)) (A U) (Y U) (F U))
    (jb:j ≤ b)(B₀ B₁:ℝ) :
    let blank:=fun U=>WilsonThermometerMixedRefund.reading Q (A U)-N₀ U
    let large:=fun U=>WilsonThermometerMixedRefund.reading Q (F U)-N₀ U
    let full:=fun U=>WilsonThermometerMixedRefund.reading Q (Y U)-WilsonThermometerMixedRefund.reading Q (A U)
    Integrable blank (prior G _) → Integrable large (prior G _) →
    g^d*‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) blank j jb‖ ≤ B₀ →
    g^d*‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) large j jb‖ ≤ B₁ →
    ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) full j jb‖ ≤ g^p*(B₁+B₀):=by
  intro blank large full erase grow blankFee gross
  have same:full=((g:ℂ)^(p+d)) • (large-blank):=by
    ext U
    have eqn:=WilsonThermometerMixedRefund.filed (line U) Q
    dsimp only [full,blank,large,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    rw [eqn]; ring
  rw [same,WilsonThermometerUnitFilingRawSum.scaled R _ _ (grow.sub erase) jb,
    subtract R large blank grow erase jb,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp,pow_add,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg gp.le p)
  exact (mul_le_mul_of_nonneg_left (norm_sub_le ..) (pow_nonneg gp.le _)).trans
    ((mul_add ..).le.trans (add_le_add gross blankFee))

end YM.Integration.WilsonThermometerMixedTapScalar
end
