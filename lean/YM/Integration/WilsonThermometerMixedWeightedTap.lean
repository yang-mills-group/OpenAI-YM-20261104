import YM.Integration.WilsonThermometerMixedTapScalar
import YM.Integration.WilsonThermometerMixedTandemReading
import YM.Integration.WilsonThermometerMixedEndpoint
import YM.Integration.WilsonThermometerUnitFilingRawSum
import YM.Integration.WilsonThermometerMixedRefund

/-! The two complete auxiliary readings share the filed bank. Their normalized
  difference recovers the previously mixed source under each original older kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedWeightedTap
open Filter Finset MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato Marker
open WilsonThermometerMixedAmplitude WilsonThermometerCenteredAlgebra
open WilsonGeometricSignedCapture
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per b j:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" => Config G (R.family.side b per)

theorem filed {q:ℂ} {A Y F:Poly J} (line:Line q A Y F) (c:(J).Mode→ℂ) :
    take c Y - take c A=q*(take c F-take c A) := by
  unfold take
  rw [←sum_sub_distrib,←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro s _
  have e:=congrArg (fun t:Poly J=>t.part s) line.value
  change Y.part s=A.part s+q*(F.part s-A.part s) at e
  rw [e]
  ring

theorem original (c:(J).Mode→ℂ) (A Y F:X→Poly J)(N₀:X→ℂ){g:ℝ}(gp:0<g)(p d:ℕ)
    (line:∀U,Line ((g:ℂ)^(p+d)) (A U) (Y U) (F U))
    (jb:j ≤ b)(B₀ B₁:ℝ) :
    let blank:=fun U=>take c (A U)-N₀ U
    let large:=fun U=>take c (F U)-N₀ U
    let full:=fun U=>take c (Y U)-take c (A U)
    Integrable blank (prior G _) → Integrable large (prior G _) →
    g^d*‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) blank j jb‖ ≤ B₀ →
    g^d*‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) large j jb‖ ≤ B₁ →
    ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) full j jb‖ ≤ g^p*(B₁+B₀):=by
  intro blank large full erase grow blankFee gross
  have same:full=((g:ℂ)^(p+d)) • (large-blank):=by
    ext U
    have eqn:=filed (line U) c
    dsimp only [full,blank,large,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    rw [eqn]; ring
  rw [same,WilsonThermometerUnitFilingRawSum.scaled R _ _ (grow.sub erase) jb,
    WilsonThermometerMixedTapScalar.subtract R large blank grow erase jb,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp,pow_add,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg gp.le p)
  exact (mul_le_mul_of_nonneg_left (norm_sub_le ..) (pow_nonneg gp.le _)).trans
    ((mul_add ..).le.trans (add_le_add gross blankFee))

end YM.Integration.WilsonThermometerMixedWeightedTap
end
