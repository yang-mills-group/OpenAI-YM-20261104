import YM.Integration.WilsonOriginalObservedRoseVaneCaliber
import YM.Integration.WilsonOriginalObservedRoseStoppedSalary

/-! Finance a prebooked source exponent using the actual kinetic coupling on the prescribed older window. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalObservedRosePublicCurrency
open Function Filter Lattice Wilson RG Real PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalObservedRoseStoppedSalary (stop)
open scoped Topology Classical
variable {G:Gauge}

theorem clock (R:Run G)(simple:G.Simple)(L E:ℕ):
    ∀ᶠv:ℕ in atTop,∀N per K:ℕ,v≤K → K≤N →
    R.family.S.scale K-R.family.S.scale v≤L*Real.log (R.family.path.levels.clock.hatBeta v) →
    (R.family.path.levels.clock.hatBeta K)^E≤(4:ℝ)^E*((regulatorRun R.family N per v)⁻¹)^(2*E):=by
  filter_upwards [WilsonReportingAbsoluteInletCoordinates.clocks R simple L] with v prior N per K vk kn span
  let H:=R.family.path.levels.clock.hatBeta
  let g:=regulatorRun R.family N per v
  have hv:0<H v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have hk:0≤H K:=zero_le_one.trans (R.family.path.levels.fits.delayed K).le
  have mono:=WilsonReflectedOpticalStock.monotone R simple vk
  have corridor:=prior vk (span.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hv mono) (Nat.cast_nonneg _)))
  have band:H v/2≤R.family.path.β N per v:=(R.makes.wilson.represents N per v (vk.trans kn)).band.1
  have bp:0≤R.family.path.β N per v:=by linarith
  have unit:(g⁻¹)^2=R.family.path.β N per v:=by
    change (((Real.sqrt _)⁻¹)⁻¹)^2=_
    rw [inv_inv,Real.sq_sqrt bp]
  have paid:H K≤4*(g⁻¹)^2:=by rw [unit];linarith
  simpa only [mul_pow,←pow_mul] using pow_le_pow_left₀ hk paid E

theorem returned (P D E A h:ℕ)(bound:h≤14){r g M B X τ C gap:ℝ}
    (rp:0≤r)(pos:0<g)(small:g≤1)(one:1≤g⁻¹)(bpos:0≤B)(xp:0≤X)(tp:0≤τ)(cp:0≤C)
    (top:r^h*M≤B*(g⁻¹)^E*(g⁻¹)^(A*h+1))(test:τ≤X*(g⁻¹)^D)
    (gross:gap≤M*(τ*(C*g^(stop P (D+E) A))))(liquid:B*X*C≤g⁻¹):
    r^h*gap≤g^P:=by
  let z:=g⁻¹
  have zp:0<z:=inv_pos.mpr pos
  have reserve:1≤z^12:=one_le_pow₀ one
  have billed:r^h*(M/z^E)≤B*z^12*z^(A*h+1):=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (pow_pos zp _)).mpr
    calc r^h*M≤B*z^E*z^(A*h+1):=top
         _≤B*z^E*z^(A*h+1)*z^12:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg bpos (pow_nonneg zp.le _)) (pow_nonneg zp.le _)) reserve
         _=B*z^12*z^(A*h+1)*z^E:=by ring
  have total:τ*z^E≤X*z^(D+E):=by
    rw [pow_add,←mul_assoc];exact mul_le_mul_of_nonneg_right test (pow_nonneg zp.le _)
  apply WilsonOriginalObservedRoseStoppedSalary.original P (D+E) A h bound rp pos small bpos xp
    (mul_nonneg tp (pow_nonneg zp.le E)) cp billed total _ liquid
  calc gap≤M*(τ*(C*g^(stop P (D+E) A))):=gross
       _=(M/z^E)*(τ*z^E*(C*g^(stop P (D+E) A))):=by field_simp [zp.ne']

end YM.Integration.WilsonOriginalObservedRosePublicCurrency
end
