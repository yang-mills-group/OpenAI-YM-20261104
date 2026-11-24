import YM.Integration.WilsonPositionProgramTrialPublicJointRoom

/-! The single before-cutoff spectral income after all measured angular test amplitudes have been normalized. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCredit
open RG WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Lattice Precision MeasureTheory
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonPositionProgramTrialPublicJointSpectrum (spectrum color mode)
open WilsonPositionProgramTrialPublicJointRoom (base width)
open scoped Classical BigOperators Topology SchwartzMap
variable {n:ℕ}

def price (Φ:Test n)(D:Fin n→ℕ)(ξ:Points n)(c:Fin n→Bool):ℂ:=
  spectrum Φ ξ*(∏i,color (c i))*((width ξ ^ (∑i,D i):ℝ):ℂ)

theorem faces (Φ:Test n)(D:Fin n→ℕ)(ξ:Points n)(c:Fin n→Bool):
    ‖price Φ D ξ c‖=width ξ ^ (∑i,D i)*‖spectrum Φ ξ‖:=by
  have colors (i:Fin n):‖color (c i)‖=1:=by cases q:c i <;> simp [color]
  have pos:0≤width ξ:=zero_le_one.trans (WilsonPositionProgramTrialPublicJointRoom.big ξ)
  simp only [price,norm_mul,norm_prod,colors,Finset.prod_const_one,one_mul,Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg pos _),mul_comm]

theorem income (Φ:Test n)(D:Fin n→ℕ)(c:Fin n→Bool):Integrable (fun ξ:Points n=>price Φ D ξ c):=by
  let h:=∑i,D i
  have smooth:Continuous (fun ξ:Points n=>price Φ D ξ c):=by
    unfold price width
    fun_prop
  have basep:0≤base:=by unfold base;positivity
  apply ((WilsonPositionProgramTrialPublicJointSpectrum.moment Φ h).const_mul (base^h)).mono' smooth.aestronglyMeasurable
  filter_upwards [] with ξ
  rw [faces]
  have bound:(max 1 ‖ξ‖)^h≤1+‖ξ‖^h:=by
    rcases le_total ‖ξ‖ 1 with hξ|hξ
    · rw [max_eq_left hξ,one_pow];exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · rw [max_eq_right hξ];exact le_add_of_nonneg_left zero_le_one
  change (base*max 1 ‖ξ‖)^h*‖spectrum Φ ξ‖≤base^h*((1+‖ξ‖^h)*‖spectrum Φ ξ‖)
  rw [mul_pow,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (pow_nonneg basep _)) (norm_nonneg _)

theorem paid (Φ:Test n)(D:Fin n→ℕ):Integrable (fun ξ:Points n=>∑c:Fin n→Bool,‖price Φ D ξ c‖):=
  integrable_finsetSum _ (fun c _=>(income Φ D c).norm)

theorem restored {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ x:Points n)(c:Fin n→Bool):
    (∏i,(mode T ξ c i).ψ.val (physical (x i)))=
      width ξ^(∑i,D i)*(∏i,(WilsonPositionProgramTrialPublicJointRoom.normalized T ξ c i).ψ.val (physical (x i))):=by
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have pos:width ξ ^ D i≠0:=pow_ne_zero _ (lt_of_lt_of_le zero_lt_one (WilsonPositionProgramTrialPublicJointRoom.big ξ)).ne'
  change _=width ξ^D i*((width ξ^D i)⁻¹ * _)
  rw [←mul_assoc,mul_inv_cancel₀ pos,one_mul]

theorem original (Φ:Test n){D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))
    (window:∀x:Points n,Φ x≠0→∏i,(T i).ψ.val (physical (x i))=1):
    Integrable (fun ξ:Points n=>∑c:Fin n→Bool,‖price Φ D ξ c‖) ∧
    ∀x:Points n,Φ x=∫ξ:Points n,∑c:Fin n→Bool,price Φ D ξ c *
      ((∏i,(WilsonPositionProgramTrialPublicJointRoom.normalized T ξ c i).ψ.val (physical (x i)):ℝ):ℂ):=by
  refine ⟨paid Φ D,?_⟩
  intro x
  rw [WilsonPositionProgramTrialPublicJointSpectrum.original Φ T window x]
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply Finset.sum_congr rfl
  intro c _
  rw [restored T ξ x c,Complex.ofReal_mul]
  exact (mul_assoc ..).symm

end YM.Integration.WilsonPositionProgramTrialPublicJointCredit
end
