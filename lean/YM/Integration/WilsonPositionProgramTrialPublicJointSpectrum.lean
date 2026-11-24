import YM.Integration.WilsonPositionProgramTrialPublicCellCohort
import YM.Integration.WilsonSeparatedPrefixMovingJointExpansion

/-! A compact complex test of all public positions expanded in real, compact Rarity sheets on the filed rectangle. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSpectrum
open RG WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Precision Lattice MeasureTheory FourierTransform
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid character physical)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonSeparatedPrefixMovingJointWaves (sheet wave)
open scoped Classical BigOperators Topology FourierTransform SchwartzMap RealInnerProductSpace
variable {n:ℕ}

def spectrum (Φ:Test n):𝓢(Points n,ℂ):=𝓕 (Φ.hasCompactSupport.toSchwartzMap Φ.contDiff)

theorem moment (Φ:Test n)(a:ℕ):
    Integrable (fun ξ:Points n=>(1+‖ξ‖^a)*‖spectrum Φ ξ‖):=by
  apply ((spectrum Φ).integrable.norm.add ((spectrum Φ).integrable_pow_mul volume a)).congr
  filter_upwards [] with ξ
  simp only [Pi.add_apply,add_mul,one_mul]

theorem character_prod (ξ x:Points n):
    Complex.exp (((2*Real.pi*inner ℝ ξ x:ℝ):ℂ)*Complex.I)=∏i,character (ξ i) (physical (x i)):=by
  simp only [character,ContinuousLinearEquiv.symm_apply_apply,←Complex.exp_sum,PiLp.inner_apply]
  congr 1
  push_cast
  rw [Finset.mul_sum,Finset.sum_mul]

theorem inverse (Φ:Test n)(x:Points n):
    Φ x=∫ξ:Points n,spectrum Φ ξ*(∏i,character (ξ i) (physical (x i))):=by
  let f:𝓢(Points n,ℂ):=Φ.hasCompactSupport.toSchwartzMap Φ.contDiff
  have eq:(𝓕⁻ (spectrum Φ):𝓢(Points n,ℂ))=f:=FourierTransform.fourierInv_fourier_eq _
  change f x=_
  nth_rw 1 [←eq]
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  change Complex.exp (((2*Real.pi*inner ℝ ξ x:ℝ):ℂ)*Complex.I)*spectrum Φ ξ=_
  rw [character_prod,mul_comm]

def color (a:Bool):ℂ:=if a then Complex.I else 1

theorem split {D:ℕ}(T:Rarity D)(ξ:Euclid)(x:Point4):
    ((T.ψ.val x:ℝ):ℂ)*character ξ x=∑c:Bool,color c*((sheet T (angle ξ) c).ψ.val x:ℂ):=by
  have re:(character ξ x).re=Real.cos (angle ξ x):=Complex.exp_ofReal_mul_I_re _
  have im:(character ξ x).im=Real.sin (angle ξ x):=Complex.exp_ofReal_mul_I_im _
  rw [Fintype.sum_bool]
  apply Complex.ext <;> simp [color,sheet,WilsonSeparatedPrefixMovingJointWaves.wave,Complex.mul_re,Complex.mul_im,re,im] <;>
    simp only [←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.ofReal_re,true_or]

def mode {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ:Points n)(c:Fin n→Bool)(i:Fin n):Rarity (D i):=
  sheet (T i) (angle (ξ i)) (c i)

theorem words {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ x:Points n):
    ((∏i,(T i).ψ.val (physical (x i)):ℝ):ℂ)*(∏i,character (ξ i) (physical (x i)))=
      ∑c:Fin n→Bool,(∏i,color (c i))*((∏i,(mode T ξ c i).ψ.val (physical (x i)):ℝ):ℂ):=by
  push_cast
  rw [←Finset.prod_mul_distrib]
  simp_rw [split]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun c _=>Finset.prod_mul_distrib)

theorem original (Φ:Test n){D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))
    (window:∀x:Points n,Φ x≠0→∏i,(T i).ψ.val (physical (x i))=1):
    ∀x:Points n,Φ x=∫ξ:Points n,∑c:Fin n→Bool,(spectrum Φ ξ*(∏i,color (c i)))*
      ((∏i,(mode T ξ c i).ψ.val (physical (x i)):ℝ):ℂ):=by
  intro x
  let mask:ℂ:=((∏i,(T i).ψ.val (physical (x i)):ℝ):ℂ)
  have support:Φ x=mask*Φ x:=by
    by_cases zero:Φ x=0
    · simp [zero]
    · have one:mask=1:=by change (((∏i, (T i).ψ.val (physical (x i)):ℝ)):ℂ)=1; rw [window x zero]; rfl
      rw [one,one_mul]
  nth_rw 1 [support,inverse Φ x]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  calc
    mask*(spectrum Φ ξ * _) = spectrum Φ ξ*(mask*(∏i,character (ξ i) (physical (x i)))):=by ring
    _=_:=by rw [show mask*(∏i,character (ξ i) (physical (x i)))=_ from words T ξ x,Finset.mul_sum]
            exact Finset.sum_congr rfl (fun c _=>(mul_assoc ..).symm)

end YM.Integration.WilsonPositionProgramTrialPublicJointSpectrum
end
