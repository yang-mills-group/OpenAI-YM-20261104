import YM.Integration.WilsonThermometerOccupiedPolynomial

/-! Recover the ordinary occupied contribution from four genuine real hard intakes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedInterpolation
open Marker WilsonThermometerOccupiedPolynomial MeasureTheory
open scoped Classical BigOperators
def w₁ (q:ℝ):ℝ:=q*(q-2)*(q-3)/2
def w₂ (q:ℝ):ℝ:= -(q*(q-1)*(q-3)/2)
def w₃ (q:ℝ):ℝ:=q*(q-1)*(q-2)/6

def fitted {A:Type*} [AddCommGroup A] [Module ℂ A] (q:ℝ) (a b c d:A):A:=
  a+(w₁ q:ℂ) • (b-a)+(w₂ q:ℂ) • (c-a)+(w₃ q:ℂ) • (d-a)

theorem readings {R:Census (Fin 3)} {F:ℂ→Poly R} (C:Cubic F) (q T:ℝ) (inv:q*T=1):
    F 1=fitted q (F 0) (F T) (F (2*T)) (F (3*T)):=by
  ext1 s
  change (F 1).part s=(F 0).part s+(w₁ q:ℂ)*((F T).part s-(F 0).part s)+
    (w₂ q:ℂ)*((F (2*T)).part s-(F 0).part s)+(w₃ q:ℂ)*((F (3*T)).part s-(F 0).part s)
  have unit:(q:ℂ)*(T:ℂ)=1:=by exact_mod_cast inv
  conv_lhs => rw [←unit]
  simp only [read C, w₁,w₂,w₃, Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_sub,
    Complex.ofReal_neg,Complex.ofReal_ofNat,Complex.ofReal_one]
  ring

theorem mass (q:ℝ) (pos:0≤q) (small:q≤1) :
    |w₁ q|+|w₂ q|+|w₃ q| ≤ 5*q :=by
  have a:|q-1|≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
  have b:|q-2|≤2:=abs_le.mpr ⟨by linarith,by linarith⟩
  have c:|q-3|≤3:=abs_le.mpr ⟨by linarith,by linarith⟩
  have one:|w₁ q| ≤ q*2*3/2:=by
    simp only [w₁,abs_div,abs_mul,abs_of_nonneg pos,abs_of_nonneg (by norm_num:0 ≤ (2:ℝ))]
    gcongr
  have two:|w₂ q| ≤ q*1*3/2:=by
    simp only [w₂,abs_neg,abs_div,abs_mul,abs_of_nonneg pos,abs_of_nonneg (by norm_num:0 ≤ (2:ℝ))]
    gcongr
  have three:|w₃ q| ≤ q*1*2/6:=by
    simp only [w₃,abs_div,abs_mul,abs_of_nonneg pos,abs_of_nonneg (by norm_num:0 ≤ (6:ℝ))]
    gcongr
  linarith

theorem bill {A:Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (q:ℝ) (pos:0≤q) (small:q≤1) (a b c d:A) (K:ℝ)
    (p:‖a‖≤K) (pb:‖b‖≤K) (pc:‖c‖≤K) (pd:‖d‖≤K):
    ‖fitted q a b c d-a‖ ≤ 10*K*q:=by
  have d₁:‖b-a‖≤2*K:=(norm_sub_le b a).trans (by linarith)
  have d₂:‖c-a‖≤2*K:=(norm_sub_le c a).trans (by linarith)
  have d₃:‖d-a‖≤2*K:=(norm_sub_le d a).trans (by linarith)
  let u:=(w₁ q:ℂ) • (b-a)
  let v:=(w₂ q:ℂ) • (c-a)
  let w:=(w₃ q:ℂ) • (d-a)
  have change:fitted q a b c d-a=u+v+w:=by dsimp only [fitted,u,v,w];abel
  rw [change]
  calc
    _ ≤ ‖u‖+‖v‖+‖w‖ := (norm_add_le _ _).trans (by linarith only [norm_add_le u v])
    _ ≤ |w₁ q| * (2*K)+|w₂ q| * (2*K)+|w₃ q| * (2*K) := by
      dsimp only [u,v,w]
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      gcongr
    _ = (|w₁ q|+|w₂ q|+|w₃ q|)*(2*K) := by ring
    _ ≤ _ :=by have := mul_le_mul_of_nonneg_right (mass q pos small) (by linarith [norm_nonneg a]:0≤2*K); linarith

theorem summed {ι:Type*} {A:Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (q:ℝ) (a b c d:ι→A) (ha:Summable a) (hb:Summable b) (hc:Summable c) (hd:Summable d):
    (∑'i,fitted q (a i) (b i) (c i) (d i)) =
      fitted q (∑'i,a i) (∑'i,b i) (∑'i,c i) (∑'i,d i):=by
  exact (((ha.hasSum.add ((hb.hasSum.sub ha.hasSum).const_smul (w₁ q:ℂ))).add
    ((hc.hasSum.sub ha.hasSum).const_smul (w₂ q:ℂ))).add ((hd.hasSum.sub ha.hasSum).const_smul (w₃ q:ℂ))).tsum_eq

end YM.Integration.WilsonThermometerOccupiedInterpolation
