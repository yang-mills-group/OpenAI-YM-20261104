import YM.Integration.WilsonOffsetSourceBasis

/-! Compare the actual signed complex conditional with two separately
supplied real and imaginary source columns. The price includes the untouched
source coefficients. No geometric smallness of the offset is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetMarkComparison
open Function MeasureTheory Lattice RG Wilson Source Labels MSbar.Bulk RGComparison.Core16.Spool
open WilsonOffsetConditionalCharge WilsonOffsetSourceBasis
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} {P:Rep G f}
variable (hk:S.IsKernel P.beta G) (hp:Envelope P.eval) (V:Config G c)

include hk hp
theorem part (X:Config G f→ℂ) (hx:Continuous X) (b:Bool) :
    look b (conditional S P V X) = expect S P V (fun U=>look b (X U)) :=by
  have h : Integrable (fun U:Config G f=>S.density P.beta U V • ((P.eval U:ℂ)*X U)) (prior G f) := StepData.push_slice hk V _ (((Envelope.ofReal_env hp).mulC (Envelope.compactC hx)).integrableC (prior G f))
  cases b
  · change (conditional S P V X).re=_
    simp only [conditional,Complex.div_ofReal_re,expect,StepData.push]
    congr 1
    refine (integral_re h).symm.trans ?_
    apply integral_congr_ae
    filter_upwards with U
    simp [Complex.real_smul,look,mul_left_comm,mul_comm]
  · change (conditional S P V X).im=_
    simp only [conditional,Complex.div_ofReal_im,expect,StepData.push]
    congr 1
    refine (integral_im h).symm.trans ?_
    apply integral_congr_ae
    filter_upwards with U
    simp [Complex.real_smul,look,mul_left_comm,mul_comm]

theorem subtract (X Y:Config G f→ℂ) (hx:Continuous X) (hy:Continuous Y) :
    conditional S P V (fun U=>X U-Y U)=conditional S P V X-conditional S P V Y :=by
  have hZ (Z:Config G f→ℂ) (hw:Continuous Z) :
      Integrable (fun U=>S.density P.beta U V • ((P.eval U:ℂ)*Z U)) (prior G f) :=
    StepData.push_slice hk V _ (((Envelope.ofReal_env hp).mulC (Envelope.compactC hw)).integrableC _)
  simp only [conditional,StepData.push,mul_sub,smul_sub]
  rw [integral_sub (hZ X hx) (hZ Y hy),sub_div]

def paint (W:Bool→ℝ):ℂ := (W false:ℂ)+(W true:ℂ)*Complex.I

theorem one (X:Config G f→ℂ) (hx:Continuous X) (W:Bool→ℝ) (q:ℝ)
    (paid:∀ b, |expect S P V (fun U=>look b (X U))-W b| ≤ q) :
    ‖conditional S P V X-paint W‖ ≤ 2*q :=by
  have hr:=paid false;have hi:=paid true
  rw [←part hk hp V X hx false] at hr
  rw [←part hk hp V X hx true] at hi
  change |(conditional S P V X).re-W false| ≤ q at hr
  change |(conditional S P V X).im-W true| ≤ q at hi
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp [paint]
  linarith

theorem pair {I:Type*} [Fintype I] (x:I→ℂ) (A B:I → Config G f → ℂ)
    (hA:∀ i,Continuous (A i)) (hB:∀ i,Continuous (B i)) (w z:I→Bool→ℝ)
    (ε:ℝ) (wA:∀ i b,|expect S P V (fun U=>look b (A i U))-w i b| ≤ ε)
    (wB:∀ i b,|expect S P V (fun U=>look b (B i U))-z i b| ≤ ε) :
    ‖(conditional S P V (fun U=>∑i,x i*A i U) - conditional S P V (fun U=>∑i,x i*B i U))-
       ∑i,x i*(paint (w i)-paint (z i))‖ ≤ (∑i,‖x i‖)*(4*ε):=by
  classical
  rw [combination hk hp V x A hA,combination hk hp V x B hB,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [show x i*conditional S P V (A i)-x i*conditional S P V (B i)-x i*(paint (w i)-paint (z i))=
      x i*((conditional S P V (A i)-paint (w i))-(conditional S P V (B i)-paint (z i))) by ring,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sub_le ..).trans
  linarith [one hk hp V (A i) (hA i) (w i) ε (wA i),one hk hp V (B i) (hB i) (z i) ε (wB i)]

end YM.Integration.WilsonOffsetMarkComparison
