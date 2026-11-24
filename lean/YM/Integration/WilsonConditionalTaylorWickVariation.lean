import YM.Integration.WilsonConditionalTaylorWick
import YM.Integration.WilsonMovingExponentialConvention

/-! Change of the *actual* earlier action and entering numerator in one
normalized Wick step. The action correction is a connected insertion in
the older Gaussian gas. Both authentic, field-dependent vacuum factors stay
in the identity at a nonzero external coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWickVariation
open Matrix PowerSeries FormalBulk08 FormalBulk08.Series MSbar MSbar.Cacao MSbar.Bakery
open WilsonMovingNormalizedBank WilsonConditionalTaylorWick
open scoped Classical BigOperators Matrix
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (B:Matrix J I ℝ) (x:View J) (Q:Matrix I I ℝ)

def excess (f g:PowerSeries (MvPolynomial J ℝ)):=Spring (f-g)-1

def mass (f:PowerSeries (MvPolynomial J ℝ)):=contract B x Q (Spring f)
def raw (f T:PowerSeries (MvPolynomial J ℝ)):=contract B x Q (T*Spring f)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem shifted {f g:PowerSeries (MvPolynomial J ℝ)} (hf:Kind f) (hg:Kind g):
    Spring f=(1+excess f g)*Spring g:=by
  have zero:Kind (f-g):=by rw [Kind,map_sub,show coeff 0 f=0 from hf,show coeff 0 g=0 from hg,sub_zero]
  rw [excess,show 1+(Spring (f-g)-1)=Spring (f-g) by ring,←WilsonMovingExponentialConvention.exp _ zero,←WilsonMovingExponentialConvention.exp _ hg,
    ←WilsonMovingExponentialConvention.exp _ hf,expan_mul zero hg,sub_add_cancel]

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem linear (T U:PowerSeries (MvPolynomial J ℝ)):
    contract B x Q (T-U)=contract B x Q T-contract B x Q U:=by simp only [contract,map_sub]

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem action {f g:PowerSeries (MvPolynomial J ℝ)} (hf:Kind f) (hg:Kind g) (T:PowerSeries (MvPolynomial J ℝ)):
    raw B x Q f T-raw B x Q g T=raw B x Q g (T*excess f g):=by
  unfold raw
  rw [←linear]
  apply congrArg (contract B x Q)
  rw [shifted hf hg]
  ring

omit [Fintype J] [DecidableEq J] in
theorem normalized (sym:Q.IsSymm) (pd:Q.PosDef) (f T:PowerSeries (MvPolynomial J ℝ)) (hf:Kind f):
    quotient B x Q f T * mass B x Q f=raw B x Q f T:=by
  have one:coeff 0 (mass B x Q f)=1:=by
    change coeff 0 (Series.beam _ _)=1
    rw [←WilsonMovingWickCoefficient.complete B x Q sym pd.posSemidef (Spring f)]
    exact WilsonMovingGaussianResponse.first Q B x (Spring f) (covers hf)
  have bill:=PowerSeries.mul_invOfUnit (mass B x Q f) 1 (by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,one];rfl)
  calc
    _=raw B x Q f T*(mass B x Q f*invOfUnit (mass B x Q f) 1):=by unfold quotient raw mass;ring
    _=raw B x Q f T:=by rw [bill,mul_one]

omit [Fintype J] [DecidableEq J] in
theorem connected (sym:Q.IsSymm) (pd:Q.PosDef) (f g T U:PowerSeries (MvPolynomial J ℝ)) (hf:Kind f) (hg:Kind g):
    (quotient B x Q f T-quotient B x Q g U)*mass B x Q f*mass B x Q g =
      raw B x Q f (T-U)*mass B x Q g+
      (raw B x Q g (U*excess f g)*mass B x Q g-raw B x Q g U*raw B x Q g (excess f g)):=by
  have left:=normalized B x Q sym pd f T hf
  have right:=normalized B x Q sym pd g U hg
  have paired:=action B x Q hf hg U
  have divided:mass B x Q f-mass B x Q g=raw B x Q g (excess f g):=by
    simpa only [raw,one_mul,mass] using action B x Q hf hg 1
  have signed:raw B x Q f (T-U)=raw B x Q f T-raw B x Q f U:=by
    unfold raw;rw [sub_mul,linear]
  rw [signed,←paired,←divided]
  calc
    _=(quotient B x Q f T*mass B x Q f)*mass B x Q g-(quotient B x Q g U*mass B x Q g)*mass B x Q f:=by ring
    _=_:=by rw [left,right];ring

end YM.Integration.WilsonConditionalTaylorWickVariation
end

