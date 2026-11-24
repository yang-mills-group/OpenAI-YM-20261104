import YM.Integration.WilsonIndependentSpoutSchurFrame

/-! On the true finite completed square, the held quadratic factor and the
determinant are common to the vacuum and every planted ordinary face. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutSchurVote
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior Next.Free
open WilsonIndependentSpoutSchurFrame WilsonIndependentSpoutThermalChange
open scoped Classical BigOperators MatrixOrder
variable {U V:Type}

def bias (A:Cost)(q:Ink U):Ink U:=(1-soil A⁻¹^2)*q

theorem soil_head (A:Cost):constantCoeff (soil (U:=U) A)=MvPolynomial.C (constantCoeff A):=by
  rw [soil,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply]

theorem zero (A:Cost)(unit:constantCoeff A=1)(q:Ink U):
    constantCoeff (bias A q)=0:=by
  rw [bias,map_mul,map_sub,map_one,map_pow,soil_head,constantCoeff_inv,unit,inv_one,map_one,
    one_pow,sub_self,zero_mul]

theorem keep (A:Cost)(q:Ink V):holdUp U (bias A q)=bias A (holdUp U q):=by
  rw [bias,map_mul,map_sub,map_one,map_pow,held_cash,bias]

theorem passed {R S:Type*}[CommRing R][CommRing S]
    (T:PowerSeries R→+*PowerSeries S)(h:constantCoeff (T X)=0)
    {p:PowerSeries R}(z:constantCoeff p=0):constantCoeff (T p)=0:=
  X_dvd_iff.mp ((X_dvd_iff.mpr h).trans (map_dvd T (X_dvd_iff.mpr z)))

variable {G:Gauge}{c f:Lattice.Side}(S:StepData c f)(T:Forest S.ratio)
  (H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

theorem original (A:Cost)(unit:constantCoeff A=1){Ñ:ChartRatio G}{P:PChart G f}
    (p:shellK 2 P)(base:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G)
    (hu:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f)
    (ratio:LocalRatio Ñ)(hf:(treeMatrix G S T H).PosDef)(w:Ink (Active G T⊕Woods G c)):
    let heat:=Wick (Woods G c) (treeInverse G S T H 0)
    let cash:=soil (U:=Woods G c) ((A⁻¹)^Fintype.card (Active G T))
    heat (raiseE (field S T H Y Q A Ñ P)*redo A w)*cash=
      raiseE (bias A (orbC (precisionC G c Y)))*
        redo A (heat (raiseE (shot S T Q Ñ P)*w)):=by
  dsimp only
  let K:=treeMatrix G S T H
  let C:=treeInverse G S T H 0
  let u:=shot S T Q Ñ P
  let side:=bias A (orbC (precisionC G c Y))
  let n:=bias A (bodyQ (Woods G c) K)
  have split:field S T H Y Q A Ñ P=(n+redo A u)+holdUp (Active G T) side:=by
    rw [WilsonIndependentSpoutSchurFrame.original S T H Y Q A unit p base hz hu hs]
    change _=(_+redo A (shot S T Q Ñ P))+holdUp (Active G T) (bias A _)
    rw [keep]
    simp only [n,bias,K]
    ring
  have hout:constantCoeff (redo (U:=Active G T⊕Woods G c) A X)=0:=by rw [redo_X];simp
  have hu₀:constantCoeff u=0:=by
    change constantCoeff (shot S T Q Ñ P)=0
    rw [shot,loom,←coeff_zero_eq_constantCoeff_apply,
    coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S ratio),map_zero]
  have hside:constantCoeff side=0:=zero A unit _
  have hn:constantCoeff n=0:=zero A unit _
  have hhold:constantCoeff (holdUp (Active G T) (X:Ink (Woods G c)))=0:=by simp [holdUp]
  have hST:constantCoeff (holdUp (Active G T) side)=0:=passed _ hhold hside
  have hnu:constantCoeff (n+redo A u)=0:=by rw [map_add,hn,passed _ hout hu₀,add_zero]
  have noiseEq:WilsonIndependentConditionalFormalScale.thermal K A⁻¹=raiseE n:=by
    unfold WilsonIndependentConditionalFormalScale.thermal n bias
    rw [held_cash]
  have factor:raiseE (field S T H Y Q A Ñ P)*redo A w=
      (WilsonIndependentConditionalFormalScale.thermal K A⁻¹*redo A (raiseE u*w))*
        holdUp (Active G T) (raiseE side):=by
    rw [noiseEq,split,raise_add hnu hST,raise_add hn (passed _ hout hu₀),map_mul,raise_map _ hout hu₀,
      raise_map _ hhold hside]
    ring
  have sk:K.transpose=K:=Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
  have inv:K*C=1:=by
    simp only [C,treeInverse,resolve,zero_smul,add_zero]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne')
  have sh:C.transpose=C:=by simp only [C,treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,show (treeMatrix G S T H).transpose=treeMatrix G S T H from sk]
  rw [factor,W_param,mul_right_comm,WilsonIndependentSpoutDilatedVote.original K C sk sh inv A unit]
  exact mul_comm _ _

end YM.Integration.WilsonIndependentSpoutSchurVote
