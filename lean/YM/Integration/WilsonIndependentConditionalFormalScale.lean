import YM.Integration.WilsonIndependentConditionalFiniteClock

/-! The full formal conditional uses precisely the thermal dilation of the
free coordinates on the genuine Wick law. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentConditionalFormalScale
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior
open scoped Classical BigOperators MatrixOrder
variable {U Y Z:Type}[Fintype U][DecidableEq U][Fintype Y][Fintype Z]

def leg (A:Cost)(i:U):Ink (U⊕Z):=holdUp U (soil (U:=Z) A)*path (.inl i)

omit [Fintype Z] in
private theorem jac (A:Cost):
    (motionJ (leg (U:=U) (Z:=Z) A)).det=holdUp U (soil (U:=Z) (A^Fintype.card U)):=by
  have mat:motionJ (leg (U:=U) (Z:=Z) A)=
      Matrix.diagonal (fun _:U=>holdUp U (soil (U:=Z) A)):=by
    ext i j
    simp only [motionJ,Matrix.of_apply,leg,Derivation.leibniz,up_vacant,
      smul_eq_mul,brush_path,Matrix.diagonal_apply]
    split <;> simp_all
  rw [mat,Matrix.det_diagonal,Finset.prod_const,Finset.card_univ,map_pow,map_pow]

omit [DecidableEq U] [Fintype Y] [Fintype Z] in
private theorem body (K:Matrix U U ℝ)(W:Y→Ink Z)(A:Cost):
    reroll W (leg (U:=U) (Z:=Z) A) (bodyQ Y K)=
    (holdUp U (soil (U:=Z) A))^2*bodyQ Z K:=by
  let a:=holdUp U (soil (U:=Z) A)
  let T:=reroll W (leg (U:=U) (Z:=Z) A)
  have sr (k:ℝ)(q:Ink (U⊕Y)):T (k • q)=k • T q:=train_smul (Sum.elim (leg A) (holdUp U ∘ W)) k q
  have pin (i:U):T (path (.inl i))=a*path (.inl i):=train_path (Sum.elim (leg A) (holdUp U ∘ W)) (.inl i)
  have row (i:U):T (slopeQ Y K i)=a*slopeQ Z K i:=by
    simp only [slopeQ,map_sum,sr,pin,Finset.mul_sum,mul_smul_comm]
  change T _=a^2*_
  simp only [bodyQ,sr,map_sum,map_mul,pin,row,Finset.mul_sum,mul_smul_comm]
  apply congr_arg (fun x:Ink (U⊕Z)=>(1/2:ℝ) • x)
  refine Finset.sum_congr rfl fun i _=>?_
  ring

def thermal (K:Matrix U U ℝ)(A:Cost):Ink (U⊕Z):=
  raiseE ((1-holdUp U (soil (U:=Z) A)^2)*bodyQ Z K)

theorem original (K H:Matrix U U ℝ)(hk:K.transpose=K)(hh:H.transpose=H)(inv:K*H=1)
    (A:Cost)(unit:constantCoeff A=1)(W:Y→Ink Z)(p:Ink (U⊕Y)):
    Wick Z H (thermal K A * reroll W (leg A) p)*soil (A^Fintype.card U)=
      train W (Wick Y H p):=by
  have lead (i:U):constantCoeff (leg (U:=U) (Z:=Z) A i)=
    constantCoeff (noiseLine (Y:=Z) (1:Matrix U U ℝ) i):=by
    rw [unit_pin,leg,map_mul,holdUp,soil,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_map,coeff_zero_eq_constantCoeff_apply,unit,map_one,map_one,one_mul]
  have motion:=W_covariance (Y:=Y) (Z:=Z) (N:=K) hh hk inv hh p (1:Matrix U U ℝ)
    (by simp) (by simp) (by simp) (leg A) W lead
  have cash:bodyQ Z K-reroll W (leg A) (bodyQ Y K)=
      (1-holdUp U (soil (U:=Z) A)^2)*bodyQ Z K:=by rw [body];ring
  simp only [cash,jac,Matrix.det_one,realS,map_one,one_mul] at motion
  rw [←W_param]
  apply Eq.trans _ motion
  apply congr_arg (Wick Z H)
  exact mul_comm _ _

variable {G:Gauge}{c f:Lattice.Side}(S:RG.StepData c f)(T:Tree.Forest S.ratio)
  (H:FreeResolvent.FaceRow)(Q:Matrix (Exterior.Body 1 f) (Exterior.Body 1 c) ℝ)

theorem planted (hf:(treeMatrix G S T H).PosDef)(A:Cost)(unit:constantCoeff A=1)
    (W:Woods G c→Ink Z)(Ñ:ChartRatio G)(P w:PChart G f):
    let D:=raiseE (shot S T Q Ñ P)
    let x:=loom (camSlice G S T (extractV G S T Q)) (flash w)
    let heat:=Wick Z (treeInverse G S T H 0)
    let turn:=reroll W (leg (U:=Active G T) A)
    let burn:=thermal (Z:=Z) (treeMatrix G S T H) A
    let cash:=soil (U:=Z) (A^Fintype.card (Active G T))
    heat (burn*turn D)*cash=train W (inside S T H Q Ñ P) ∧
      heat (burn*turn (D*x))*cash=train W (insideMark S T H Q Ñ P w):=by
  dsimp only
  have sym:(treeMatrix G S T H).transpose=treeMatrix G S T H:= Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
  have hi:treeMatrix G S T H*treeInverse G S T H 0=1:=by
    simp only [treeInverse,resolve,zero_smul,add_zero]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne')
  have hj:(treeInverse G S T H 0).transpose=treeInverse G S T H 0:=by
    simp only [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,sym]
  exact ⟨original _ _ sym hj hi A unit W _,original _ _ sym hj hi A unit W _⟩

end YM.Integration.WilsonIndependentConditionalFormalScale
