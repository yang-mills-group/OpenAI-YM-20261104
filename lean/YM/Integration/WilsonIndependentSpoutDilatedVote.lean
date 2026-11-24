import YM.Integration.WilsonIndependentConditionalFormalScale
import YM.Integration.WilsonIndependentSpoutThermalChange

/-! Complete both substitutions on the same conditional law, before taking
the normalized marked response. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutDilatedVote
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior
open WilsonIndependentConditionalFormalScale WilsonIndependentSpoutThermalChange
open scoped Classical BigOperators MatrixOrder
variable {U Y:Type}[Fintype U][DecidableEq U][Fintype Y]

theorem original (K H:Matrix U U ℝ)(hk:K.transpose=K)(hh:H.transpose=H)(inv:K*H=1)
    (A:Cost)(unit:constantCoeff A=1)(p:Ink (U⊕Y)):
    Wick Y H (thermal K A⁻¹*redo A p)*soil ((A⁻¹)^Fintype.card U)=
      redo A (Wick Y H p):=by
  have same:reroll (axes (U:=Y) A) (leg (U:=U) A⁻¹)=train (axes (U:=U⊕Y) A):=by
    unfold reroll
    congr 1
    funext i
    rcases i with j|j
    · exact congr_arg (· * _) (held_cash (U:=U) (Y:=Y) A⁻¹)
    · change holdUp U (soil A⁻¹*path j)=_
      rw [map_mul,held_cash,up_var]
      rfl
  have one:constantCoeff A⁻¹=1:=by rw [PowerSeries.constantCoeff_inv,unit,inv_one]
  have f:=WilsonIndependentConditionalFormalScale.original K H hk hh inv A⁻¹ one (axes A)
    (degree A p)
  rw [same,heat] at f
  rwa [←RingHom.comp_apply,exact_reset,←RingHom.comp_apply,exact_reset] at f

variable {G:Gauge}{c f:Lattice.Side}(S:StepData c f)(T:Forest S.ratio)
  (H:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

theorem planted (hf:(treeMatrix G S T H).PosDef)(A:Cost)(unit:constantCoeff A=1)
    (Ñ:ChartRatio G)(P w:PChart G f):
    let K:=treeMatrix G S T H
    let heat:=Wick (Woods G c) (treeInverse G S T H 0)
    let η:=thermal (Z:=Woods G c) K A⁻¹
    let v:=raiseE (shot S T Q Ñ P)
    let source:=loom (camSlice G S T (extractV G S T Q)) (flash w)
    let cash:=soil (U:=Woods G c) ((A⁻¹)^Fintype.card (Active G T))
    heat (η*redo A v)*cash=redo A (inside S T H Q Ñ P) ∧
      heat (η*redo A (v*source))*cash=redo A (insideMark S T H Q Ñ P w):=by
  dsimp only
  have sk:(treeMatrix G S T H).transpose=treeMatrix G S T H:=Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
  have inv:treeMatrix G S T H*treeInverse G S T H 0=1:=by
    simp only [treeInverse,resolve,zero_smul,add_zero]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne')
  have sh:(treeInverse G S T H 0).transpose=treeInverse G S T H 0:=by
    simp only [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,sk]
  exact ⟨original _ _ sk sh inv A unit _,original _ _ sk sh inv A unit _⟩

end YM.Integration.WilsonIndependentSpoutDilatedVote
