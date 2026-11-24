import YM.Integration.WilsonIndependentSpoutDilatedVote
import YM.Integration.WilsonIndependentSpoutScaledPrimitive

/-! Actual bare and earlier action on the finite integration tree, with both
completed free squares at the appointed positive scale. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutSchurFrame
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior Next.Free
open WilsonIndependentSpoutThermalChange
open scoped Classical BigOperators MatrixOrder
variable {U V:Type}[Fintype U][Fintype V]

theorem linear (A:Cost)(unit:constantCoeff A=1)(M:Matrix U V ℝ)(p:Ink U):
    redo A (loom M p)=loom M (redo A p):=by
  have h:=(redo_com A unit (fun z:Lawn V=>M*ᵥz) (by simp))
  rw [spool_loom] at h
  exact DFunLike.congr_fun h p

omit [Fintype V] in
private theorem noise (A:Cost)(K:Matrix U U ℝ):
    redo A (bodyQ V K)=(soil A⁻¹)^2*bodyQ V K:=by
  have row (i:U):redo A (slopeQ V K i)=soil A⁻¹*slopeQ V K i:=by
    simp only [slopeQ,map_sum,redo_μ,redo_path,Finset.mul_sum,mul_smul_comm]
  simp only [bodyQ,redo_μ,map_sum,map_mul,redo_path,row,Finset.mul_sum,mul_smul_comm]
  apply congr_arg (fun x:Ink (U⊕V)=>(1/2:ℝ) • x)
  exact Finset.sum_congr rfl fun _ _=>by ring

private theorem slow (A:Cost)(unit:constantCoeff A=1)(K:Matrix V V ℝ):
    redo A (holdUp U (orbC K))=(soil A⁻¹)^2*holdUp U (orbC K):=by
  rw [←hold_loom,linear A unit,orbC,redo_palm,map_mul,map_pow,hold_loom,held_cash]

variable {G:Gauge}{c f:Lattice.Side}(S:StepData c f)(T:Forest S.ratio)
  (H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def field (A:Cost)(Ñ:ChartRatio G)(P:PChart G f):Ink (Active G T⊕Woods G c):=
  loom (camSlice G S T (extractV G S T Q)) (jet (unhaar Ñ))-
    (loom (camSlice G S T (extractV G S T Q)) (flash (mix A P))+
     loom (panSlice G S T (extractV G S T Q)) (flash (mix A (sprig (jointPen G S) 2))))+
    (holdUp (Active G T) (orbC (precisionC G c Y))+bodyQ (Woods G c) (treeMatrix G S T H))

theorem original (A:Cost)(unit:constantCoeff A=1){Ñ:ChartRatio G}{P:PChart G f}
    (p:shellK 2 P)(base:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G)
    (hu:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f):
    field S T H Y Q A Ñ P=redo A (shot S T Q Ñ P)+
      (1-soil A⁻¹^2)*(holdUp (Active G T) (orbC (precisionC G c Y))+
        bodyQ (Woods G c) (treeMatrix G S T H)):=by
  rw [shot_bill S T H Y Q p base hz hu hs]
  simp only [field,unscaled,map_add,map_sub,linear A unit,redo_jet A unit,noise,slow A unit,
    redo_stern A p,redo_stern A (sprig_count _ _)]
  ring

end YM.Integration.WilsonIndependentSpoutSchurFrame
