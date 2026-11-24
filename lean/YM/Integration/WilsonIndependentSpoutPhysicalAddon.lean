import YM.Integration.WilsonIndependentSpoutSchurFrame
import YM.Integration.WilsonIndependentSpoutScaledPrimitive
import YM.Integration.WilsonIndependentSpoutOpeningTree

/-! Read the RegulatorIR spring and tree-Haar primitive tensors on an
ordinary periodic board, with the entire genuine incoming finite energy and
the positive scale already in use. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPhysicalAddon
open Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Binding
open RegulatorIR.Profiles RegulatorIR.Clocks RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Diagram
open RegulatorIR.Prim RegulatorIR.Diagram.Formal RegulatorIR.Clocks.Warp RegulatorIR.Ward
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open FreeResolvent Metric Tree Exterior Precision WilsonIndependentSpoutOrdinarySpring
open WilsonIndependentSpoutOrdinaryHaar
open scoped Classical BigOperators Matrix Topology ContDiff

private theorem pulled {U V:Type}[Fintype U][Fintype V](M:Matrix U V ℝ)
    (v:Lawn V)(p:Ink U)(e:ℕ):
    MvPolynomial.eval v (coeff e (loom M p))=MvPolynomial.eval (M *ᵥ v) (coeff e p):=by
  exact (congrArg (MvPolynomial.eval v) (coeff_map _ _ p)).trans (cord_apply ..)

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H Y:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

theorem original (branch:S.patch.Branches S.kernel G)(sq:Square F)(K:Feeds)
    {T:Branchix→Orders (KFoot G)}(sale:Sphere S F K.scale T)(P:PChart G f)
    (x:Lawn (Active G F⊕Woods G c))(e:ℕ)(pos:0<e):
    let α:=tale K.dine;let z:=overM G S F *ᵥ x;let u:=camber G (extractV G S F Q) *ᵥ z
    let b:=rightArm z;let X:=joined u b
    MvPolynomial.eval x (coeff e (WilsonIndependentSpoutSchurFrame.field S F H Y Q α (XSpace.Bare.chart G) P))=
      MvPolynomial.eval u (coeff e (orbC (precisionC G f H)-flash (mix α P)))+
      (∑p:Edge (Site f),drums (T (.inl (peg p)) e) e X)+
      ∑p:Edge (Site c),drums (T (.inr (peg p)) e) (e+2) X:=by
  intro α z u b X
  have cu:camSlice G S F (extractV G S F Q) *ᵥ x=u:=by
    rw [camSlice,←Matrix.mulVec_mulVec]
  have cb:panSlice G S F (extractV G S F Q) *ᵥ x=tuple u b:=by
    rw [panSlice,←Matrix.mulVec_mulVec]
    ext j;cases j with
    | inl j=>exact congr_fun (camIn G (extractV G S F Q) z).1 j
    | inr j=>exact congr_fun (camIn G (extractV G S F Q) z).2 j
  have pure:Sliced S F u:=WilsonIndependentSpoutOpeningTree.sliced S F Q x
  have haar:=WilsonIndependentSpoutOrdinaryHaar.original S F sq K.scale sale u pure b e pos
  have spring:=WilsonIndependentSpoutScaledPrimitive.spring S F branch K sale u b e pos
  have a:MvPolynomial.eval u (coeff e (jet (unhaar (XSpace.Bare.chart G))))=
      coeff e (tale (fun t:ℝ=>unhaar (XSpace.Bare.chart G) (t • u))):=by
    rw [rayon,lore ((unhaar_green (XSpace.Bare.chart_ratio G)).of_le (by simp)) u,inscription,coeff_mk]
    rfl
  dsimp only [X]
  rw [haar,spring]
  simp only [WilsonIndependentSpoutSchurFrame.field,map_add,map_sub,pulled,cu,cb,
    body_orb_C,holdUp,orbC,coeff_map,coeff_C,if_neg pos.ne',map_zero]
  rw [a]
  simp only [flash,coeff_mk]
  ring

end YM.Integration.WilsonIndependentSpoutPhysicalAddon
