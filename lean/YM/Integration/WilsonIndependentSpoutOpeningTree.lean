import YM.Integration.WilsonIndependentSpoutOpeningPost

/-! The actual constrained Gaussian and the actual extracted predictor
land in the slice on which the joined spring and Haar bills were read. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOpeningTree
open Lattice Exterior RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open FreeResolvent Precision RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger
open WilsonIndependentSpoutOrdinaryPlate WilsonIndependentSpoutOrdinarySpring
open WilsonIndependentSpoutOrdinaryHaar
open scoped Classical BigOperators Matrix
variable {G:Gauge}{f c:Side}(S:StepData c f)(F:Tree.Forest S.ratio)

theorem constrained (y:Lawn (Active G F)):Sliced S F (reveal G S F *ᵥ y) := by
  intro p hp;ext k
  change (insertion (FreeResolvent.plant (G:=G) F) *ᵥ y) (ix (p.1,coord p.2) k)=0
  apply Finset.sum_eq_zero
  intro j _
  change (if FreeResolvent.plant F j = ix (p.1, coord p.2) k then (1:ℝ) else 0)*y j=0
  rw [if_neg,zero_mul]
  intro he
  simp only [FreeResolvent.plant,ix,Prod.mk.injEq,coord_iff] at he
  exact j.1.property ((Prod.ext he.1 he.2.1).symm ▸ hp)

theorem predicted (W:Matrix (Body 1 f) (Body 1 c) ℝ)(b:TreeVars G c):
    Sliced S F (extractV G S F W *ᵥ b) := by
  intro p hp;ext k
  change component (tensor G (extracted S F W) *ᵥ b) k (p.1,coord p.2)=0
  rw [component_mul];exact stays F W (component b k) p hp

theorem sliced (W:Matrix (Body 1 f) (Body 1 c) ℝ)(x:Lawn (Active G F ⊕ Woods G c)):
    Sliced S F (camber G (extractV G S F W) *ᵥ (overM G S F *ᵥ x)):=by
  rw [camVec,←left_hit,Matrix.mulVec_mulVec,overM,(flag_cast (Woods G c) (reveal G S F)).1,
    ←Matrix.mulVec_mulVec,left_hit]
  intro p hp
  change (cloth G f).symm (_+_) (p.1,coord p.2)=0
  rw [map_add,Pi.add_apply,show (cloth G f).symm _ (p.1,coord p.2)=0 from constrained S F _ p hp,
    zero_add]
  exact predicted S F W _ p hp

theorem original {X:Type}{D:X→ℕ}(t:Page D→Scale)(w:X)(bare:t (Page.opening D w)=Clocks.flat)
    (h:S.patch.Branches S.kernel G)(sq:Square F)
    {T:Branchix→Orders (KFoot G)}(V:Sphere S F Clocks.flat T)
    (W:Matrix (Body 1 f) (Body 1 c) ℝ)(x:Lawn (Active G F ⊕ Woods G c))(e:ℕ)(pos:0<e):
    let z:=overM G S F *ᵥ x
    let u:=camber G (extractV G S F W) *ᵥ z
    let b:=rightArm z
    (∑ p:Edge (Site f),drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) e (joined u b))+
    (∑ p:Edge (Site c),drums (T (.inr (WilsonIndependentSpoutOrdinarySpring.peg p)) e) (e+2) (joined u b))+
    (∑ p:Face (Per f),drums (Circuit.mural G t w (base p) e) (e+2) (sample u)) =
      MvPolynomial.eval z (totalR (casePW S (XSpace.Bare.chart G) (extractV G S F W) (topW G f) e)) :=
  WilsonIndependentSpoutOpeningPost.original S F t w bare h sq V _ _ (sliced S F W x) e pos

end YM.Integration.WilsonIndependentSpoutOpeningTree
