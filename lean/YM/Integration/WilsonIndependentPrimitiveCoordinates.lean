import YM.Integration.WilsonIndependentPrimitiveTranslations
import YM.Integration.WilsonIndependentPrimitiveWidth
import YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives

/-! Actual component and position coordinates on the two angular arms before any summation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveCoordinates
open FreeResolvent (PAC)
open Exterior Function Filter Lattice Laurent Bloch Wilson RG RegulatorIR RegulatorIR.Oracle
open RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger
open RegulatorIR.Halo RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Calibration
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonIndependentConditionalNativeLinks WilsonIndependentConditionalUnshiftedExit
open WilsonIndependentSpoutFiniteStencil (Raw fold coordinates)
open WilsonIndependentSpoutOrdinaryPrimitives (board)
open scoped BigOperators Classical Topology
variable {G:Gauge}

def site (G:Gauge)(n:Side):Raw G n≃Co n (PAC G 1):=
  (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _)))

def jo (G:Gauge)(P:Patch)(n:Side):Raw G (n*P.L) ⊕ Raw G n ≃ Co n (Hinge G P.L):=
  (((site G (n*P.L)).trans ((blockQ G P.L).markedP n)).sumCongr (site G n)).trans
    (Equiv.prodSumDistrib _ _ _).symm

theorem wrapping (P:Patch)(n:Side)(x:KFoot G):
    jo G P n (fold P n x)=foldUnder n (joint G P x):=by
  cases x with
  | inl x=>
    have h:=congr_arg ((blockQ G P.L).markedP n) (v_loc x P.L n)
    rw [Quarry.swrap,Equiv.apply_symm_apply] at h
    exact congr_arg (fun z:Co n (Larvae G P.L)=>(z.1,Sum.inl z.2)) h.symm
  | inr x=>rfl

theorem translation {a b:Side}(S:StepData b a)(v:Cover)(x:KFoot G):
    joint G S.patch (bundleS S v x)=jog v (joint G S.patch x):=by
  cases x with
  | inl x=>
    have h:=(blockQ G S.patch.L).to_shift v x
    rw [strut] at h
    exact congr_arg (fun z:Cloth (Larvae G S.patch.L)=>(z.1,Sum.inl z.2)) h
  | inr x=>
    have h:=(linksQ G).to_shift v x
    rw [site_roll] at h
    exact congr_arg (fun z:YForest G=>(z.1,Sum.inr z.2)) h

def printed (P:Patch)(T:Branchix→Orders (KFoot G))(e r:ℕ):raw (Hinge G P.L) ℝ r:=
  fun n x=>board P n T e r ((jo G P n).symm ∘x)

theorem point {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(e r:ℕ)(pin:Fin r)
    (x:Fin r→Cloth (Hinge G (C.pactP f).L)):
    let P:=C.pactP f;let T:=C.bore G Z (sheet D) f
    ∀ᶠ n:Side in atTop,printed P T e r n (foldUnder n∘x)=
      ((C.dialect Y G Z (sheet D)).frames f).addon e r ((joint G P).symm ∘x):=by
  intro P T
  filter_upwards [WilsonIndependentSpoutOrdinaryPrimitives.original C Y Z D f e r ((joint G P).symm∘x) pin] with n h
  convert h using 1
  apply congr_arg (board P n T e r)
  funext j
  change (jo G P n).symm (foldUnder n (x j))=fold P n ((joint G P).symm (x j))
  apply (jo G P n).injective
  rw [Equiv.apply_symm_apply,wrapping,Equiv.apply_symm_apply]

end YM.Integration.WilsonIndependentPrimitiveCoordinates
