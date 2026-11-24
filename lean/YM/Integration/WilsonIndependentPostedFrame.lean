import YM.Integration.WilsonIndependentPostedBoard

/-! The incoming vacuum and its new Wilson cells form the genuine IR `jVac` in the declared frame. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedFrame
open Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Halo
open RegulatorIR.Step RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Diagram
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalNativeLinks (fine coarse joint)
open WilsonIndependentPostedInjection (channel)
open WilsonIndependentConditionalCoordinateHeat (row)
open scoped BigOperators Classical Topology
variable {G:Gauge}
theorem old (P:Patch)(A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(e r:ℕ)(hr:0<r)
    (q:Fin r→KFoot G):
    WilsonIndependentPostedGrant.oldCover A Ñ N m α P.L e r (joint G P∘q)=
      offer (Function.Embedding.inl (α:=Foot G) (β:=Foot G)) (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α e r) q:=by
  rw [WilsonIndependentPostedGrant.oldCover,WilsonIndependentPostedInjection.cover]
  let t:=channel Cover (Larvae G P.L) (Hooks G)
  have pay:plants P.L (fun r=>WilsonIndependentSpoutReportedQuiet.cover A Ñ N m α e r) r=
      (fun z=>WilsonIndependentSpoutReportedQuiet.port A Ñ N m α e r ((fine G P).symm∘z)):=by
    funext z
    rw [plants,if_neg (ne_of_gt hr)]
    apply congr_arg (WilsonIndependentSpoutReportedQuiet.cover A Ñ N m α e r)
    funext i
    change panel P.L (Hooks G) (z i) = coarse G ((fine G P).symm (z i))
    rw [←WilsonIndependentConditionalNativeLinks.fine_link,Equiv.apply_symm_apply]
  rw [pay]
  exact WilsonIndependentPostedBoard.carried (fine G P) (joint G P) Function.Embedding.inl t (fun _=>rfl) _ q

variable {W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
    (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)

theorem original (e r:ℕ)(hr:0<r):
    row (joint G (C.pactP f)) (WilsonIndependentPostedBoard.port C Y Z D f A Ñ N m α e r)=
      (C.devices Y G Z (sheet D) f).jVac (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α) e r:=by
  funext z
  by_cases h:e=0
  · subst e
    have zero:(C.devices Y G Z (sheet D) f).addon 0=0:=vacuum_lo _ (Halo.essential (C.lane Y G Z (sheet D)) f)
    change _=offer (firstChannel _ _).native (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α 0 r) z+
      (C.devices Y G Z (sheet D) f).addon 0 r z
    rw [zero]
    simp [WilsonIndependentConditionalCoordinateHeat.row,WilsonIndependentPostedBoard.port,WilsonIndependentSpoutReportedQuiet.port,
      WilsonIndependentSpoutReportedQuiet.cover,offer,Stalk.collect]
  · simp only [WilsonIndependentConditionalCoordinateHeat.row,WilsonIndependentPostedBoard.port,if_neg h,WilsonIndependentPostedGrant.cover,GridStep.jVac,Pi.add_apply]
    rw [old _ _ _ _ _ _ _ _ hr]
    apply congr_arg₂ (·+·) rfl
    apply congr_arg (((C.dialect Y G Z (sheet D)).frames f).addon e r)
    funext i;exact Equiv.symm_apply_apply _ _

end YM.Integration.WilsonIndependentPostedFrame
