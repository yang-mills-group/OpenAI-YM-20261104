import YM.Integration.WilsonConditionalTaylorWheelAffine

/-! The true finite product Haar Jacobian on the old Gaussian slice, through
the complete nonlinear germ, at the nonzero affine coarse mean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelHaar
open Function Filter Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Power
open scoped Classical BigOperators Matrix Topology
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

theorem sites (O:ChartRatio G) (law:LocalRatio O) (v:Pine G S F→ℝ):
    unhaar O (Reef.offer G F v)=∑i:F.Free,Real.log (O.J (Reef.stand G F v i)):=by
  have stored:reveal G S F*ᵥ(vcloth S F G).symm (Reef.stand G F v)=Reef.offer G F v:=by
    rw [WilsonConditionalTaylorWheelAffine.injection]
    apply congrArg (Reef.offer G F)
    funext q
    change v (Reef.pines F ((Reef.pines F).symm q))=v q
    rw [Equiv.apply_symm_apply]
  rw [←stored]
  exact prism S F _ O law

theorem localJacobian (O:ChartRatio G) (law:LocalRatio O):
    (fun v:Pine G S F→ℝ=>unhaar O (Reef.offer G F v))=ᶠ[𝓝 0]
      fun v=>Real.log (Reef.sap F O v):=by
  have pos:∀ᶠ v:Pine G S F→ℝ in 𝓝 0,0<Reef.sap F O v:=
    (Reef.sap_smooth F O law).continuousAt (Ioi_mem_nhds (by rw [Reef.sap_root F O law];exact zero_lt_one))
  filter_upwards [pos] with v hv
  rw [sites S F O law]
  change (∑i:F.Free,Real.log (O.J (Reef.stand G F v i)))=Real.log (∏i:F.Free,O.J (Reef.stand G F v i))
  rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hv.ne')]

def drift (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ) : Pine G S F→ℝ :=
  (leftArm z∘(Reef.pines F).symm)+Flat.rawMean G S F M*ᵥrightArm z

theorem tending (M:Matrix (Body 1 f) (Body 1 c) ℝ):
    Tendsto (drift (G:=G) S F M) (𝓝 0) (𝓝 0):=by
  have hc:Continuous (drift (G:=G) S F M):=by unfold drift leftArm rightArm;fun_prop
  have origin:drift (G:=G) S F M 0=0:=by
    change (0:_)+Flat.rawMean G S F M*ᵥ(0:_)=0
    rw [Matrix.mulVec_zero,zero_add]
  have tm:=hc.continuousAt (x:=0)
  change Tendsto _ _ (𝓝 (drift (G:=G) S F M 0)) at tm
  rwa [origin] at tm

theorem original (O:ChartRatio G) (law:LocalRatio O) (M:Matrix (Body 1 f) (Body 1 c) ℝ):
    loom (camSlice G S F (extractV G S F M)) (Blue.jet (unhaar O)) =
      Jets.paste (fun z=>Real.log (Reef.sap F O (drift (G:=G) S F M z))):=by
  rw [loom_jet _ _ (unhaar_green law),WilsonConditionalTaylorWheelBare.germ]
  apply WilsonMovingPolynomialPull.germ
  filter_upwards [(tending (G:=G) S F M).eventually (localJacobian S F O law)] with z hz
  rw [WilsonConditionalTaylorWheelAffine.fine];exact hz

end YM.Integration.WilsonConditionalTaylorWheelHaar
end

