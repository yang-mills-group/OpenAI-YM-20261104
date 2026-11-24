import YM.Integration.WilsonConditionalTaylorWheelShot
import YM.Integration.WilsonMovingForestRestriction

/-! Exact complete independent old action at its physical affine saddle:
one fine field, the genuine nonlinear block energy, and its product
Haar factor. No projection to a fixed covariance order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelReef
open Function Filter Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets FormalBulk08.Series
open WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonConditionalTaylorWheelHaar
open scoped Classical BigOperators Matrix Topology ContDiff
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

theorem primitive (O:ChartRatio G) (law:LocalRatio O) (a:S.Choices) (U:Pap (wire G f))
    (y:Pine G S F→ℝ) (x:wire G c→ℝ) (e:ℕ):
    MvPolynomial.eval (Sum.elim y x) (coeff e (Reef.flush F a O U))=
      MvPolynomial.eval (Reef.offer G F y) (coeff e U)-
      MvPolynomial.eval (Sum.elim (Reef.offer G F y) x) (coeff e (Reef.noisePin S a))+
      MvPolynomial.eval y (coeff e (Jets.paste (Real.log∘Reef.sap F O))):=by
  rw [Reef.flush,map_add,map_add]
  congr 1
  · have actual:=congrArg (coeff e) (WilsonMovingForestRestriction.complete (graft (G:=G) F)
      ((graft_receipt F).of_le le_top) (fun t v=>graft_linear F v t) (Sum.elim y x) (vacuumU a U))
    rw [glimpse_coeff,glimpse_coeff] at actual
    change MvPolynomial.eval (Sum.elim y x) (coeff e (roam ℝ (motor (graft (G:=G) F)) (vacuumU a U)))=
      MvPolynomial.eval (graft F (Sum.elim y x)) (coeff e (vacuumU a U)) at actual
    rw [actual,Reef.vacuumU,map_sub,map_sub,PowerSeries.coeff_map]
    change (MvPolynomial.aeval (graft F (Sum.elim y x))) (MvPolynomial.rename Sum.inl (coeff e U))-_ = _
    rw [MvPolynomial.aeval_rename];rfl
  · rw [Jets.halo,PowerSeries.coeff_map,←Plait.pin_rung (Reef.sap F O) (Reef.sap_root F O law)
      (Reef.sap_smooth F O law)]
    change (MvPolynomial.aeval (Sum.elim y x)) (MvPolynomial.rename Sum.inl _)=_
    rw [MvPolynomial.aeval_rename];rfl

private theorem radial {I V:Type} [Fintype I] [Fintype V] (m:(V→ℝ)→(I→ℝ)) (f:(I→ℝ)→ℝ)
    (zero:m 0=0) (linear:∀t:ℝ,∀v,m (t•v)=t•m v) (reg:ContDiffAt ℝ ∞ m 0)
    (h:ContDiffAt ℝ ∞ f 0) (z:V→ℝ):
    glimpse z (Jets.paste (fun v=>f (m v)))=glimpse (m z) (Jets.paste f):=by
  have hm:ContDiffAt ℝ ∞ f (m 0):=zero.symm ▸ h
  have hull:=Jets.fixed_path z (fun v=>f (m v)) (hm.comp 0 reg)
  have rays:(fun s:ℝ=>f (m (s•z)))=(fun s:ℝ=>f (s•m z)):=by funext s;rw [linear]
  rw [rays] at hull
  exact Jets.unique_gaze hull (Jets.fixed_path (m z) f h)

theorem haar (O:ChartRatio G) (law:LocalRatio O) (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (z: Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (Jets.paste (fun v=>Real.log (Reef.sap F O (drift (G:=G) S F M v)))))=
      MvPolynomial.eval (drift (G:=G) S F M z) (coeff e (Jets.paste (Real.log∘Reef.sap F O))):=by
  have zero:drift (G:=G) S F M 0=0:=by change (0:_)+Flat.rawMean G S F M*ᵥ(0:_)=0;rw [Matrix.mulVec_zero,zero_add]
  have linear (t:ℝ) (v:Active G F⊕Woods G c→ℝ):drift (G:=G) S F M (t•v)=t•drift (G:=G) S F M v:=by
    change t•(leftArm v∘(Reef.pines F).symm)+Flat.rawMean G S F M*ᵥ(t•rightArm v)=t•(_+_)
    rw [Matrix.mulVec_smul,smul_add]
  have reg:ContDiffAt ℝ ∞ (drift (G:=G) S F M) 0:=by
    change ContDiffAt ℝ ∞ (fun v:Active G F⊕Woods G c→ℝ => fun i =>
      v (.inl ((Reef.pines F).symm i))+∑k,(Flat.rawMean G S F M) i k*v (.inr k)) 0
    fun_prop
  have hlog:ContDiffAt ℝ ∞ (Real.log∘Reef.sap F O) 0:=
    (Reef.sap_smooth F O law).log (by rw [Reef.sap_root F O law];exact one_ne_zero)
  have hr:=congrArg (coeff e) (radial (drift (G:=G) S F M) (Real.log∘Reef.sap F O) zero linear reg hlog z)
  exact hr

end YM.Integration.WilsonConditionalTaylorWheelReef
end

