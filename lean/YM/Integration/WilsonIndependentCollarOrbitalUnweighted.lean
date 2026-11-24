import YM.Integration.WilsonIndependentCollarMeasuredProbeWindow

/-! After the winding estimate has spent its smooth test ball, only the original
marker weights remain. The actual flat canonical sheet prices their sum directly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitalUnweighted
open Finset Lattice Marker Multi QuadraticLocal QuadraticLocal.Earn
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Flooring
open WilsonReceivedCanonicalSocketSeed (present contact sheet)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonIndependentCollarOrbitalPeg (ink)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators ContDiff

theorem flat {V:Type}[Fintype V][DecidableEq V](D:V→ℕ)(J:Finset V):
    ‖ink (present D) J‖=1 := by
  have upper:(∏i∈J,‖present D i‖)=(1:ℝ):=prod_eq_one (fun i _=>WilsonIndependentCollarCanonicalProbe.cap D i)
  have inner:=WilsonIndependentCollarOrbitalPeg.inner (present D) J
  have isometric:‖touch (present D) J‖=‖seaMark (present D) J‖:=
    (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (seaMark (present D) J)
  let site:Plot D:=fun v=>(contact (D v),zeroC)
  have low:=ContinuousMap.norm_coe_le_norm (folio (present D) J) site
  have unit (i:V):slice (present D i) (site i)=1:=by
    change iteratedFDeriv ℝ 0 (fun _:E=>(1:ℝ)) (zeroC:E) (dot ∘ (Fin.elim0:Fin 0→Axis))=1
    simp only [iteratedFDeriv_zero_apply]
  have sampled:folio (present D) J site=1:=prod_eq_one fun i _=>unit i
  rw [sampled,norm_one] at low
  exact le_antisymm (inner.2.trans_eq upper) (by rw [inner.1,isometric];exact low)

theorem marker {I:Type}[Fintype I][DecidableEq I]{side:Side}{n:ℕ}{P:Passport side (Fin n)}
    (B:I→Binder P (Stock.census (Fin n)))(x:Affinity.Wallet (room (Fin n)))
    (target:(Stock.census (Fin n)).Mode):
    (∑s:Finset I,‖wages B x target s‖) ≤
      (2:ℝ)^(Fintype.card I)*∏v∈target.val,‖(x v).val‖ := by
  have h:=WilsonIndependentCollarCanonicalProbe.original B (fun _=>0) x target
  simpa only [flat,prod_const_one,mul_one] using h

theorem disk {I:Type}[Fintype I][DecidableEq I]{side:Side}{n:ℕ}{P:Passport side (Fin n)}
    (B:I→Binder P (Stock.census (Fin n)))(x:Affinity.Wallet (room (Fin n)))
    (target:(Stock.census (Fin n)).Mode):
    (∑s:Finset I,‖wages B x target s‖) ≤ (2:ℝ)^(Fintype.card I) := by
  have non:0≤(2:ℝ)^(Fintype.card I):=by positivity
  exact (marker B x target).trans ((mul_le_mul_of_nonneg_left
    (prod_le_one (fun v _=>norm_nonneg _) (fun v _=>(x v).property)) non).trans_eq (mul_one _))

end YM.Integration.WilsonIndependentCollarOrbitalUnweighted
end
