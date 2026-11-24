import YM.Integration.WilsonMeasuredPublicEntranceQuadraticTriangle
import YM.XSpace.DeepBond

/-! The native reflected two-point dual separates every actual engineering field at any
two different positions. The original Householder map transports the complete tester. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticSeparation
open Maxwell Maxwell.Free XSpace.Normalize
open scoped InnerProductSpace
variable {G:Gauge}{d:ℕ}

theorem align (x y:E4)(size:‖x‖=‖y‖):∃s:Ortho,Ortho.move s x=y:=by
  by_cases eq:x=y
  · exact ⟨1,(Ortho.move_one x).trans eq⟩
  have nz:‖x-y‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr eq))
  have rate:‖x-y‖^2=2*⟪x-y,x⟫_ℝ:=by
    rw [norm_sub_sq_real,inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm y x,size]
    ring
  have unit:2*(‖x-y‖^2)⁻¹*⟪x-y,x⟫_ℝ=1:=by
    calc
      _=(2*⟪x-y,x⟫_ℝ)*(‖x-y‖^2)⁻¹:=by ring
      _=1:=by rw [←rate,mul_inv_cancel₀ nz]
  refine ⟨house (x-y),?_⟩
  change M4.move (houseM (x-y)) x=y
  rw [house_on,unit,one_smul]
  abel

theorem original {x y:E4}(apart:x≠y){p:WickPol G}(hp:p∈shellSector G d)
    (heard:∀q∈shellSector G d,bond G x y p q=0):p=0:=by
  have positive:0<‖x-y‖:=norm_pos_iff.mpr (sub_ne_zero.mpr apart)
  have normed : ‖x-y‖=‖(-‖x-y‖) • basis 3‖:=by simp [norm_smul,basis]
  obtain ⟨s,site⟩:=align (x-y) ((-‖x-y‖) • basis 3) normed
  have physical(q:WickPol G)(hq:q∈shellSector G d):bond G (x-y) 0 p q=0:=by
    have h:=congrArg (fun B:WickPol G→ₗ[ℂ] WickPol G→ₗ[ℂ] ℂ=>B p q) (pair_flow (G:=G) x y (-y))
    simpa [sub_eq_add_neg,heard q hq] using h
  have zero:=pair_nonzero 3 (reflectPol s p) positive (closed_sector hp s).1 (fun q hq=>by
    have k:=move_bond s (x:=x-y) (y:=0) (sub_ne_zero.mpr apart) p (reflectPol s⁻¹ q)
    rw [site,move_zero,←pol_mul,mul_inv_cancel,pol_one,physical _ (closed_sector hq s⁻¹).1] at k
    exact k)
  have old:=congrArg (reflectPol s⁻¹) zero
  simpa only [←pol_mul,inv_mul_cancel,pol_one,map_zero] using old
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticSeparation

