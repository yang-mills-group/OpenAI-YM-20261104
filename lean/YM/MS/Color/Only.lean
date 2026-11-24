import YM.Gauge.Casimir
/-!
# Invariants detecting allowed local Taylor coefficients

See also the analogous rank-one and -two scalarization in StressFlux.Color &
Extra.WeakScaling.Color. We'll need the alternating three-tensors. Use an
  ordinary derivation/Killing proof from the same simple-G assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Only
open Gauge Set Filter LinearMap
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}

lemma ad_anti (x y : G.Color): G.ad x y = - G.ad y x:= G.colorMat_injective (by simp)
lemma rotate (x y z : G.Color) : ⟪G.ad x y,z⟫_ℝ = ⟪G.ad y z,x⟫_ℝ := by
   rw [ad_anti x, inner_neg_left, Gauge.ad_skew, real_inner_comm,neg_neg]

abbrev Tri (G : Gauge) (R : Type) [AddCommMonoid R] [Module ℝ R] := G.Color→ₗ[ℝ] G.Color→ₗ[ℝ] G.Color→ₗ[ℝ] R
abbrev Bi (G : Gauge) (R : Type) [AddCommMonoid R] [Module ℝ R] := G.Color→ₗ[ℝ] G.Color→ₗ[ℝ] R

variable (H : G.Simple)
-- Killing inner makes every derivation inner.
def hook (G : Gauge) : (G.Color →ₗ[ℝ] ℝ) →ₗ[ℝ] G.Color := ((InnerProductSpace.toDual ℝ G.Color).symm.toLinearEquiv.toLinearMap : (G.Color →L[ℝ] ℝ) →ₗ[ℝ] G.Color).comp toContinuousLinearMap.toLinearMap
lemma hop (D : G.Color →ₗ[ℝ] ℝ) (x : G.Color): ⟪hook G D,x⟫_ℝ=D x := InnerProductSpace.toDual_symm_apply
-- D_x matrix if cocycle test
private def leaves (D : Module.End ℝ G.Color) : G.Color →ₗ[ℝ] ℝ where
    toFun x:= trace ℝ G.Color (D * G.ad x)
    map_add' a b:= by rw [map_add,mul_add,map_add]
    map_smul' t a:= by rw [map_smul,mul_smul_comm,map_smul]; rfl
lemma ideals_z (H : G.Simple) : Function.Injective G.ad := LinearMap.ker_eq_bot.mp (by
    rcases H.ideals (LinearMap.ker G.ad) (fun i j h=> by rw [LinearMap.mem_ker,Gauge.ad_jacobi,LinearMap.mem_ker.mp h]; simp) with hl|hl
    exact hl
    obtain ⟨x,y,hxy⟩:= H.nonabelian; exact (hxy (by rw [LinearMap.ker_eq_top.mp hl]; rfl)).elim )


lemma traceTest (H : G.Simple) (D : Module.End ℝ G.Color) (h : ∀ x, D*G.ad x-G.ad x*D=G.ad (D x)) : ∃ v, D=G.ad v := by
   let a := -(G.casimir)⁻¹; have he : 0<G.casimir:= Gauge.casimir_pos H
   let v:= a • hook G (leaves D)
   have hk x : leaves D x = trace ℝ G.Color (G.ad v * G.ad x) := by
      apply neg_injective; rw [Gauge.trace_adjoint H, show inner ℝ v x = a*leaves D x from by unfold v; rw [real_inner_smul_left, hop]] -- test lemma
      unfold a; field_simp
   let Y := D-G.ad v
   have hv x : trace ℝ G.Color (Y*G.ad x) = 0:= by unfold Y; rw [sub_mul,map_sub]; exact sub_eq_zero.mpr (hk x)
   have hm x : Y*G.ad x-G.ad x*Y=G.ad (Y x) := by unfold Y; rw [sub_mul,mul_sub,LinearMap.sub_apply,map_sub,Gauge.ad_jacobi,← h]; abel
   have hy : Y=0:= by
      apply LinearMap.ext; intro x; apply ext_inner_right ℝ; intro y
      have hw : trace ℝ G.Color (G.ad (Y x)*G.ad y)=0:= by
          rw [← hm,sub_mul,map_sub]
          have ht := hv (G.ad x y); rw [Gauge.ad_jacobi,mul_sub,map_sub] at ht
          rw [mul_assoc, mul_assoc (G.ad x), trace_mul_comm _ (G.ad x), mul_assoc]; exact ht
      rw [LinearMap.zero_apply,inner_zero_left]; have hc:= Gauge.trace_adjoint H (Y x) y; rw [hw,neg_zero] at hc; exact (mul_eq_zero.mp hc.symm).resolve_left he.ne'
   exact ⟨v, sub_eq_zero.mp hy⟩
end YM.MS.Only
