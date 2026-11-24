import YangMills.WilsonProof.NativeSupport.WilsonBridge
import YangMills.WilsonProof.NativeSupport.WilsonLatticeData

set_option autoImplicit false

namespace IssuedBank.PhysicalColourChart

open YangMills
open scoped InnerProductSpace
noncomputable section

variable {g : GaugeGroup} (B : Maxwell.Reference g)

def coordinates : Maxwell.Color B.m →ₗ[ℝ] g.core.Color := g.core.projectColor.comp B.matrix

theorem represented (x : Maxwell.Color B.m) : g.core.colorMat (coordinates B x) = B.matrix x := by
  apply g.core.colorMat_project_self
  apply (g.generates _).1
  rw [← B.colors]
  exact ⟨x, rfl⟩

theorem paidInner (x y : Maxwell.Color B.m) :
    inner ℝ (coordinates B x) (coordinates B y) = inner ℝ x y := by
  apply mul_left_cancel₀ (show (((g.n+1 : ℕ) : ℝ)) ≠ 0 by positivity)
  calc
    _ = -(g.core.colorMat (coordinates B x) * g.core.colorMat (coordinates B y)).trace.re :=
      (g.core.trace_color _ _).symm
    _ = _ := by
      rw [represented, represented]
      exact B.traceForm x y

theorem onto : Function.Surjective (coordinates B) := by
  intro z
  have hz : g.core.colorMat z ∈ g.lieAlgebra := (g.generates _).2 (g.core.colorMat_mem z)
  rw [← B.colors] at hz
  obtain ⟨x,hx⟩ := hz
  exact ⟨x, g.core.colorMat_injective ((represented B x).trans hx)⟩

private theorem preservedNorm (x : Maxwell.Color B.m) : ‖coordinates B x‖ = ‖x‖ := by
  have earn := paidInner B x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at earn
  nlinarith [norm_nonneg (coordinates B x), norm_nonneg x]

def isometry : Maxwell.Color B.m →ₗᵢ[ℝ] g.core.Color where
  toLinearMap := coordinates B
  norm_map' := preservedNorm B

def chart : Maxwell.Color B.m ≃ₗᵢ[ℝ] g.core.Color :=
  LinearIsometryEquiv.ofSurjective (isometry B) (onto B)

theorem chart_apply (x : Maxwell.Color B.m) : chart B x = coordinates B x := rfl

def frame : OrthonormalBasis (Fin B.m) ℝ g.core.Color :=
  (EuclideanSpace.basisFun (Fin B.m) ℝ).map (chart B)

theorem frame_apply (i : Fin B.m) :
    frame B i = coordinates B (EuclideanSpace.single i 1) := by
  change chart B ((EuclideanSpace.basisFun (Fin B.m) ℝ) i) = _
  rw [EuclideanSpace.basisFun_apply, chart_apply]


end
end IssuedBank.PhysicalColourChart
