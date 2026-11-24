import YM.Integration.WilsonPosteriorProjectionWire
import YM.Analysis.Symmetric
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Recover the specified mixed wire component from a finite set of radial
reads chosen only from its number of slots. No dimensional constant from
the ambient torus enters the rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionPolarization
open Finset Set Lattice Wilson RG Precision Tree Exterior Push.Uniform
open WilsonPosteriorProjectionWire
open scoped BigOperators Classical
variable {G : Gauge} {c : Side}

abbrev Slots (r : ℕ) := Fin r → ℝ

private def symmetric (r : ℕ) : Submodule ℝ (Tensor.T (Slots r) ℝ r) where
  carrier := {A | Tensor.Sym A}
  zero_mem' := fun _ _ => rfl
  add_mem' {A B} hA hB u s := by simp only [add_apply,hA _ _,hB _ _]
  smul_mem' a A hA u s := by simp only [smul_apply,hA _ _]

private theorem booked (r : ℕ) : ∃ w : Slots r →₀ ℝ, ∀ A : Tensor.T (Slots r) ℝ r, Tensor.Sym A →
    A (fun i => Pi.single i (1:ℝ)) = ∑ u ∈ w.support, w u * A (fun _ => u) := by
  let F := symmetric r
  let eval (v : Fin r → Slots r) : F →ₗ[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Slots r) ℝ v).toLinearMap.comp F.subtype
  let diag (u : Slots r) := eval (fun _ => u)
  let comp := eval (fun i => Pi.single i (1:ℝ))
  have separate (A : F) (h : ∀ u, diag u A = 0) : A = 0 := by
    apply Subtype.ext
    apply Tensor.ext_diag _ _ A.2 (fun _ _ => rfl)
    exact funext h
  have mem : comp ∈ Submodule.span ℝ (Set.range diag) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker (by
      intro A hA
      rw [separate A (fun u => (Submodule.mem_iInf _).mp hA u)]
      exact Submodule.zero_mem _)
  obtain ⟨w,hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp mem
  refine ⟨w,fun A hA => ?_⟩
  let B : F := ⟨A,hA⟩
  have price := congrArg (fun p : F →ₗ[ℝ] ℝ => p B) hw.symm
  simpa [Finsupp.sum,comp,diag,eval,B,LinearMap.sum_apply] using price

def rule (r : ℕ) := (booked r).choose

theorem wire_component {r : ℕ} (v : Fin r → Letter G c)
    (A : Tensor.T (Positions (Primary c G)) ℝ r) (sym : Tensor.Sym A) :
    A (fun i => display (impulse (v i))) =
      ∑ u ∈ (rule r).support, rule r u * A (fun _ => studio v u) := by
  let B := A.compContinuousLinearMap (fun _ => studio v)
  have s : Tensor.Sym B := by
    intro x p
    simp only [B,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact sym ((studio v) ∘ x) p
  have h := (booked r).choose_spec B s
  simpa only [B,ContinuousMultilinearMap.compContinuousLinearMap_apply,studio_basis,rule] using h

end YM.Integration.WilsonPosteriorProjectionPolarization

