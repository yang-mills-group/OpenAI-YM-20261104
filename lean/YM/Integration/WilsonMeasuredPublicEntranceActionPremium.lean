import YM.Integration.WilsonMeasuredPublicEntranceActionInvariant
import YM.TraceExtension.Margin.Pillar

/-! The positive size, reality and signed symmetries of the original quadratic action
in every raw grade-four frame, before any physical station is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionPremium
open Lattice Labels StressFlux Trace
open scoped Classical BigOperators
variable {G:Gauge}

theorem grade : square4 G ∈ Grade (4,2) := by
  let L:Submodule ℝ (Label G 4):=(Grade (4,2)).restrictScalars ℝ
  change (1/4:ℝ) • (∑ i:Axis,∑ j:Axis,pair G i j i j)∈L
  apply L.smul_mem
  apply L.sum_mem
  intro i _
  apply L.sum_mem
  intro j _
  exact productPol_grade _ _

theorem positive (simple:G.Simple)(F:Frame G 4):
    0<F.coeffSize (F.core (F.coords (square4 G))) := by
  let y:=F.coords (square4 G)
  have empty:y 0=0:=F.power_coefficient 0 (F.zero_degree ▸ by decide : (4,2)≠F.grades 0) grade
  have center:F.core y=y:=by ext i;by_cases hi:i=0 <;> simp [Frame.core,hi,empty]
  rw [show F.core (F.coords (square4 G))=y from center]
  by_contra! h
  have none:y=0:=by
    funext i
    apply norm_eq_zero.mp
    exact le_antisymm ((Finset.single_le_sum (f:=fun j=>‖y j‖) (fun j _=>norm_nonneg _) (Finset.mem_univ i)).trans h) (norm_nonneg _)
  exact Margin.square_alive simple (F.coords.injective (none.trans (map_zero F.coords).symm))

theorem symmetries (F:Frame G 4):let y:=F.coords (square4 G)
    star y=y ∧ ∀s:Signed,F.act s.ortho y=y:=by
  let v:Fin 3→ℝ:=![0,1,0]
  let w:=Fin.cons (α:=fun _=>ℝ) 0 v
  have diag (i:Axis):stress G w i i=(4:ℝ) • square4 G:=by
    simpa [w,v] using Margin.quart (G:=G) v rfl rfl i i
  have origin:=((labelStress (G:=G) w).property.2.1 (0:Axis) 0)
  change conjR (stress G w 0 0)=stress G w 0 0 at origin
  rw [diag,map_smul] at origin
  have bar:realBar (square4 G)=square4 G:=by
    exact (smul_right_injective _ (by norm_num:(4:ℝ)≠0)) origin
  constructor
  · funext i
    change star (F.coords (square4 G) i)=_
    rw [←F.conj_basis,F.coords.symm_apply_apply,bar]
  · intro s
    have rot:=((labelStress (G:=G) w).property.2.2 s (0:Axis) 0)
    change spinR s (stress G w 0 0)=_ • stress G w _ _ at rot
    rw [diag,diag,←sq,sign_sq,one_smul,map_smul] at rot
    have native:tensor s.ortho (square4 G)=square4 G:=
      (smul_right_injective _ (by norm_num:(4:ℝ)≠0)) rot
    exact (F.act_coords ..).trans (congrArg F.coords native)
end YM.Integration.WilsonMeasuredPublicEntranceActionPremium
end
