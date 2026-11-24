import YM.Integration.WilsonPositionScaleLawColorMeasured
import YM.Integration.WilsonPhysicalPositionBornCandidates

/-! The inverse coordinate is obtained on the original finite Born candidate set,
from the very same two-sided bound, before any continuum target is read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorInverse
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land
open WilsonPhysicalPositionDiscreteBranches (field shift preserves)
open WilsonPhysicalPositionBornCandidates (operator possible)
open scoped Topology Classical
variable {G:Gauge}{d:ℕ}
local notation "N" => MoveSpace G d

theorem read (C:Family G)(a:N)(p:(Bel C.book).Field d):
    fields C.labels d (operator C a p)=field a (fields C.labels d p):=
  (fields C.labels d).apply_symm_apply _

theorem inject (C:Family G){B:ℝ}{a:N}(chosen:a∈possible C d B):Injective (field a):=by
  have h:Injective (operator C a):=by
    intro p q he
    have z:=chosen.2.2 (p-q)
    rw [map_sub,he,sub_self,norm_zero,mul_zero] at z
    exact sub_eq_zero.mp (norm_le_zero_iff.mp z)
  intro p q hp
  let S:=fields C.labels d
  apply S.symm.injective
  apply h
  apply S.injective
  rw [read,read,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hp]

def inverse (a:N)(ha:Injective (field a)):N:=
  Classical.choose ((LinearMap.injective_iff_surjective.mp (WilsonPhysicalPositionDiscreteBranches.cancellation ha)) (-a))

theorem both (a:N)(ha:Injective (field a)):
    field a ∘ₗ field (inverse a ha)=1 ∧ field (inverse a ha) ∘ₗ field a=1:=by
  have h:shift a (inverse a ha) = -a:=Classical.choose_spec
    ((LinearMap.injective_iff_surjective.mp (WilsonPhysicalPositionDiscreteBranches.cancellation ha)) (-a))
  have f:field a ∘ₗ field (inverse a ha)=1:=by
    rw [←WilsonPhysicalPositionDiscreteBranches.action,h,add_neg_cancel]
    unfold field;rw [map_zero,stand0]
  refine ⟨f,?_⟩;ext1 p;apply ha
  exact DFunLike.congr_fun f (field a p)

theorem selected (C:Family G){a:N}{B:ℝ}(chosen:a∈possible C d B):
    inverse a (inject C chosen)∈possible C d B:=by
  letI :NormedAddCommGroup ((Bel C.book).Field d→L[ℂ](Bel C.book).Field d):=ContinuousLinearMap.toNormedAddCommGroup
  let b:=inverse a (inject C chosen)
  obtain ⟨f,_⟩:=both a (inject C chosen)
  have fb:field a ∘ₗ field b=1:=f
  have cancel (p:(Bel C.book).Field d):operator C a (operator C b p)=p:=by
    apply (fields C.labels d).injective
    rw [read,read]
    exact DFunLike.congr_fun fb _
  refine ⟨?_,?_,?_⟩
  · change recruit (field b) (reference G d)=reference G d
    calc
      _=recruit (field b) (recruit (field a) (reference G d)):=congrArg (recruit (field b)) chosen.1.symm
      _=reference G d:=by rw [recruits_comp,fb];rfl
  · apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans chosen.2.1)
    intro p
    simpa only [cancel] using chosen.2.2 (operator C b p)
  · intro p
    calc
      ‖p‖=‖operator C a (operator C b p)‖:=by rw [cancel]
      _≤‖operator C a‖*‖operator C b p‖:=(operator C a).le_opNorm _
      _≤B*‖operator C b p‖:=mul_le_mul_of_nonneg_right chosen.2.1 (norm_nonneg _)

end YM.Integration.WilsonPositionScaleLawColorInverse
end
