import YM.Integration.WilsonConditionalTaylorWheelCoverBirth

/-! The upper construction uses the same independently prescribed local
tree as the canonical finite-volume forest at every torus side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
open Function Lattice RG Tree Wilson Laurent
open FormalBulk08 FormalBulk08.Flat WilsonCoeffUV
open scoped Classical

theorem localPath (P:Patch) (x:Site P.L):residueGo P x=(Flat.routes P).aim x:=by
  change shrinkAt (lift x)=Flat.slideTo P x
  by_cases zero:x=0
  · subst x;simp [shrinkAt,bad,Flat.slideTo]
  · have nz:lift x≠0:=fun no=>zero (by rw [←wrap_lift x,no,map_zero])
    obtain ⟨k,positive⟩:=Function.ne_iff.mp nz
    have occupied:(bad (lift x)).Nonempty:=⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,positive⟩⟩
    rw [shrinkAt,dif_pos occupied,Flat.slideTo,dif_pos zero]
    rfl

theorem original {c f:Side} (S:StepData c f):
    repeatF S=Flat.Lodge.forest (S:=S) (Flat.routes S.patch):=by
  unfold repeatF Flat.Lodge.forest
  congr 1
  funext i
  exact localPath S.patch (S.ratio.residue i)

end YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
end

