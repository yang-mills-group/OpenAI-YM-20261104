import YM.RegulatorIR.Halo.Caps
import YM.FormalBulk08.Reef.Mount

/-! The actual chronological forest repeats the canonical least-axis block lodge. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramForestRoutes
open Function Finset Lattice Wilson RG Tree Tree.Forest RegulatorIR RegulatorIR.Geometry
open FormalBulk08 FormalBulk08.Flat
open scoped Classical

private theorem same {c f:Side}{g:Ratio c f}(A B:Forest g)(h:A.up=B.up)(k:A.height=B.height):A=B:=by
  cases A
  cases B
  cases h
  cases k
  rfl

theorem original {c f:Side}(S:StepData c f):Halo.bios S=(routes S.patch).forest (S:=S):=by
  refine same _ _ ?_ rfl
  funext x
  by_cases h:leaf S.ratio x
  · have live:= (Lodge.is_leaf S x).mp h
    change (if q:leaf S.ratio x then Bark.toward S.ratio x q else posDir 0)=slideTo S.patch (S.ratio.residue x)
    rw [dif_pos h,slideTo]
    split
    · rfl
    · rename_i a
      exact (a live).elim
  · have gone:=mt (Lodge.is_leaf S x).mpr h
    change (if q:leaf S.ratio x then Bark.toward S.ratio x q else posDir 0)=slideTo S.patch (S.ratio.residue x)
    rw [dif_neg h,slideTo]
    split
    · rename_i a
      exact (gone a).elim
    · rfl

end YM.Integration.WilsonPositionProgramForestRoutes
end
