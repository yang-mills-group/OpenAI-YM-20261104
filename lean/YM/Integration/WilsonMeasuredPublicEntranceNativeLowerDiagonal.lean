import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerInduction
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDiagonal
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open Extra.FD
open WilsonMeasuredPublicEntranceBranchGap (watches)
theorem original {d:ℕ}(T:Module.End ℂ (D d))
    (hearing:∀i j:WilsonMeasuredPublicEntranceBranchGap.Axis C d,watches C i j→let B:=recorded C.labels d
      (B.w j).1=d→∃c:ℝ,0≤c ∧ B.b.coord i (T (B.b j)-(c:ℂ) • B.b j)=0):
    ∃price:WilsonMeasuredPublicEntranceBranchGap.Axis C d→ℝ,(∀j,0≤price j) ∧ ∀i j,watches C i j→let B:=recorded C.labels d
      (B.w j).1=d→B.b.coord i (T (B.b j)-(price j:ℂ) • B.b j)=0:=by
  let B:=recorded C.labels d
  have diagonal (j:WilsonMeasuredPublicEntranceBranchGap.Axis C d):∃c:ℝ,0≤c ∧ (watches C j j→(B.w j).1=d→B.b.coord j (T (B.b j)-(c:ℂ) • B.b j)=0):=by
    by_cases h:watches C j j ∧ (B.w j).1=d
    · obtain ⟨c,p,read⟩:=hearing j j h.1 h.2
      exact ⟨c,p,fun _ _=>read⟩
    · exact ⟨1,zero_le_one,fun w t=>(h ⟨w,t⟩).elim⟩
  let price j:=(diagonal j).choose
  refine ⟨price,fun j=>(diagonal j).choose_spec.1,?_⟩
  intro i j w
  change (B.w j).1=d→_
  intro top
  by_cases same:i=j
  · subst i
    exact (diagonal j).choose_spec.2 w top
  obtain ⟨c,_,seen⟩:=hearing i j w top
  have erased:B.b.coord i (B.b j)=0:=by simp [Module.Basis.coord_apply,same]
  change B.b.coord i (T (B.b j)-(c:ℂ) • B.b j)=0 at seen
  change B.b.coord i (T (B.b j)-(price j:ℂ) • B.b j)=0
  simpa only [map_sub,map_smul,erased,smul_zero,sub_zero] using seen

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDiagonal
end
