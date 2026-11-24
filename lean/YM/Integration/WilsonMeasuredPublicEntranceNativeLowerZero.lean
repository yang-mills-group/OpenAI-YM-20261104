import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerInduction
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerZero
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

private theorem singleton (F:Labels.Frame G 0)(j:F.Index):j=0:=by
  have base:=Labels.decompose (F.basis j)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at base
  have grade:F.basis j∈Labels.Grade (0,0):=base ▸ Labels.gradePart_mem (0,0) (F.basis j)
  obtain ⟨z,equal⟩:=Labels.scalar_grade (m:=0) grade
  by_contra distinct
  have live:F.coords (F.basis j) j=1:=by simp
  rw [equal,map_smul,F.coords_unit] at live
  simp [Labels.Frame.e0,distinct] at live
theorem original (T:Module.End ℂ (D 0))(native:WilsonPhysicalPositionAdmissible.Native C T):T=1:=by
  apply LinearMap.ext
  intro v
  have scalar:∃z:ℂ,v=z • (Bel C.book).unit 0:=by
    obtain ⟨X,rfl⟩:=(Bel C.book).onto 0 v
    obtain ⟨z,scaled⟩:∃z:ℂ,X=z • (standard C.book.grid).scalar 0:=by
      refine ⟨X 0,funext fun i=>?_⟩
      rw [Register.scalar,pow_zero,one_smul,singleton _ i]
      simp [Labels.Frame.e0]
    rw [scaled,map_smul]
    exact ⟨z,rfl⟩
  obtain ⟨z,rfl⟩:=scalar
  simp only [map_smul,native.neutral,Module.End.one_apply]

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerZero
end
