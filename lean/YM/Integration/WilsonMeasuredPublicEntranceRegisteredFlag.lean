import YM.Integration.WilsonMeasuredPublicEntrancePositiveFlag

/-! A physical field known on a nonnegative real ray modulo the fixed vacuum
is fixed by an isometry of its actual reflected two-point form. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRegisteredFlag
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem original {d:ℕ}(T:Module.End ℂ (D d))(native:WilsonPhysicalPositionAdmissible.Native C T)
    (iso:∀x,positive C.labels (hierarchy C.labels) (T x) (T x)=positive C.labels (hierarchy C.labels) x x)
    (price:WilsonMeasuredPublicEntranceBranchGap.Axis C d→ℝ)(nonneg:∀j,0 ≤ price j)(unit:price 0=1)
    (purchased:∀i j,WilsonMeasuredPublicEntranceBranchGap.watches C i j→let B:=Extra.FD.recorded C.labels d
      B.b.coord i (T (B.b j)-(price j:ℂ) • B.b j)=0):T=1:=by
  let B:=Extra.FD.recorded C.labels d
  let mass:D d→ℝ:=fun x=>positive C.labels (hierarchy C.labels) x x
  have pd (x:D d)(h:x≠0):0 < mass x:=positive_def C.labels (hierarchy C.labels) h
  have para (x y:D d):mass (x+y)+mass (x-y)=2*(mass x+mass y):=by
    dsimp only [mass]
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
    ring
  have scale (s:ℝ)(y:D d):mass ((s:ℂ) • y)=s^2*mass y:=by
    dsimp only [mass]
    simp only [Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  apply WilsonMeasuredPublicEntrancePositiveFlag.original B.b B.w T mass pd para scale iso price nonneg
  intro i j later
  by_cases h:j=0
  · subst j
    rw [unit,Complex.ofReal_one,one_smul,B.unit_,show T ((Bel C.book).unit d)=(Bel C.book).unit d from native.neutral,sub_self,map_zero]
  by_cases above:(B.w j).1<(B.w i).1
  · have ne:i≠j:=by intro e;subst j;exact (lt_irrefl _ above)
    have z:B.b.coord i (B.b j)=0:=by simp [Module.Basis.coord_apply,ne]
    have raw:=WilsonMeasuredPublicEntranceRecordedQuotient.native B T native i j above
    change B.b.coord i (T (B.b j)-B.b j)=0 at raw
    rw [map_sub,z,sub_zero] at raw
    rw [map_sub,map_smul,z,smul_zero,sub_zero,raw]
  apply purchased i j
  refine ⟨h,?_⟩
  change (B.w i).1=(B.w j).1 ∧ (B.w j).2≤(B.w i).2
  change ¬((B.w i).1<(B.w j).1 ∨ (B.w i).1=(B.w j).1 ∧ (B.w i).2<(B.w j).2) at later
  omega
end YM.Integration.WilsonMeasuredPublicEntranceRegisteredFlag
