import YM.Integration.WilsonMeasuredSignedActionProjected
import YM.Integration.WilsonMeasuredPublicEntranceActionGram
import YM.Integration.WilsonMeasuredPublicEntrancePositiveRay
/-! The uncentered original reflected comparison fixes the scale and the
additive unit of the directed action. It suffices to hear its finite
free determining bank on the same limit of the enrolled fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionHeard
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace Trace.Pilot
open PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonMeasuredPublicEntranceCommonColor (carried)
open XSpace.Stab Next.Rank OJoint PertExtension.Rigidity.Positive
open WilsonMeasuredPublicEntranceFiniteFreeTests
open WilsonPhysicalPositionAdmissible
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)
local notation "D₄" => (Bel C.book).Field 4

theorem fixed (T:Module.End ℂ D₄)(native:Native C T)
    (all:∀{n:ℕ}(v:Fin n→HFields G 4){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>((carried C T) (v i)).val)=Wick.moment G x (fun i=>(v i).val))
    (ray:∃a:ℝ,0 ≤ a ∧ ∃c:ℂ,T (stepField C)=(a:ℂ) • stepField C+c • (Bel C.book).unit 4):
    T (stepField C)=stepField C:=by
  obtain ⟨a,ha,c,land⟩:=ray
  let mass:D₄→ℝ:=fun x=>gram C.labels (hierarchy C.labels) 0 x x
  have iso(x:D₄):mass (T x)=mass x:=WilsonMeasuredPublicEntranceActionGram.original T native all x
  have pd(x:D₄)(hx:x≠0):0 < mass x:=(Complex.lt_def.mp (gramC_pos C.labels (hierarchy C.labels) 0 hx)).1
  have para(x y:D₄):mass (x+y)+mass (x-y)=2*(mass x+mass y):=by
    dsimp only [mass]
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
    ring
  have rate(s:ℝ)(x:D₄):mass ((s:ℂ) • x)=s^2*mass x:=by
    dsimp only [mass]
    simp only [Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  exact WilsonMeasuredPublicEntrancePositiveRay.fixed T ((Bel C.book).unit 4) (stepField C)
    native.neutral mass pd para rate iso ha land

theorem tested:
    let e:=(Extra.FD.recorded C.labels 4).b.map (fields C.labels 4)
    ∃s:Finset (Hearing (Fin ((Extra.FD.recorded C.labels 4).m+1))),∃n:ℕ,
    (∀h∈s,h.arity≤n) ∧ ∀T:Module.End ℂ D₄,Native C T →
      (∀h∈s,heard e (carried C T) h=0) →
      (∃a:ℝ,0 ≤ a ∧ ∃c:ℂ,T (stepField C)=(a:ℂ) • stepField C+c • (Bel C.book).unit 4) →
      T (stepField C)=stepField C:=by
  obtain ⟨s,n,arity,detected⟩:=WilsonMeasuredPublicEntranceFiniteFreeTests.recorded C 4
  refine ⟨s,n,arity,fun T native hearing ray=>?_⟩
  exact fixed C T native (WilsonMeasuredPublicEntranceAbsoluteColor.pointwise
    ((detected (carried C T)).mp hearing)) ray

end YM.Integration.WilsonMeasuredSignedActionHeard
end
