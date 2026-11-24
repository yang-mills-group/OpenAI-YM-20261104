import YM.Integration.WilsonMeasuredPublicEntranceActionColor
import YM.Integration.WilsonMeasuredPublicEntranceActionGram

/-! Absolute colour on one named physical field map. A finite menu of the original
recorded tests determines all its free moments. With the signed action fixed, the
remaining freedom is a single colour isometry and its Cartan sign. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionTests
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceFiniteFreeTests WilsonMeasuredPublicEntranceCommonColor
open WilsonMeasuredPublicEntranceMarkedQuadratics
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open PertExtension.Rigidity.Positive
open WilsonMeasuredPublicEntranceActionColor (field transfer)
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem original (C:Family G)(simple:G.Simple){d:ℕ}(hd:6≤d):
    let h4:4≤d:=by omega
    let e:=(Extra.FD.recorded C.labels d).b.map (fields C.labels d)
    ∃s:Finset (Hearing (Fin ((Extra.FD.recorded C.labels d).m+1))),∃n:ℕ,
      (∀h∈s,h.arity≤n) ∧ ∀A:Module.End ℂ ((Bel C.book).Field d),
        let T:=carried C A
        WilsonPhysicalPositionAdmissible.Native C A→(∀h∈s,heard e T h=0)→
        (∃a:ℝ,0 ≤ a ∧ ∃k:ℂ,A (field C h4)=(a:ℂ)•field C h4+k•(Bel C.book).unit d)→
        ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v:(Bel C.book).Field d,
          records G d (fields C.labels d (A v))=changing c (records G d (fields C.labels d v)):=by
  obtain ⟨s,n,arity,detected⟩:=WilsonMeasuredPublicEntranceFiniteFreeTests.recorded C d
  refine ⟨s,n,arity,fun A native hearing cone=>?_⟩
  obtain ⟨a,ha,k,land⟩:=cone
  let h4:4≤d:=by omega
  have all:∀{n:ℕ}(v:Fin n→HFields G d){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>((carried C A) (v i)).val)=Wick.moment G x (fun i=>(v i).val):=WilsonMeasuredPublicEntranceAbsoluteColor.pointwise ((detected (carried C A)).mp hearing)
  let mass:(Bel C.book).Field d→ℝ:=fun x=>gram C.labels (hierarchy C.labels) 0 x x
  have iso(x:(Bel C.book).Field d):mass (A x)=mass x:=WilsonMeasuredPublicEntranceActionGram.original A native all x
  have pd(x:(Bel C.book).Field d)(ne:x≠0):0 < mass x:=(Complex.lt_def.mp (gramC_pos C.labels (hierarchy C.labels) 0 ne)).1
  have para (x y:(Bel C.book).Field d):mass (x+y)+mass (x-y)=2*(mass x+mass y):=by
    dsimp only [mass]
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
    ring
  have scale (s:ℝ)(y:(Bel C.book).Field d):mass ((s:ℂ) • y)=s^2*mass y:=by
    dsimp only [mass]
    simp only [Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  have fixed:=WilsonMeasuredPublicEntrancePositiveRay.fixed A ((Bel C.book).unit d) (field C h4)
    native.neutral mass pd para scale iso ha land
  exact WilsonMeasuredPublicEntranceRegisteredColor.complete simple hd A native all (transfer h4 A fixed)
end YM.Integration.WilsonMeasuredPublicEntranceActionTests
