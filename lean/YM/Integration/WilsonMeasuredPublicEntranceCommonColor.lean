import YM.Integration.WilsonMeasuredPublicEntranceBranchGap
import YM.XSpace.PairGlyph

/-! A single original reporter transition acts by one orthogonal colour change on the
entire finite physical field when its elementary weight-four quadratic fields are fixed. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCommonColor
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def carried (C:Family G){d:ℕ}(T:Module.End ℂ ((Bel C.book).Field d)):FieldEnd G d:=
  let U:=fields C.labels d
  U.toLinearMap ∘ₗ T ∘ₗ U.symm.toLinearMap

theorem original (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(simple:G.Simple)
    {d:ℕ}(hd:6≤d){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    (Z:Module.End ℂ (D d))
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (quadratics:∀a:Flavor 0,carried C Z (postedTeam (by omega:4≤d) a a)=postedTeam (by omega) a a):
    ∃s:Knight G,(conn s 1 ∨ conn s (-1)) ∧ ∀v:D d,
      records G d (fields C.labels d (Z v))=changing s (records G d (fields C.labels d v)):=by
  let U:=fields C.labels d
  let T:=carried C Z
  have run:=WilsonMeasuredPublicEntranceBranchGap.income F J lead hr hu ht pos Z conv
  have ev (p:Sec G d):T p=U (Z (U.symm p)):=rfl
  have bar(v:D d):U (WilsonPhysicalPositionAdmissible.real C d v)=negating (U v):=
    Subtype.ext (address_star ..)
  have signed:Deliver (by omega:4≤d) T:=by
    refine ⟨quadratics,?_,?_⟩
    · intro p
      have eq:U (WilsonPhysicalPositionAdmissible.real C d (U.symm p))=negating p:=
        (bar _).trans (congrArg negating (U.apply_symm_apply p))
      rw [ev,←eq,U.symm_apply_apply,run.1.conjugate,ev,bar]
    intro n x v hx
    have real:=WilsonPhysicalPositionBornTransition.invariant F J lead hr hu ht pos Z conv
      (fun i=>U.symm (v i)) hx
    have old:=WilsonPositionPrescribedScreen.zero (C:=C) d n v x
    have moved:=WilsonPositionPrescribedScreen.zero (C:=C) d n (fun i=>T (v i)) x
    have same (i:Fin n):U.symm (T (v i))=Z (U.symm (v i)):=U.symm_apply_apply _
    change Wick.moment G x (fun i=>(T (v i)).val)=Wick.moment G x (fun i=>(v i).val)
    have paired:WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (T (v i))) x=
        WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (v i)) x:=by
      simpa only [same] using real
    exact moved.symm.trans (paired.trans old)
  haveI:=simple.nontrivial_color
  obtain ⟨c⟩:Nonempty G.ColorIndex:=by
    refine ⟨⟨0,?_⟩⟩
    rw [Gauge.lieDim,←G.colorIso.finrank_eq]
    exact Module.finrank_pos
  obtain ⟨s,pays⟩:=signed.actor c
  refine ⟨s,reach simple hd T s pays,fun v=>?_⟩
  simpa only [ev,U.symm_apply_apply] using pays (U v)
end YM.Integration.WilsonMeasuredPublicEntranceCommonColor

