import YM.Integration.WilsonMeasuredPublicEntranceQuadraticFiled

/-! Absolute colour on one named physical field map. A finite menu of the original
recorded tests determines all its free moments. With the signed action fixed, the
remaining freedom is a single colour isometry and its Cartan sign. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRegisteredColor
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceFiniteFreeTests WilsonMeasuredPublicEntranceCommonColor
open WilsonMeasuredPublicEntranceMarkedQuadratics
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem complete (simple:G.Simple){d:ℕ}(hd:6≤d)(A:Module.End ℂ (D d))
    (native:WilsonPhysicalPositionAdmissible.Native C A)
    (all:∀{n:ℕ}(v:Fin n→HFields G d){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>((carried C A) (v i)).val)=Wick.moment G x (fun i=>(v i).val))
    (signed:carried C A (marked G (by omega:4≤d) 1)=marked G (by omega) 1):
    ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v:D d,
      records G d (fields C.labels d (A v))=changing c (records G d (fields C.labels d v)):=by
  let T:=carried C A
  have h4:4≤d:=by omega
  obtain ⟨one,low,real⟩:=WilsonMeasuredPublicEntranceQuadraticFiled.placed native h4
  have both:Deliver h4 T:=⟨WilsonMeasuredPublicEntranceMarkedQuadratics.original h4 T
    (fun u hu=>WilsonMeasuredPublicEntranceMarkedQuadratics.finite h4 T signed
      (WilsonMeasuredPublicEntranceQuadraticFiled.original simple h4 T one low all) hu),
    real,fun _ _ v hx=>all v hx⟩
  haveI:=simple.nontrivial_color
  obtain ⟨i⟩:Nonempty G.ColorIndex:=by
    refine ⟨⟨0,?_⟩⟩
    rw [Gauge.lieDim,←G.colorIso.finrank_eq]
    exact Module.finrank_pos
  obtain ⟨c,shows⟩:=both.actor i
  refine ⟨c,reach simple hd T c shows,fun v=>?_⟩
  simpa only [T,WilsonMeasuredPublicEntranceCommonColor.carried,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    using shows ((fields C.labels d) v)

theorem finite (C:Family G)(simple:G.Simple){d:ℕ}(hd:6≤d):
    let h4:4≤d:=by omega
    let e:=(Extra.FD.recorded C.labels d).b.map (fields C.labels d)
    ∃s:Finset (Hearing (Fin ((Extra.FD.recorded C.labels d).m+1))),∃n:ℕ,
      (∀h∈s,h.arity≤n) ∧ ∀A:Module.End ℂ ((Bel C.book).Field d),
        let T:=carried C A
        WilsonPhysicalPositionAdmissible.Native C A→(∀h∈s,heard e T h=0)→
        T (marked G h4 1)=marked G h4 1→
        ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v:(Bel C.book).Field d,
          records G d (fields C.labels d (A v))=changing c (records G d (fields C.labels d v)):=by
  obtain ⟨s,n,arity,detected⟩:=WilsonMeasuredPublicEntranceFiniteFreeTests.recorded C d
  refine ⟨s,n,arity,fun A native hearing signed=>?_⟩
  exact complete simple hd A native (WilsonMeasuredPublicEntranceAbsoluteColor.pointwise
    ((detected (carried C A)).mp hearing)) signed

theorem original (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(simple:G.Simple)
    {d:ℕ}(hd:6≤d){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    (Z:Module.End ℂ (D d))
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (signed:carried C Z (marked G (by omega:4≤d) 1)=marked G (by omega) 1):
    ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v:D d,
      records G d (fields C.labels d (Z v))=changing c (records G d (fields C.labels d v)):=by
  apply complete simple hd Z (WilsonMeasuredPublicEntranceBranchGap.income F J lead hr hu ht pos Z conv).1 _ signed
  intro n v x hx
  let U:=fields C.labels d
  let T:=carried C Z
  have tested:=WilsonPhysicalPositionBornTransition.invariant F J lead hr hu ht pos Z conv
    (fun i=>U.symm (v i)) hx
  have old:=WilsonPositionPrescribedScreen.zero (C:=C) d n v x
  have moved:=WilsonPositionPrescribedScreen.zero (C:=C) d n (fun i=>T (v i)) x
  have same(i:Fin n):U.symm (T (v i))=Z (U.symm (v i)):=U.symm_apply_apply _
  have read:WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (T (v i))) x=
      WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (v i)) x:=by
    simpa only [same] using tested
  exact moved.symm.trans (read.trans old)
end YM.Integration.WilsonMeasuredPublicEntranceRegisteredColor

