import YM.Integration.WilsonMeasuredPublicEntranceFiniteFreeTests
import YM.Integration.WilsonMeasuredPublicEntranceCommonColor
import YM.Integration.WilsonMeasuredPublicEntranceMarkedQuadratics

/-! A finite measured test on the recorded physical horizon for one absolute colour
convention. The signed action and the directional reads involve this same field map. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceAbsoluteColor
open Function Set Climb Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceFiniteFreeTests WilsonMeasuredPublicEntranceCommonColor
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticGrid
open WilsonMeasuredPublicEntranceQuadraticSpan WilsonMeasuredPublicEntranceQuadraticProducts
open scoped Classical BigOperators
variable {G:Gauge}{C:Family G}{d:ℕ}

theorem pointwise {T:FieldEnd G d}(paid:recruit T (reference G d)=reference G d)
    {n:ℕ}(u:Fin n→HFields G d){x:Points n}(open_:x∈conf n):
    Wick.moment G x (fun i=>(T (u i)).val)=Wick.moment G x (fun i=>(u i).val):=by
  apply (Test.unique_kernel (smooths (fun i=>T (u i))) (smooths u)).mp _ open_
  exact fun f=>congrArg (fun F:Prediction G d=>F n f u) paid

theorem original (C:Family G)(simple:G.Simple){d:ℕ}(hd:6≤d):
    let h4:4≤d:=by omega
    let e:=(Extra.FD.recorded C.labels d).b.map (fields C.labels d)
    ∃s:Finset (Hearing (Fin ((Extra.FD.recorded C.labels d).m+1))),∃n:ℕ,
      (∀h∈s,h.arity≤n) ∧ ∀A:Module.End ℂ ((Bel C.book).Field d),
        let T:=carried C A
        (∀h∈s,heard e T h=0)→(∀v,T (negating v)=negating (T v))→
        T (marked G h4 1)=marked G h4 1→
        (∀a b:WilsonMeasuredPublicEntranceQuadraticGrid.Four,∀U V:Plane ℝ,
          U.transpose=U→V.transpose=V→T (marked G h4 U)=marked G h4 U→
          T (marked G h4 V)=marked G h4 V→T (marked G h4 (product (lift (exterior a b)) U V))=
            marked G h4 (product (lift (exterior a b)) U V))→
        ∃c:Knight G,(conn c 1 ∨ conn c (-1)) ∧ ∀v,
          records G d ((fields C.labels d) (A v))=changing c (records G d ((fields C.labels d) v)):=by
  let h4:4≤d:=by omega
  obtain ⟨s,n,arity,heard_⟩:=WilsonMeasuredPublicEntranceFiniteFreeTests.recorded C d
  refine ⟨s,n,arity,fun A checked real signed directed=>?_⟩
  let T:=carried C A
  have all:= (heard_ T).mp checked
  have filed:Deliver h4 T:=⟨
    WilsonMeasuredPublicEntranceMarkedQuadratics.original h4 T
      (fun u hu=>WilsonMeasuredPublicEntranceMarkedQuadratics.finite h4 T signed directed hu),
    real,fun _ _ v yes=>pointwise all v yes⟩
  haveI:=simple.nontrivial_color
  obtain ⟨i⟩:Nonempty G.ColorIndex:=by
    refine ⟨⟨0,?_⟩⟩
    rw [Gauge.lieDim,←G.colorIso.finrank_eq]
    exact Module.finrank_pos
  obtain ⟨c,read⟩:=filed.actor i
  refine ⟨c,reach simple hd T c read,fun v=>?_⟩
  simpa only [T,WilsonMeasuredPublicEntranceCommonColor.carried,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    using read ((fields C.labels d) v)
end YM.Integration.WilsonMeasuredPublicEntranceAbsoluteColor

