import YM.Integration.WilsonOriginalCensusCopyGraphs

/-! The actual finite color substitution groups its source by compatible
prior pupils. Each retained pupil has one independent copy location. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCompatibleCopies
open Finset Function Marker Multi RG05Readout.Many
open WilsonReceivedDepositedAlias (fold permit)
open WilsonOriginalCensusCopyGraphs (graph homes member Valid)
open scoped Classical BigOperators
variable {V I U:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype U][DecidableEq U]
variable (B:Census V)(mode:I→Hot B)

def plate {Z:Type}[Fintype Z][DecidableEq Z]:Finset Z≃(Stock.census Z).Mode where
  toFun q:=⟨q,mem_powerset.mpr (subset_univ _)⟩
  invFun q:=q.val
  left_inv _:=rfl
  right_inv _:=rfl

def entry (s:B.Mode)(q:Finset I)(z:ℂ):ℂ:=
  if h:Lit (parts B) mode q then if s=unionOf h.climb then z else 0 else 0

omit [Fintype V] [Fintype I] [Fintype U] in
theorem admitted (q:Finset I)(p:q→U):
    Lit (parts B) (fun x:I×U=>mode x.1) (graph q p) ↔ Lit (parts B) mode q:=by
  have same:(graph q p).image (fun x=>mode x.1)=q.image mode:=by
    nth_rw 2 [←homes q p]
    rw [image_image]
    rfl
  constructor
  · intro h
    refine ⟨same ▸ h.1,?_⟩
    intro a ha b hb eqn
    have owned(x:q):(x.val,p x)∈graph q p:=member.mpr ⟨x.property,rfl⟩
    exact congrArg Prod.fst (h.2 (owned ⟨a,ha⟩) (owned ⟨b,hb⟩) eqn)
  · intro h
    refine ⟨same.symm ▸ h.1,?_⟩
    intro a ha b hb eqn
    exact WilsonOriginalCensusCopyGraphs.one q p ha hb
      (h.2 (member.mp ha).choose (member.mp hb).choose eqn)

omit [Fintype V] in
private theorem emitted {Z:Type}[Fintype Z][DecidableEq Z](labels:Z→Hot B)
    (q:Finset Z)(s:B.Mode)(z:ℂ):
    (fold B labels (Poly.send (plate q) z)).part s=entry B labels s q z:=by
  classical
  unfold WilsonReceivedDepositedAlias.fold entry
  rw [AlgHom.comp_apply,mouth,move]
  simp only [show (plate q).val=q from rfl,Finset.prod_const_one,one_mul]
  by_cases enrolled:Lit (parts B) labels q
  · simp only [dif_pos enrolled,substitute_apply,substituteL_send,Poly.part_send]
  · simp only [dif_neg enrolled,map_zero]
    rfl

omit [Fintype V] in
theorem original (K:Poly (Stock.census (I×U)))(s:B.Mode):
    (fold B (fun x:I×U=>mode x.1) K).part s=
       ∑q:Finset I,∑p:q→U,entry B mode s q (K.part (plate (graph q p))):=by
  classical
  let fee (g:Finset (I×U)):=entry B (fun x:I×U=>mode x.1) s g (K.part (plate g))
  have sale:(fold B (fun x:I×U=>mode x.1) K).part s=∑g:Finset (I×U),fee g:=by
    conv_lhs=>rw [←Poly.studs K,map_sum,Poly.part_sum]
    rw [←plate.sum_comp]
    exact sum_congr rfl (fun g _=>emitted B _ g s _)
  have trimmed:(∑g:Finset (I×U),fee g)=∑g:Valid I U,fee g.val:=by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun g:Finset (I×U)=>Set.InjOn Prod.fst (g:Set (I×U))) fee]
    have dark:(∑g:{g:Finset (I×U)//¬Set.InjOn Prod.fst (g:Set (I×U))},fee g.val)=0:=by
      apply sum_eq_zero
      intro g _
      exact dif_neg (fun ok=>g.property (WilsonOriginalCensusCopyGraphs.admissible B mode g.val ok))
    rw [dark,add_zero]
  rw [sale,trimmed,WilsonOriginalCensusCopyGraphs.sum fee]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro p _
  unfold fee entry
  by_cases allowed:Lit (parts B) mode q
  · rw [dif_pos allowed,dif_pos ((admitted B mode q p).2 allowed)]
    have same:((admitted B mode q p).2 allowed).climb=allowed.climb:=by
      apply Subtype.ext
      change (graph q p).image (fun x=>mode x.1)=q.image mode
      nth_rw 2 [←homes q p]
      rw [image_image]
      rfl
    rw [same]
  · rw [dif_neg allowed,dif_neg (fun h=>allowed ((admitted B mode q p).1 h))]

end YM.Integration.WilsonOriginalCensusCompatibleCopies
end
