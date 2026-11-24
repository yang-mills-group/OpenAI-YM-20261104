import YM.Integration.WilsonOriginalAlternativeTrialRegular
import YM.Integration.WilsonOriginalAlternativeExtraction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialPartitions
open Finset Marker Multi QuadraticLocal QuadraticLocal.Fusion.Attached Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V][Fintype V]{J:Census V}

def unary (a:Poly J):Poly J:=∑v:V,Poly.send (J.fire v) (a.part (J.fire v))

private theorem entry (a:Poly J)(s:J.Mode):
    (unary a).part s=if s.val.card=1 then a.part s else 0:=by
  have inj {v u:V}:(J.fire v=J.fire u) ↔ v=u:=⟨fun h=>singleton_inj.mp (congrArg Subtype.val h),congrArg _⟩
  rw [unary,Poly.part_sum]
  by_cases single:s.val.card=1
  · obtain ⟨v,h⟩:=card_eq_one.mp single
    have hv:s=J.fire v:=Subtype.ext h
    subst s
    simp [Poly.part_send,inj,single]
  · have no(v:V):s≠J.fire v:=by
      intro h
      apply single
      rw [h]
      exact card_singleton v
    simp [Poly.part_send,no,single]

private theorem block (w:V→ℝ)(wp:∀v,0<w v)(a:Poly J)(β:ℝ)(bp:0≤β)
    (each:∀t:Hot J,Poly.toll w t.val*‖a.part t.val‖≤1)
    (many:∀t:Hot J,1<t.val.val.card→Poly.toll w t.val*‖a.part t.val‖≤β)
    (s:J.Mode)(q:(parts J).Mode)(ok:q∈shards J s):
    Poly.toll w s*‖(∏t∈q.val,a.part t.val)-(∏t∈q.val,(unary a).part t.val)‖≤β:=by
  by_cases all:∀t∈q.val,t.val.val.card=1
  · have h:(∏t∈q.val,(unary a).part t.val)=∏t∈q.val,a.part t.val:=by
      apply prod_congr rfl
      intro t ht
      rw [entry,if_pos (all t ht)]
    rwa [h,sub_self,norm_zero,mul_zero]
  · push Not at all
    obtain ⟨t,ht,no⟩:=all
    have big:1<t.val.val.card:=by
      have pos:=card_pos.mpr t.property
      omega
    have blank:(∏z∈q.val,(unary a).part z.val)=0:=by
      apply prod_eq_zero ht
      rw [entry,if_neg no]
    have split:Poly.toll w s=∏t∈q.val,Poly.toll w t.val:=by
      rw [←show unionOf q=s from (mem_filter.mp ok).2]
      exact prod_biUnion (parts_wise q)
    let b:=fun t:Hot J=>Poly.toll w t.val*‖a.part t.val‖
    have b0(z:Hot J):0≤b z:=mul_nonneg (Poly.worth wp _).le (norm_nonneg _)
    have rest:(∏z∈q.val.erase t,b z)≤1:=prod_le_one (fun z _=>b0 z) (fun z _=>each z)
    rw [blank,sub_zero,split,norm_prod,←prod_mul_distrib]
    change (∏z∈q.val,b z)≤β
    rw [←mul_prod_erase _ _ ht]
    exact (mul_le_of_le_one_right (b0 _) rest).trans (many t big)

theorem original (w:V→ℝ)(wp:∀v,0<w v)(a:Poly J)(quiet:a.part J.quiet=0)(β:ℝ)(bp:0≤β)
    (each:∀t:Hot J,Poly.toll w t.val*‖a.part t.val‖≤1)
    (many:∀t:Hot J,1<t.val.val.card→Poly.toll w t.val*‖a.part t.val‖≤β)(s:J.Mode):
    Poly.toll w s*‖(Poly.pass a).part s-∏v∈s.val,a.part (J.fire v)‖≤(shards J s).card*β:=by
  have bare:(unary a).part J.quiet=0:=by rw [entry,quiet];simp
  have form:(Poly.pass (unary a)).part s=∏v∈s.val,a.part (J.fire v):=Extra.Trajectories.pass_fire _ _
  rw [←form,pass_partition a quiet,pass_partition (unary a) bare,←sum_sub_distrib]
  calc _ ≤ Poly.toll w s*∑q∈shards J s,‖(∏t∈q.val,a.part t.val)-(∏t∈q.val,(unary a).part t.val)‖:=
         mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth wp _).le
       _ = _:=mul_sum ..
       _ ≤ ∑_∈shards J s,β:=sum_le_sum fun q h=>block w wp a β bp each many s q h
       _ = _:=by simp

end YM.Integration.WilsonOriginalAlternativeTrialPartitions
end
