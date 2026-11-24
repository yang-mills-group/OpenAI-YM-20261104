import YM.Frontier6.Bouquet.Atlas.Courts

/-! Arity-wise normalized partition. No root or cell standard sets to
 restrict pressing onto other strata. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Place}[FiniteDimensional ℝ P]{I:Type*}
lemma unit_loc {x:P}{U:Set P}(h:IsOpen U)(he:x∈ U):∃ S: Set P, IsOpen S ∧ x∈ S∧∃ f: Full P, tsupport f⊆ U∧∀ y∈S,f y=1:=by
    obtain ⟨r,hr,hg⟩:= Metric.mem_nhds_iff.mp (h.mem_nhds he)
    let i:=r/4; have hi:0< i:=by unfold i; positivity
    let g:=Normal.shrink P i; let f:= restrictS (le_refl P) (-x) g; have hx(u):forward (le_refl P) (-x) u=u - x:=by change -x+u = u-x; abel;
    refine ⟨ball x i,isOpen_ball, mem_ball_self hi, f, fun z hz=>?_,fun z hz=>?_⟩
    · have hy:= mem_closedBall_zero_iff.mp (shrink_fits hi (restrict_support (le_refl P) _ g hz)); rw [hx] at hy; apply hg; rw [mem_ball,dist_eq_norm];unfold i at *; linarith only [hy,hr]
    unfold f; rw [restrict_at,hx]; exact shrink_home hi _ (by rw [← dist_eq_norm]; exact (mem_ball.mp hz).le )
lemma whenever (U V:I→ Set P)(s:Finset I)(hs:∀ p∈s, ∃ f:Full P, tsupport f⊆ U p∧ ∀ x∈V p,f x=1):
    ∃ f:I→ Full P,(∀ p∈s,tsupport (f p)⊆ U p)∧ ∀ x∈⋃ p∈s,V p, ∑ p∈s,f p x=1:=by
   induction s using Finset.induction_on with
   | empty=> exact ⟨fun _=>0,by simp⟩
   | @insert i s hb ih=>
      obtain ⟨f,hf,hg⟩:= ih fun k hk=> hs k (mem_insert_of_mem hk); obtain ⟨p,hp,hh⟩:= hs i (mem_insert_self ..)
      let U' := screen (X:=P) (fun x=>1-p x) (contDiff_const.sub p.contDiff); let f' := Function.update (U' ∘ f) i p
      have hk(u: P): (∑ j∈insert i s,f' j u)= p u+(1-p u) * (∑ j∈s, f j u):=by rw [Finset.sum_insert hb, show f' i=p from update_self .., Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [show f' j= _ from update_of_ne (show j≠i from fun h=>hb (h ▸ hj)) ..]; rfl
      refine ⟨f',fun k h=>?_,fun x hx=>?_⟩
      · rcases mem_insert.mp h with rfl|hj; rw [show f' k=p from update_self ..]; exact hp
        have hv:k≠ i:=fun he=>by subst k; contradiction -- h shadow
        exact (show f' k= _ from update_of_ne hv ..) ▸ subset_trans (screen_subset ..) (hf k hj)
      rw [hk]; obtain ⟨k,hk,hq⟩:=mem_iUnion₂.mp hx; rcases mem_insert.mp hk with rfl|hf'; · rw [hh x hq,sub_self,zero_mul,add_zero]
      rw [hg x (mem_iUnion₂.mpr ⟨k,hf',hq⟩)]; ring

variable {E:Ensemble}(i:E)
lemma ring_compact : IsCompact (Ringed (normal i.val) 1):= (isCompact_closedBall (0:normal i.val) 2).of_isClosed_subset (ring_closed _) (fun v hv=>by apply mem_closedBall_zero_iff.mpr; simpa using hv.2)
lemma unit_choice : ∃ (I:Type)(_s:Fintype I)(Z:I→ Court i)(f:I→ Full (normal i.val)), (∀ p,tsupport (f p)⊆(Z p).chamber)∧∀ x∈ Ringed (normal i.val) 1, ∑ p,f p x=1:=by
    let X:= Ringed (normal i.val) 1; choose Z hZ using fun i':X=> Court.exists_at i'.val (by exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) i'.property.1))
    choose V hV hW hp using fun i':X=> unit_loc ((Z i').open_chamber) (hZ i'); obtain ⟨t,ht⟩:= IsCompact.elim_finite_subcover (ring_compact i) V hV (fun x hx=> mem_iUnion.mpr ⟨⟨x,hx⟩,hW ⟨x,hx⟩⟩)
    obtain ⟨f,hf,h⟩:=whenever (fun i=> (Z i).chamber) V t (fun i _=> hp i); refine ⟨t,inferInstance,Z ∘ Subtype.val,f ∘ Subtype.val, fun p=> hf p p.property, fun x hx=>?_⟩; exact (Finset.sum_coe_sort t (fun i:X=>f i x)).trans (h x (ht hx))
end YM.Frontier6.Bouquet.Atelier
