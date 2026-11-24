import YM.MSbar.Pole.Sew.Collar
/-!
# Scale transfer including `D`-dependent weight on new momentum integrations
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Sew.Thread
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Tip
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n:ℕ} {T:Thread I} {V Q : Finset I} (A:Finset I)

lemma spin_scale (h:Fits T V) (hh:T.inputs⊆A) (hp:Disjoint A T.chain.reads) {F:ℂ→Cloud I} (d:Age) {r:ℝ} (hr:0<r) (x:External I n) (p:place n) {z:ℂ}
    (ha : ∀ i∈ T.chain.reads, Tone (F z) i) :
    let α:= d.alpha z
    T.spun r (roll A d r F) z n (p,x)=(r:ℂ)^(α+ 2 - T.chain.demand) * T.spun 1 F z n (r • p,move A r x) := by
  intro α
  have hl : T.warp n (r • p,move A r x)=move A r (T.warp n (p,x)) := by
    rw [warps,warps];
    exact enlarges T.output T.root T.left T.right A ( -- syntax
      show _ from fun i hi=> hh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))) h.root_mem (hh (by simp [inputs])) (hh (by simp [inputs])) x p r
  let C:=Chain.term T.left (dimension z)
  let D: Cloud I:= C (F z) T.chain
  let y := T.warp n (p,x)
  have hv : C (roll A d r F z) T.chain n y = (r:ℂ)^(α-T.chain.demand)*D n (move A r y):= by
    have hx := T.chain.tips T.left (dimension z) A d z (F:=F z) (hh (by simp [inputs])) hp.symm ha y hr
    have he:(r:ℂ)≠0:= by exact_mod_cast hr.ne'
    apply mul_left_cancel₀ (pow_ne_zero T.chain.demand he)
    rw [Complex.cpow_sub _ _ he,Complex.cpow_natCast]
    change (r:ℂ)^T.chain.demand * Chain.term T.left _ (roll A d r (fun _=>F z) z) _ _ _ = _
    rw [← hx]; change _*D _ _= _*( _/_ * D _ _); field_simp; exact mul_comm ..
  have ht : Heat.wave r p=(r:ℂ)^2*Heat.wave 1 (r • p):=by
    unfold Heat.wave; rw [one_smul]; norm_num; ring
  unfold spun pre; simp only; rw [ht,hl]; change _*C _ T.chain n y= _*( _*D n (move A r y)); rw [hv]; rw [show α+2-T.chain.demand=(α-T.chain.demand)+2 by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hr.ne'), Complex.cpow_ofNat]; change _*_*(_*D _ _)=_*_*(_*_ *D _ _); ring

private lemma shift_momentum (h:Fits T V) {L:Finset I} (hh:T.inputs⊆A) (hL:L⊆T.output) (x:External I n) (r:ℝ): T.momentum L n (move A r x)=r • T.momentum L n x:= by
  have he:T.output ⊆ A:=fun i hi=>hh (show i∈insert _ (insert _ _) from Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))
  unfold momentum; rw [inferred,inferred,smul_neg,Finset.smul_sum]; congr 1
  apply Finset.sum_congr rfl; intro i hi; unfold anchor; by_cases hb:i=T.root
  · rw [hb,update_self,update_self,smul_neg,Finset.smul_sum]; congr 1; apply Finset.sum_congr rfl; intro i hi; exact if_pos (he (Finset.mem_of_mem_erase hi))
  rw [update_of_ne hb,update_of_ne hb]; exact if_pos (he (hL hi))

lemma bridge_scale (h:Fits T V) (hh:T.inputs⊆A) (hp:Disjoint A T.chain.reads) {F:ℂ→Cloud I} (d:Age) {r:ℝ} (hr:0<r)
    (x:External I n) {L:Finset I} (hL:L⊆T.output) {z:ℂ} (ha : ∀ i∈ T.chain.reads, Tone (F z) i) :
    T.twig L r (roll A d r F) z n x=roll A ⟨d.a+2-T.chain.demand,d.l⟩ r (T.twig L 1 F) z n x := by
  rw [roll]; change T.spun r _ _ _ _= _*T.spun 1 _ _ _ (T.momentum L n _,_); rw [shift_momentum A h hh hL];
  rw [spin_scale A h hh hp d hr x _ ha]; congr 2; unfold alpha linear; push_cast; abel

lemma arrives (h:Fits T V) (hh:T.inputs⊆A) (hp:Disjoint A (T.chain.reads∪V))
    {F:ℂ→Cloud I} (d:Age) {r:ℝ} (hr:0<r) {k} (hk:Vortex k F)
    (ho:Acts (T.inputs ∪ (T.chain.reads ∪ V)) (T.chain.reads ∪ V) F) (μ:ℝ) :
    (Integrates μ (T.spun r (roll A d r F))) =ᶠ[approaching] roll A ⟨d.a-2-T.chain.demand,d.l+1⟩ r (Integrates μ (T.spun 1 F)) := by
  have ht: Acts (T.inputs ∪ (T.chain.reads ∪ V)) (T.chain.reads ∪ V) (roll A d r F):= Eventually.mono (p:=fun z=>Shape _ _ (F z)) ho fun z hz => (hz.move_by A hp r).scale _
  filter_upwards [Skin.statuses (joined h r hr (roll_vortex _ _ hk hr) ht),Skin.statuses (joined h 1 zero_lt_one hk ho), ho] with z ⟨hy,hx⟩ ⟨hy',hx'⟩ hf; funext n x
  let c:= d.alpha z+2-(T.chain.demand:ℕ)
  let X:= T.spun r (roll A d r F) z; let B:= T.spun 1 F z; let D:= dimension z
  have hv := scaled (F:=X) (G:=B) hx hy hx' hy' x (move A r x) hr ((r:ℂ)^c) D ?_
  · unfold Integrates
    change omega n X x D * factor μ z= _*(omega n B _ D * factor μ z)
    rw [hv]; have he : (Age.mk (d.a-2-T.chain.demand) (d.l+1)).alpha z = - D + c:= by unfold c D dimension Age.alpha Age.linear; push_cast; ring
    rw [he,Complex.cpow_add _ _ (by exact_mod_cast hr.ne')]; ring
  intro y t; unfold lifting
  have hl : pad n ∘ move A r x= move A r (pad n ∘ x):=(move_pad ..).symm
  have HB := spin_scale A h hh (Finset.disjoint_left.mpr fun i hi hv=> Finset.disjoint_left.mp hp hi (Finset.mem_union_left _ hv)) (F:=F) d hr (pad n ∘ x) (portal n (y,(t:ℂ))) (z:=z)
        (fun i hi=> hf.angle i (Finset.mem_union_left _ hi))
  change X _ (_,_)= _* B _ (portal _ _,pad n∘ _); rw [hl,show portal n (r • y,(↑(r*t):ℂ))= r • portal n (y,(t:ℂ)) from ?_]; exact HB
  rw [← map_smul (portal n)]; congr 1; refine Prod.ext rfl ?_; change (↑(r*t):ℂ)= r • (t:ℂ); rw [Complex.ofReal_mul,Complex.real_smul]
end YM.MSbar.Pole.Sew.Thread
