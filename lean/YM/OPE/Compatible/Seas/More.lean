import YM.OPE.Compatible.Tides.Vivid
/-!
# harm reaches. eve is unaffected by isolated native shifts.T
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam.Port
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Next.Rank.Radian (dV)
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{d:ℝ}{g h:ℕ→ Cover→ℝ}{k j:ℕ}
lemma unstalk (x:Cover)(g:ℕ→Cover→ℝ)(l:List Axis):stalkP l (shutter x g)=shutter x (stalkP l g):=by
      induction l generalizing g with
      | nil=> rfl
      | cons a l ih=>
        rw [← streak,show smear a (shutter x g)= shutter x (smear a g) from ?_]; rw [ih,streak]
        funext i z; unfold smear numDiff shutter; rw [add_right_comm z]
lemma flutter (hp:Port U d k g)(x:Cover): Sake U (k+1) (fun i=>g i x-g i 0):=by
    generalize he:size x=t; induction t using Nat.strong_induction_on generalizing x with
    | h n ih=>
      by_cases hw:x=0; · subst x;simp_rw [sub_self]; exact sake_zero ..
      obtain ⟨i,y,hv,hx⟩:=stride x hw; rw [he] at hv
      have L:=ih (size y) (by omega) y rfl
      rcases hx with hx|hx <;> subst x
      · obtain ⟨p,hp⟩:=(hp.split i).lo.sell y
        rw [show (fun j=>g j _-g j 0)=(fun j=>smear i g j y)+(fun j=>g j y-g j 0) from funext fun j=>by rw [Pi.add_apply]; unfold smear numDiff;abel]; exact hp.1.fuse L
      obtain ⟨p,hp⟩:=(hp.split i).lo.sell (y-stint i)
      rw [show (fun j=>g j _-g j 0)= -(fun j=> smear i g j (y-stint i))+(fun j=> g j y-g j 0) from funext fun j=>by rw [Pi.add_apply,Pi.neg_apply];unfold smear numDiff; rw [sub_add_cancel];abel]; exact hp.1.dark.fuse L
lemma shrivel {f:ℕ→ℝ}(hp:Sake U (k+1) f): Tendsto (fun i=>(U.h i^k)⁻¹*f i) atTop (𝓝 0):=by
   apply Sake.flop (U:=U) (m:=1) _ zero_lt_one
   obtain ⟨C,hC,h⟩:=hp; refine ⟨C,hC,fun i=>?_⟩; have he:= U.h_pos i; rw [norm_mul,Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left (h i) (by positivity)).trans (le_of_eq ?_); rw [pow_succ,pow_one]; field_simp
lemma flutter_slit (hp:Port U d k g)(x: Cover): Tendsto (fun i=>(U.h i^k)⁻¹*g i x) atTop (𝓝 (slit U k g)):=by
   have ht:=shrivel (flutter hp x); have h:=hp.lo.slit.2.2; simpa only [mul_sub,sub_add_cancel,zero_add] using! ht.add h
lemma eve_pass(hp:Port U d k g)(x:Cover): eve U k j (shutter x g)=eve U k j g:=by
   unfold eve; apply Finset.sum_congr rfl; intro i hi; rw [← (cardA _).1 hi,← Multiset.length_toList,unstalk, show slit U _ (shutter x (stalkP i.toList g))= slit U (k+i.toList.length) (stalkP i.toList g) from tendsto_nhds_unique (((hp.arms i.toList).pass x).lo.slit.2.2) ?_] -- underscore
   have ht:= flutter_slit (hp.arms i.toList) x; simpa only [shutter,zero_add] using ht
lemma nullC (hs:0<d):Port U d k (0:ℕ→Cover→ℝ):=by
    intro l; rw [show stalkP l 0=0 from funext fun i=> dvol_zero _]; constructor; · exact hs
    · intro x; simp only [Pi.zero_apply,mul_zero]; exact cleared_zero _
    intro r hr; exact ⟨0,le_rfl,Eventually.of_forall fun i x _=>by simp⟩
lemma slit_plus (hf: Port U d k g)(hp:Port U d k h): slit U k (g+h)=slit U k g+slit U k h:=by
    apply tendsto_nhds_unique (hf.glue hp|>.lo.slit.2.2); simpa only [Pi.add_apply,mul_add] using! hf.lo.slit.2.2.add hp.lo.slit.2.2
lemma eve_plus (hf: Port U d k g)(hp:Port U d k h): eve U k j (g+h)=eve U k j g+eve U k j h:=by
    unfold eve; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; rw [← (cardA _).1 hi,← Multiset.length_toList, show stalkP i.toList (g+h)=_ from (show stalkP i.toList (g+h)= stalkP i.toList g+stalkP i.toList h from funext fun z=>funext fun x=> run_add ..),slit_plus (hf.arms _) (hp.arms _),add_smul]
lemma neg_s (hp:Port U d k g):Port U d k (-g):=by
    intro l; rw [show stalkP l (-g)= -(stalkP l g) from funext fun i=>funext fun x=>by change dvol l (-g i) x= _; rw [←zero_sub,run_sub,dvol_zero];simp [stalkP]]
    constructor
    · exact hp.lo.inside
    · intro x; let L:= (-1:ℝ) • ContinuousLinearMap.id ℝ ℝ; convert! ((hp l).remit x).glu L using 2 with i; change _*(-_)=L _; simp [L] -- hints
    intro r hr; obtain ⟨C,hC,H⟩:= (hp l).near r hr; exact ⟨C,hC,H.mono (fun i hi x hx=> by simpa using hi _ hx)⟩
lemma eve_null (U:Gloam)(k j:ℕ): eve U k j (0:ℕ→Cover→ℝ)=0:=by
   have ht:= nullC (U:=U) (k:=k) (d:=1) zero_lt_one; apply add_left_cancel (a:=eve U k j 0); rw [← eve_plus ht ht, zero_add,add_zero]
lemma neg_e (hp: Port U d k g): eve U k j (-g)= -eve U k j g:=by rw [← add_left_cancel_iff (a:=eve U k j g),← eve_plus hp hp.neg_s,add_neg_cancel,add_neg_cancel,eve_null]
lemma oneP (hs:0<d):Port U d 0 (fun _ _=>1):=by
   intro l; cases l with
   | nil=> refine ⟨hs,fun x=>?_ , fun r _=>?_⟩
           · change Cleared _ (fun i=> (U.h i^0)⁻¹ * 1); simpa only [pow_zero,inv_one] using! (Cleared.always (U:=U) (x:=1*1))
           refine ⟨1,zero_le_one,Eventually.of_forall (fun i x h=>?_)⟩; change ‖(1:ℝ)‖ ≤ 1*U.h i^0;simp
   | cons a l=> rw [← streak,show smear a (fun _ _=>(1:ℝ))=0 from funext fun i=>funext fun y=>by simp[smear,numDiff]]; rw [show 0+(a::l).length=1+l.length from by simp;omega]; exact nullC hs l -- length equation
lemma zeroEv {a:ℕ→Cover→ℝ}(hp:Port U d k a)(h:∀ x:Cover, ∀ᶠ i in atTop, a i x=0): eve U k j a=0:=by
    have hx(l:List Axis)(x:Cover):∀ᶠ i in atTop,dvol l (a i) x=0:=by
        induction l generalizing x with
        | nil=> exact h _
        | cons z l ih=> filter_upwards [ih (x+stint z), ih x] with i hi hh; change dvol l _ _-dvol l _ _ = _; rw [hi,hh]; simp
    unfold eve; refine Finset.sum_eq_zero (fun m hm=>?_); suffices he: slit U _ (stalkP m.toList a) = 0 by rw [he];simp
    rw [← (cardA _).1 hm,← Multiset.length_toList]; apply tendsto_nhds_unique (hp.tap _); exact tendsto_const_nhds.congr' ((hx m.toList 0).mono (fun i hi=> by dsimp only; rw [hi,mul_zero]))
end YM.OPE.Balsam.Port
