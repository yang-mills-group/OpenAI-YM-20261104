import YM.WilsonCoeffUV.Thermo.VacuumCalculus
/-!
# Coarse-residue packing of prices. We can restore width per step.
The possibly alarming width prefactor here depends ONLY on coarse width.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {L c f:Side} {U α β V ι : Type*}{k r l j:ℕ}{s C : ℝ}

-- pack tile
private def areaL (L:Side) (x:Cover×Site L): Cover:= L.val • x.1 + lift x.2
lemma tile_design (L:Side) : Bijective (fun x:Cover×Site L=> L.val • x.1+lift x.2):= by
  let g : Ratio 1 L:= ⟨L,by simp⟩
  have he (p:Cover)(x:Site L): wrap L (areaL L (p,x))=x:=by
    haveI : Subsingleton (Site 1) := Fintype.card_le_one_iff_subsingleton.mp (by rw [site_card]; simp)
    simp only [areaL]; rw [map_add,wrap_lift]; rw [show wrap L (L.val • p)= g.embed (wrap 1 p) from (g.embed_wrap _).symm, Subsingleton.elim (wrap 1 p) (0:Site 1), show g.embed 0=0 from map_zero g.root,zero_add]
  refine ⟨?_,?_⟩
  · rintro ⟨a,b⟩ ⟨x,y⟩ hx; change areaL _ _=areaL _ _ at hx
    have hh : b=y:= by rw [← he a b,hx,he]
    subst b
    unfold areaL at hx
    exact Prod.ext (smul_right_inj L.property.ne' |>.mp (add_right_cancel hx)) rfl
  intro x
  obtain ⟨z,hz⟩:= cover_of_eq (lift (wrap L x)) x (wrap_lift _)
  exact ⟨(z,wrap L x), show _ from (add_comm _ _).trans hz.symm⟩

def panel (L : Side) (α:Type*) : Cloth (Co L α) ≃ Cloth α := ((Equiv.prodAssoc _ _ _).symm.trans ((Equiv.ofBijective _ (tile_design L)).prodCongr (Equiv.refl _)))
lemma panel_wrap (g:Ratio c f)(x:Cloth (Co g.count α)) : foldUnder f (panel g.count α x)=(splitCo g α).symm (foldUnder c x):=by
  change (wrap f (g.count.val • x.1+lift x.2.1),x.2.2)= (g.embed (wrap c _) + wrap f (lift x.2.1),x.2.2)
  rw [map_add,← g.embed_wrap]
lemma split_move (g:Ratio c f)(b:Site c)(x:Co c (Co g.count α)):
    (splitCo g α).symm (jog b x)= jog (g.embed b) ((splitCo g α).symm x) := by
  change (g.embed (b+x.1)+_,_)=(g.embed b+(g.embed x.1+_),_)
  rw [show g.embed (b+x.1)=_ from (show g.embed _=g.embed b+g.embed x.1 from map_add g.root _ _), add_assoc]; rfl

private lemma size_tick (L:Side)(x:Cover): size (L.val • x)=L.val*size x:=by unfold size; simp [Finset.mul_sum,Int.natAbs_mul]
lemma tor_embed (g:Ratio c f)(b a:Site c): (tor f).gap (g.embed b) (g.embed a)=g.count.val*(tor c).gap b a:= by
  change size (lift (g.root a-g.root b))=_; rw [←map_sub, g.root_embed, Ratio.lift_embed]; exact size_tick ..
lemma crowd (x:Site L): size (lift x) ≤ 4*L.val:= by
    refine le_trans (b:=∑ _ : Axis,L.val) (Finset.sum_le_sum (fun i _=>?_)) (by simp [Axis]); have he:= lift_centers x i; omega
private lemma summit [Fintype ι] (d:Distance U)(x:ι→U){m l a :ℕ}(he:∀ i j,l*d.gap (x i) (x j)≤m+a): l*league d x≤m+a:=by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he=> simp [league]
  | inr he'=>
    obtain ⟨i,hi,h⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) Finset.univ_nonempty (fun i=> Finset.univ.sup (fun j=> d.gap (x i) (x j)))
    obtain ⟨j,hj,g⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) Finset.univ_nonempty (fun j=>d.gap (x i) (x j))
    rw [league,h,g]; exact he i j
private lemma bridge_size (d:Distance U)(f h: Fin r→U) {k l p:ℕ} {X:Type*}{D:Distance X}(x:Fin r→X)(e:∀ i j, d.gap (f i) (f j)= k*D.gap (x i) (x j))(q:∀ i,d.gap (f i) (h i) ≤ l*p):
    k * league D x≤league d h+2*l*p:=by
   apply summit; intro i j; rw [←e]; have hw:=leg_le d h i j; have ht:=d.tri (f i) (h i) (f j); have hy:=d.tri (h i) (h j) (f j); rw [d.swap (h j)] at hy; rw [mul_assoc]; have he:=q i; have hg:=q j; omega
lemma cover_pack (m:Fin r→Cloth (Co L α)) : L.val*soar terrain m≤soar terrain (panel L α ∘ m)+8*L.val:= by
   apply bridge_size terrain (fun i=> L.val • (m i).1) (Prod.fst ∘ panel L α ∘ m) (l:=4) (p:=L.val) (Prod.fst ∘ m)
   · intro i j; change size (L.val • (m j).1-L.val • (m i).1) = _; rw [← smul_sub,size_tick]; rfl
   intro i; change size (L.val • _ + lift (m i).2.1-L.val • _ )≤_; rw [add_sub_cancel_left]; exact crowd _
lemma local_pack (g:Ratio c f)(m:Fin r→Co c (Co g.count α)): g.count.val*soar (tor c) m ≤ soar (tor f) ((splitCo g α).symm ∘ m)+8*g.count.val:= by
    apply bridge_size (tor f) (fun i=>g.embed (m i).1) (Prod.fst ∘ (splitCo g α).symm ∘ m) (l:=4) (p:=g.count.val) (Prod.fst ∘ m)
    · intro i j; exact tor_embed g ..
    intro i; change size (lift (g.embed (m i).1+ wrap f (lift (m i).2.1)-_)) ≤ _; rw [add_sub_cancel_left]; exact (wrap_size f _).trans (crowd _)
private lemma packing (L:Side){k j:ℕ}(h:L.val*k≤ j+8*L.val)(hp:0≤s) : Real.exp (-(s/L.val)*j)≤ Real.exp (8*s)*Real.exp (-s*k) := by
  rw [← Real.exp_add,Real.exp_le_exp]; have he : (L.val:ℝ)>0:= by positivity
  rw [neg_div', div_mul_eq_mul_div,div_le_iff₀ he]
  have hh : (L.val:ℝ)*k≤j+8*L.val:= by exact_mod_cast h
  linarith only [mul_le_mul_of_nonneg_left hh hp]

variable [NormedAddCommGroup V]

def turnTen (q:U≃α)(P:Ten V U r): Ten V α r:=fun i=> P (q.symm ∘ i)
def bend (q:U≃α)(P:Gen V U) : Gen V α:= fun i=> turnTen q (P i)
abbrev tiles (L:Side)(P:Gen V (Cloth α)) : Gen V (Cloth (Co L α)) := bend (panel L α).symm P
lemma gather_coast {P:Ten V (Cloth α) r}(hs:0≤s)(h:Amber terrain (s/L.val) C P) : Amber terrain s (C*Real.exp (8*s)) (turnTen (panel L α).symm P) := ⟨mul_nonneg h.1 (by positivity),fun x => (h.2 (panel L α ∘ x)).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (packing _ (cover_pack x) hs) h.1)⟩
lemma gather_isle (g:Ratio c f){P: Ten V (Co f α) r}(hs:0≤s)(h:Amber (tor f) (s/g.count.val) C P): Amber (tor c) s (C*Real.exp (8*s)) (turnTen (splitCo g α) P) := ⟨mul_nonneg h.1 (by positivity),fun x=>(h.2 ((splitCo g α).symm ∘ x)).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (packing _ (local_pack g x) hs) h.1)⟩
omit [NormedAddCommGroup V] in
lemma stroller (g:Ratio c f){P:Ten V (Co f α) r}(h:stroll P): stroll (turnTen (splitCo g α) P) := by
  intro b x; unfold turnTen; rw [show _ ∘ (jog b ∘ x)=_ from funext (fun i=> (show (splitCo g α).symm (jog b (x i))= (jog (g.embed b) ∘ (splitCo g α).symm ∘ x) i from split_move g b _))]; exact h _ _

-- rank-zero density scales by exact fine factor
variable [NormedSpace ℝ V]
def plants (L:Side)(P:Gen V (Cloth α)):Gen V (Cloth (Co L α)):=fun i=> if i=0 then Fintype.card (Site L) • tiles L P i else tiles L P i
omit [NormedSpace ℝ V] in
lemma plant_pt (L:Side)(P:Gen V (Cloth α))(r): plants L P (r+1)=tiles L P (r+1):= if_neg (by omega)
omit [NormedSpace ℝ V] in
lemma plant_coin (L:Side)(P:Gen V (Cloth α)): plants L P 0=Fintype.card (Site L) • tiles L P 0 := if_pos rfl

abbrev ratioN (L c : Side) : Ratio c (c*L):= ⟨L,rfl⟩
-- full tail all Side
lemma multi_end (L:Side): Tendsto (fun n:Side=> n*L) atTop atTop := by
  refine tendsto_atTop.2 fun t=> (eventually_ge_atTop t).mono (fun n hn=> hn.trans ?_)
  exact Nat.le_mul_of_pos_right _ L.property
lemma within_bend (q:U≃α)(P:Ten V U r)(c:ℝ): turnTen q (c•P)=c•turnTen q P:=rfl
variable {P:(n:Side)→ Gen V (Co n α)}{Q:Gen V (Cloth α)}
lemma per_bend (n:Side): dilute (fun n=>bend (splitCo (ratioN L n) α) (P (n*L)) 0 ) n=(Fintype.card (Site L):ℝ) • turnTen (splitCo (ratioN L n) α) (dilute (fun v=>P v 0) (n*L)) := by
   simp only [dilute,↓reduceIte,within_bend,smul_smul]
   have he : (Fintype.card (Site (n*L)):ℝ)=(Fintype.card (Site L):ℝ)*Fintype.card (Site n):= by
     rw [Fintype.card_congr ((ratioN L n).splitSites), Fintype.card_prod,Nat.cast_mul,mul_comm]
   rw [he, show (Fintype.card (Site L):ℝ)*_=(Fintype.card (Site n):ℝ)⁻¹ from ?_]; rfl
   rw [mul_inv]; have H : (Fintype.card (Site L) : ℝ)≠0:=by positivity
   field_simp
lemma bend_yields (h:Yields (fun v=>P v r) (Q r)):
    Yields (fun n=>bend (splitCo (ratioN L n) α) (P (n*L)) r) (plants L Q r):=by
  have Hx:= ((multi_end L).eventually h.strolls).mono (fun n hn=>stroller (ratioN L n) hn)
  cases r with
  | zero=>
    obtain ⟨s,a,hp,H⟩:=h.fees
    have H:= (multi_end L).eventually H
    refine ⟨fun x=> ?_,Hx,s,|(Fintype.card (Site L):ℝ)| *(a*Real.exp (8*s)),hp,?_⟩
    · simp_rw [per_bend (L:=L) (P:=P),plant_coin,← Nat.cast_smul_eq_nsmul (R:=ℝ), Pi.smul_apply]
      refine tendsto_const_nhds.smul (((h.point ((panel L α) ∘ x)).comp (multi_end L)).congr' ?_)
      refine Eventually.of_forall fun n=>?_
      exact congr_arg _ (Subsingleton.elim (foldUnder (n*L) ∘ (panel L α ∘ x)) ((splitCo (ratioN L n) α).symm ∘ (foldUnder n ∘ x)))
    refine H.mono (fun n hn=>?_); rw [per_bend (L:=L) (P:=P)]; exact (gather_isle (ratioN L n) hp.le (hn.mono (div_le_self hp.le (by exact_mod_cast L.property)))).smul _
  | succ r=>
    obtain ⟨s,a,hp,H⟩:=h.fees
    refine ⟨fun x=> ?_,Hx,s,a*Real.exp (8*s),hp,((multi_end L).eventually H).mono fun n hn=>?_⟩
    · simp only [dilute, Nat.succ_ne_zero,↓reduceIte]
      refine ((h.point ((panel L α) ∘ x)).comp (multi_end L)).congr' (Eventually.of_forall fun n=>?_)
      simp only [Function.comp_apply,dilute,Nat.succ_ne_zero,↓reduceIte]
      exact congr_arg _ (funext fun i=> panel_wrap (ratioN L n) (x i))
    rw [dilute,if_neg (by omega)] at hn ⊢
    exact gather_isle (ratioN L n) hp.le (hn.mono (div_le_self hp.le (by exact_mod_cast L.property)))
end YM.WilsonCoeffUV.Bank
