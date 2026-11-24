import YM.SchemeConversionRG11.FirstW.Ore.Datum
/-! Same normalized joint Replica, product erasures incl Wick offsets. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Lattice Pert Align Position Maxwell MvPolynomial Warp
open scoped BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{n:Side}{r d k:ℕ} (p:Players G r d)(s:Fin r)(o:Full.Grid n r)(h:ℝ)
def apart (G:Gauge) (d:ℕ) (s:Fin r): Finset (At G r d):= Finset.univ.filter fun a=> a.1≠s
def air := (update p s (1:Part G d))
abbrev dues (z w:At G r d):ℝ := Align.corrected h o z.1 w.1 z.2.val w.2.val
lemma silver (a b:At G r d): coins (hall G n r d h) (teams o h a) (teams o h b) = ↑(dues o h a b) := by unfold coins teams; exact node_wage ..
lemma pays_slot : ∃ L: Part G d→ₗ[ℂ] ℂ,∀ v,L v=ZeroR o h (update p s v) := by
 -- recipe is MLM? read
 let W: Part G d→ₗ[ℂ] Labels.Pol G:= (rename Subtype.val).toLinearMap
 let M:= (PowerSeries.coeff (R:=ℂ) 0).compMultilinearMap ((recipe d h o).compLinearMap fun _=> W)
 exact ⟨M.toLinearMap p s,fun v=>by simp only [M,MultilinearMap.toLinearMap_apply,LinearMap.compMultilinearMap_apply,MultilinearMap.compLinearMap_apply,PowerSeries.coeff_zero_eq_constantCoeff];rfl⟩
lemma feed_air (v:Part G d) : feed (update p s v)=rename (Prod.mk s) v* feed (air p s) := by
 let f(q:Players G r d)(i:Fin r): Cache (At G r d):=rename (Prod.mk i) (q i); have he(q:Players G r d): feed q= f q s * (∏ i ∈ Finset.univ.erase s, f q i) := (Finset.mul_prod_erase (a:=s) (s:=Finset.univ) (f q) (Finset.mem_univ _)).symm
 rw [he,he]; simp only [air,f,update_self, map_one,one_mul]; apply congrArg _; apply Finset.prod_congr rfl; intro x hx; rw [update_of_ne (Finset.mem_erase.mp hx).1,update_of_ne (Finset.mem_erase.mp hx).1]
lemma dict_comm (i j:At G r d) : dict i (dict j p)= dict j (dict i p) := by
 by_cases h:i.1=j.1
 · simp only [dict,h,update_self,update_idem];rw [show pderiv i.snd (pderiv j.snd (p j.fst))=pderiv j.snd (pderiv i.snd (p j.fst)) from commute ..]
 simp only [dict,update_of_ne h,update_of_ne (Ne.symm h)]; exact update_comm (Ne.symm h) ..  -- signature
lemma dict_b (i:At G r d)(h:i∈apart G d s)(v:Part G d): dict i (update p s v)=update (dict i p) s v:= by
 have hx: i.1≠s:=(Finset.mem_filter.mp h).2; simp only [dict, update_of_ne hx]; exact update_comm (Ne.symm hx) .. 
lemma slice1 (k:Who G d)(A:At G r d) (h:k=A.2): k.val=A.2.val:=h ▸ rfl -- unnecessary
lemma empty_air (a : At G r d)(t:Players G r d)(v: t s=1) (e:a∉apart G d s): ZeroR o h (dict a t)=0:=by
 have he : a.1=s:=by simpa only [apart,Finset.mem_filter,Finset.mem_univ,true_and, ne_eq,not_not] using e
 obtain ⟨L,H⟩:= pays_slot t s o h; rw [dict,he, ←H,v,pderiv_one,map_zero]
lemma air_mates (a : At G r d)(t : Players G r d)(hv : t s=1)(he:a∉apart G d s)(i:At G r d): ZeroR o h (dict i (dict a t))=0:=by
 by_cases hx:i∈apart G d s
 · rw [dict_comm t]; apply empty_air s o h a _ _ he; rw [dict, update_of_ne (Ne.symm (Finset.mem_filter.mp hx).2),hv]
 have hr(u:At G r d)(h:u∉apart G d s): u.1=s:=by simpa [apart] using h
 obtain ⟨L,H⟩:= pays_slot (dict a t) s o h
 rw [dict,hr i hx,←H,dict,hr a he,update_self,hv,pderiv_one,map_zero,map_zero]
-- native lines represented Wick offset in dues, actual normalized zeroth on common p
lemma gives_one (a:Who G d) : ZeroR o h (update p s (X a)) = ∑ i∈apart G d s,(↑(dues o h (s,a) i):ℂ)*ZeroR o h (dict i (air p s)):= by
 haveI := hall_G G n r d h
 let μ:=hall G n r d h; let X:=teams (G:=G) (d:=d) o h; let Q:=air p s
 have hc := one_bill μ X (feed Q) (X (s,a)) (fun i=> node_center ..) (node_center ..)
 rw [stand,feed_air]; unfold Deck.dotF; simp only [spend,rename_X,map_mul,eval_X];
 unfold X μ Q at hc; change payOne (hall G n r d h) (teams o h) (feed (air p s)) (teams o h (s,a))=_
 rw [hc]; simp only [d_feed,silver,←stand]
 symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi=>?_ ; rw [empty_air s o h i (air p s) (by simp [air]) hi,mul_zero]
lemma gives_two (a b:Who G d) : ZeroR o h (update p s (X a* X b))= (↑(dues o h (s,a) (s,b)):ℂ)*ZeroR o h (air p s)+ ∑ i∈apart G d s,∑ j∈apart G d s,(↑(dues o h (s,a) i*dues o h (s,b) j):ℂ)*ZeroR o h (dict j (dict i (air p s))) := by
 haveI:=hall_G G n r d h
 let Q:= air p s
 let V(i:Who G d)(j:At G r d):= (↑(dues o h (s,i) j):ℂ)
 have ht: ZeroR o h (update p s (X a* X b))=payTwo (hall G n r d h) (teams o h) (feed Q) (teams o h (s,a)) (teams o h (s,b)):=by
   rw [stand,feed_air]; simp only [dotF,payTwo,spend,map_mul,rename_X,eval_X,mul_assoc];rfl
 rw [ht,erase_two _ (teams o h) (feed Q) (teams o h (s,a)) (teams o h (s,b)) (fun i=>node_center ..) (node_center ..) (node_center ..)]; simp only [silver,d_feed,←stand,Complex.ofReal_mul,mul_assoc]
 unfold Q; congr 1; let S:=apart G d s; symm; let L(i j:At G r d):= V a i*(V b j*ZeroR o h (dict j (dict i Q)))
 change (∑ i∈S,∑ j∈S,L i j)=∑ i:At G r d,∑ j:At G r d,L i j
 trans ∑ i∈S,∑ j:At G r d,L i j; refine Finset.sum_congr rfl fun i hi=>?_ ; refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj=>?_ ; unfold L; rw [dict_comm Q,air_mates s o h _ _ (by simp [Q,air]) hj i,mul_zero,mul_zero]
 refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi=> Finset.sum_eq_zero fun j _=>by unfold L; rw [air_mates s o h _ _ (by simp [Q,air]) hi j,mul_zero,mul_zero]
end YM.RG11.FirstW.Deck
