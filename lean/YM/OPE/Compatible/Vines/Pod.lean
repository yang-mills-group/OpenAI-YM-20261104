import YM.OPE.Compatible.Vines.Shafts
/-! Gust & graded vanish with foreign polynomial legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{T I:Type*}
namespace Script
open Page
-- multiadd colors consumed through budget shift monotone k controls all branches
lemma quietAdd {v w:fieldX T}{d:ℕ}(h:Quiet v d)(hp:Quiet w d):Quiet (v+w) d:=by
    obtain ⟨a,ha,hg⟩:=h; obtain ⟨b,hb,ht⟩:=hp; refine ⟨a+b,by positivity,fun i=>?_⟩; rw [Pi.add_apply,add_mul]; exact (norm_add_le ..).trans (add_le_add (hg _) (ht _))
variable {x y z:Fin r→ fieldX T}{p:Script T r}{l: Fin r→ℕ}
lemma choir (i:Fin r)(hp:soot m p c)(h:Glob y l)(hq:Glob z l)(gh:∑ i,l i≤m)(ha:x i=y i+z i)(hv:∀ j≠i,x j=y j ∧ x j=z j): wholeX p x=wholeX p y+wholeX p z:=by
   unfold wholeX; rw [← (wordSum hp h gh).tsum_add (wordSum hp hq gh)]
   refine tsum_congr fun a=> ?_; rw [← mul_add]; apply congr_arg (p a * ·); unfold wordX
   rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase _ (fun j=> y j (a j)) (mem_univ i),← mul_prod_erase _ (fun j=> z j (a j)) (mem_univ i),ha,Pi.add_apply, add_mul]
   congr 1
   · exact congr_arg (y i (a i) * ·) (prod_congr rfl (fun j hj=>congr_fun (hv j (ne_of_mem_erase hj)).1 (a j))) -- possible dep rewriting
   exact congr_arg (z i (a i) * ·) (prod_congr rfl (fun j hj=>congr_fun (hv j (ne_of_mem_erase hj)).2 (a j)))
lemma choir_scalar (i:Fin r)(p:Script T r)(k:ℝ)(ha:x i=k • y i)(hv:∀ j≠i,x j=y j): wholeX p x=k *wholeX p y:=by
   unfold wholeX; rw [← tsum_mul_left]; refine tsum_congr fun a=>?_; unfold wordX; rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase _ (fun j=>y j (a j)) (mem_univ i), Finset.prod_congr rfl (fun j hj=> congr_fun (hv j (ne_of_mem_erase hj)) (a j)),ha,Pi.smul_apply,smul_eq_mul]; ring
def Low (v:fieldX T)(d:ℕ):Prop:=∀ t:T, ∃ f∈Flavor Axis d,∀ p:Cover,v (p,t)=f (translit p)
lemma low_sub {x y:fieldX T}(h:Low x d)(hp:Low y d): Low (x-y) d:= fun t=>by
    obtain ⟨f,hf,hx⟩:=h t; obtain ⟨g,hg,hy⟩:=hp t; exact ⟨f-g,(Flavor _ _).sub_mem hf hg,fun p=>by simp [hx,hy]⟩
variable [Fintype T]
lemma low_quiet {u:fieldX T}(h:Low u d):Quiet u d:=by
    choose f H hf using h; choose c hc hh using fun i=> tasting_cost (H i); refine ⟨∑ i,c i, sum_nonneg fun i _=> hc i,fun ⟨p,t⟩=>?_⟩; rw [hf]; exact (hh t _).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>hc i) (mem_univ t)) (by unfold poise; positivity))
omit [Fintype T] in
lemma prod_flower (h:∀ i:Fin r,Low (x i) (l i))(i:Ink T r): ∃ f∈Flavor (Keys r) (∑ j,l j), ∀ z:Bin r,wordX x (syn z i)= f (translit z):=by
    choose f H hf using fun j=> h j (i j)
    let g (j:Fin r) (v:Lieu (Keys r)):= f j (curry v j); have hh(j):g j∈Flavor (Keys r) (l j):=flavor_diagonal (fun v:Lieu (Keys r)=>curry v j) (fun i=> flavor_position _) (H j)
    have he(s:Finset (Fin r)): (∏ j∈s,g j)∈Flavor (Keys r) (∑ j∈s,l j):=by
        induction s using Finset.induction_on with
        | empty=>simp only [prod_empty,sum_empty]; exact flavor_one _
        | insert j s hj ih=> rw [prod_insert hj,sum_insert hj]; exact flavor_prod (hh _) ih
    refine ⟨∏ j,g j, he _,fun z=>?_⟩; unfold wordX; rw [Finset.prod_apply]; exact prod_congr rfl fun j _=>hf j _
lemma hail (hp:soot m p c) (h:∀ i:Fin r,Low (x i) (l i))(hg: ∑ i,l i≤m)(hk:∑ i,l i< n)(ht:Bells p n):wholeX p x=0:=by
    let e:Ink T r× Bin r≃Page T r:=Equiv.trans (Equiv.prodComm ..) (blurb ..)
    let f(i):= p i*wordX x i; have hP: Summable (f ∘ e):=e.summable_iff.mpr (wordSum hp (fun i=>low_quiet (h i)) hg)
    change (∑' i,f i)=_; rw [← e.tsum_eq f]; change (∑' i,(f∘e) i)=_; rw [hP.tsum_prod,tsum_fintype]; apply Finset.sum_eq_zero; intro i _; obtain ⟨g,H,hh⟩:=prod_flower h i; change (∑' j:Bin r,sliceP p i j * wordX x (syn j i))=_; simp_rw [hh];exact wells (ht i) H hk hg (slices hp _)
end Script
end YM.OPE.Flume
