import YM.SchemeConversionRG11.FirstW.Trice.Specs
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {n:Side}
lemma vapor_trac (F:Labels.Frames G)(hg:G.Simple)(d:Diorama T u p)(i j:P)(he:i≠j): Tendsto (fun k=> tracC (u k) (T.gap k) i j (SlateZ G)) atTop (𝓝 0):=by
 by_cases h:i=0; swap; · unfold tracC; exact tend_t _ _ fun a _=> tend_t _ _ fun b _=> tend_t _ _ fun c _=> wax_pair d hg F _ _ he h a b c
 subst i; have hp:Tendsto (fun k=>(2:ℂ)*tracC (u k) (T.gap k) 0 j (SlateZ G)) atTop (𝓝 0):= by
   simp_rw [tac2 j he.symm]; refine tend_t _ _ fun a _=> tend_t _ _ fun b _=> tend_t _ _ fun c _=> tend_t _ _ fun l _=>?_
   simpa only [mul_zero, zero_mul] using! (((out_charge d _ he.symm a l).const_mul (3*tau a b c)).mul (fortune d (dressed j (β b *β c) 1)))
 have h:=hp.const_mul (2:ℂ)⁻¹; simp only [←mul_assoc,inv_mul_cancel₀ (show (2:ℂ)≠0 by norm_num),one_mul, mul_zero] at h; exact h
section triples
variable {I:Type*}[DecidableEq I][Fintype I]{V:Type*}[AddCommMonoid V]
def pal (v:P× I) (f:P×I→V):= ∑ j∈(Finset.univ.filter fun x:P×I=> x.1≠v.1), f j -- unnecessary
omit [DecidableEq I] in
lemma feat (v:P)(f:P×I→V): (∑ j∈(Finset.univ.filter fun x:P× I=> x.1≠ v),f j) = ∑ i∈Finset.univ.erase v, ∑ j:I, f (i,j):= by
 rw [Finset.sum_filter, Fintype.sum_prod_type,show Finset.univ.erase v=Finset.univ.filter (fun x:P=> x≠v) from ?_, Finset.sum_filter]; swap; · ext; simp
 apply Finset.sum_congr rfl; intro j _; by_cases e:j=v <;> simp [e]
lemma feat2 (v w:P× I)(e:v.1≠w.1)(f:P×I→V) : (∑ j∈(Finset.univ.filter fun x:P×I=>x.1≠v.1)∩(Finset.univ.filter fun x:P×I=>x.1≠w.1),f j)= ∑ i∈((Finset.univ.erase v.1).erase w.1),∑ j:I, f (i,j):=by
 rw [show (Finset.univ.filter fun x:P×I=>x.1≠v.1)∩_ = Finset.univ.filter fun x=> x.1≠v.1∧x.1≠w.1 from ?_, Finset.sum_filter,Fintype.sum_prod_type]; swap; · ext; simp
 rw [show (Finset.univ.erase v.1).erase w.1= Finset.univ.filter fun x:P=> x≠v.1 ∧ x≠w.1 from ?_, Finset.sum_filter]; swap; · ext; simp [and_comm]
 apply Finset.sum_congr rfl; intro x _; by_cases h:x=v.1 <;> by_cases w:x=w.1 <;> simp [h,w, e] -- shadow
end triples
variable (o:Full.Grid n 3)(s:ℝ)(P₁:Players G 3 6)
private lemma capSym (a b c:At G 3 6): verbD o s P₁ a b c=verbD o s P₁ b a c:=by unfold verbD; rw [dict_comm P₁ b a]; congr 2; simp only [lap_shield,wheels,tower_sym (A:=arise s o a) (B:=arise s o b)]
private lemma capThr (a b c:At G 3 6): verbD o s P₁ a b c=verbD o s P₁ a c b:= by unfold verbD; rw [dict_comm (dict a P₁) c b]; congr 2; simp only [lap_shield,wheels,tower_cross (B:=arise s o b) (C:=arise s o c)]
def slitW (i j k:P) := ∑ a:Who G 6,∑ b: Who G 6,∑ c:Who G 6,verbD o s P₁ (i,a) (j,b) (k,c)
def spinC (i j k:P):= ∑ a:Who G 6,∑ b:Who G 6,∑ c:Who G 6, changeD o s P₁ (i,a) (j,b) (k,c)
lemma spinV_print : flowV P₁ o s=6 * slitW o s P₁ 0 1 2:= by
 let f:= slitW o s P₁; let V:=verbD o s P₁
 have he(i j k:P): f i j k=f j i k:= by unfold f slitW; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun c _=>capSym ..
 have hq(i j k:P): f i j k=f i k j:= by unfold f slitW; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun c _=>capThr ..
 let L(i:P):= ∑ j∈Finset.univ.erase i,∑ k∈(Finset.univ.erase i).erase j,f i j k; have H: flowV P₁ o s = ∑ i:P,L i:= by
    unfold flowV Star3 Deck.apart; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; dsimp only; simp_rw [feat] -- `f` under star binder
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j hj; have e:i≠j:= (Finset.mem_erase.mp hj).1.symm
    let f(a b:Who G 6):= V (i,a) (j,b); simp_rw [show ∀ a b:Who G 6,(∑ _x ∈ (Finset.univ.filter fun x:P× Who G 6=>x.1≠i)∩(Finset.univ.filter fun x:P× Who G 6=> x.1≠j),verbD o s P₁ (i,a) (j,b) _x)= _ from fun a b=>feat2 (i,a) (j,b) e (f a b)]
    conv_lhs=>arg 2; intro a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; rfl
 rw [H]; change (∑ i:P,L i)=6*f 0 1 2
 have hl(i:P) : L i=2*f i (foreL i) (aft i):= by unfold L; rw [flood_load i,Finset.sum_pair (Ne.symm (neg3 i))]; unfold foreL aft; rw [Finset.erase_insert (by simpa only [Finset.mem_singleton] using (Ne.symm (neg3 i))),Finset.pair_comm, Finset.erase_insert (by simpa only [Finset.mem_singleton] using neg3 i), Finset.sum_singleton,Finset.sum_singleton,hq i (Triad.lag i),two_mul]
 have hp : ∑ i:P,L i=L 0+L 1+L 2:= by simp [P,Fin.sum_univ_succ];abel
 rw [hp]; simp_rw [hl]; change 2*f 0 1 2+ 2*f 1 2 0+2*f 2 0 1= _; rw [hq 1, he 1,he 2,hq 0 2]; ring
end YM.RG11.FirstW.Branch
