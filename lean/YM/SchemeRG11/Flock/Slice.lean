import YM.SchemeRG11.Flock.Ringlet
/-! Contravariant grading across power-mixed field vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Flock
open Function Pert MvPolynomial Haze Submodule
variable {R S I J K:Type*}[CommRing R][CommRing S]
abbrev rankW(i:I→ℕ)(s:I→₀ℕ):=Finsupp.weight i s
namespace Crest
variable {F:I→ℕ}{G:J→ℕ}{m n:ℕ}{f f' g g':Paper I R}
abbrev rake := (weightedHomogeneousComponent (R:=R) F n)
def hill(i:I→ℕ)(n:ℕ):Submodule R (Paper I R):= MvPolynomial.restrictSupport R {s| n≤rankW i s}
def Starts (i:I→ℕ)(n:ℕ)(f p:Paper I R):Prop:= f∈hill i n ∧ weightedHomogeneousComponent i n f=p
open scoped Classical Pointwise
lemma ranks (h:f∈hill F n){s:I→₀ℕ}(hp:s∈f.support): n≤rankW F s:= MvPolynomial.mem_restrictSupport_iff R |>.mp h hp
lemma begins (hp:IsWeightedHomogeneous F f m): Starts F m f f:=⟨(mem_restrictSupport_iff R).mpr (fun _ hb=>show _≤_ from (hp (mem_support_iff.mp hb)).ge), hp.weightedHomogeneousComponent_same⟩
lemma disappears {s:I→₀ℕ}(h:f∈hill F n)(p:rankW F s<n): f.coeff s=0:=by by_contra! hw; exact not_lt.mpr (ranks h (MvPolynomial.mem_support_iff.mpr hw)) p
lemma foot (h:f∈hill F m)(k:g∈hill F n):f*g∈hill F (m+n):=by apply (mem_restrictSupport_iff R).mpr; intro s hs; obtain ⟨i,hi,j,hj,rfl⟩ := Finset.mem_add.mp (support_mul _ _ hs); change m+n≤_; unfold rankW; rw [_root_.map_add]; exact add_le_add (ranks h hi) (ranks k hj)
lemma spike (h:f∈hill F m){a:ℕ}(ha:a<m): weightedHomogeneousComponent F a f=0:=by
 ext i; rw [coeff_weightedHomogeneousComponent,coeff_zero]; split
 · next w=> exact disappears h (lt_of_eq_of_lt w ha)
 rfl
lemma Starts.prod (h:Starts F m f f')(k:Starts F n g g'): Starts F (m+n) (f*g) (f'*g'):=by
 refine ⟨foot h.1 k.1,?_⟩; rw [← h.2,← k.2]; ext s; rw [coeff_weightedHomogeneousComponent]; split
 · next w=>
    rw [coeff_mul,coeff_mul]; apply Finset.sum_congr rfl; intro a ha
    rw [coeff_weightedHomogeneousComponent,coeff_weightedHomogeneousComponent]
    by_cases hg:g.coeff a.2=0
    · simp [hg]
    by_cases hf:f.coeff a.1=0
    · simp [hf]
    have hp:m≤ rankW F a.1:=ranks h.1 (mem_support_iff.mpr hf)
    have hq:n≤ rankW F a.2:=ranks k.1 (mem_support_iff.mpr hg)
    rw [← Finset.mem_antidiagonal.mp ha,map_add] at w; unfold rankW at *; rw [if_pos (by omega), if_pos (by omega)]
 next w=>
   symm; by_contra! hr; exact w ((IsWeightedHomogeneous.mul (weightedHomogeneousComponent_mem F f m) (weightedHomogeneousComponent_mem F g n)) hr)
lemma Starts.powers (h:Starts F m f f')(p:ℕ): Starts F (p • m) (f^p) (f'^p):=by induction p with | zero=>rw [zero_smul,pow_zero,pow_zero]; exact begins (isWeightedHomogeneous_one ..) | succ t ih=>rw [succ_nsmul,pow_add,pow_add,pow_one,pow_one]; exact ih.prod h
lemma Starts.fin (f p:J→Paper I R)(g:J→ℕ)(k:Finset J)(h:∀i∈k,Starts F (g i) (f i) (p i)):Starts F (∑i∈k,g i) (∏i∈k,f i) (∏i∈k,p i):=by induction k using Finset.induction_on with
 | empty=>rw [Finset.sum_empty,Finset.prod_empty,Finset.prod_empty]; exact begins (isWeightedHomogeneous_one ..)
 | insert i k hi ih=>rw [Finset.sum_insert hi,Finset.prod_insert hi,Finset.prod_insert hi]; exact (h i (by simp)).prod (ih fun j hq=> h j (by simp [hq]))
lemma pool (f p:J→Paper I R)(k:Finset J)(h:∀i∈k,Starts F m (f i) (p i)):Starts F m (∑i∈k,f i) (∑i∈k,p i):=by
 refine ⟨Submodule.sum_mem _ (fun i e=>(h i e).1),?_⟩; rw [_root_.map_sum]; exact Finset.sum_congr rfl fun i e=>(h i e).2
lemma cascade (U V:Paper J R→ₐ[R] Paper I R)(h:∀i, Starts F (G i) (U (X i)) (V (X i))) (g:Paper J R)(hp:IsWeightedHomogeneous G g m): Starts F m (U g) (V g):=by
 rw [← g.support_sum_monomial_coeff,map_sum,map_sum]; apply pool; intro i hi
 rw [← hp (mem_support_iff.mp hi),Finsupp.weight_apply, monomial_eq, _root_.map_mul,map_mul]
 simp_rw [Finsupp.sum,Finsupp.prod,map_prod,map_pow]
 rw [show ∀ x:R, U (C x)=C x from fun x=>U.commutes x, show ∀ x:R,V (C x)=C x from fun x=> V.commutes x]
 exact (zero_add (∑j∈i.support,i j • G j)) ▸ (begins (isWeightedHomogeneous_C ..)).prod (Starts.fin _ _ _ i.support fun j _=>(h j).powers _)
lemma graded (U:Paper J R→ₐ[R] Paper I R)(h:∀i,IsWeightedHomogeneous F (U (X i)) (G i))(f:Paper J R)(hp:IsWeightedHomogeneous G f m): IsWeightedHomogeneous F (U f) m:=(cascade U U (fun i=>begins (h i)) f hp).2 ▸ weightedHomogeneousComponent_mem F (U f) m
lemma teeters (U:Paper J R→ₐ[R] Paper I R)(h:∀i,IsWeightedHomogeneous F (U (X i)) (G i))(g:Paper J R): U (weightedHomogeneousComponent G n g) = weightedHomogeneousComponent F n (U g):=by
 induction g using MvPolynomial.induction_on' with
 | monomial s a=>
   have he: IsWeightedHomogeneous G (monomial s a) (rankW G s):= isWeightedHomogeneous_monomial _ _ _ rfl
   have hz:= graded U h _ he
   by_cases ht:n=rankW G s
   · rw [ht,he.weightedHomogeneousComponent_same,hz.weightedHomogeneousComponent_same]
   rw [he.weightedHomogeneousComponent_ne _ ht,hz.weightedHomogeneousComponent_ne _ ht,map_zero]
 | add a b ha hb=> simp only [map_add,ha,hb]
lemma mapped (U:R→+* S)(hp:IsWeightedHomogeneous F f n): IsWeightedHomogeneous F (MvPolynomial.map U f) n:=fun _ h=>hp (mem_support_iff.mp (support_map_subset _ _ (mem_support_iff.mpr h))) -- check
end Crest
end YM.SchemeRG11.Flock
