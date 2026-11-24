import YM.SchemeRG11.Flock.Plink
/-!
Triangular realization, EXACT; permits projections with discretization corrections.
For each horizontal polynomial through height n. Finite-dimensional type above. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Outlook
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical
variable {G:Gauge} {n d w:ℕ}
def Ladder (n d:ℕ):Submodule ℝ (Sketch G n):=restrictSupport ℝ {s|rankW inkAge s ≤d}
def Eidolon (n d:ℕ): Submodule ℝ (Sketch G n) where
 carrier:={p|p∈Ladder n d ∧ Still p ∧ Solid p}
 zero_mem':=⟨Submodule.zero_mem _,by intro x u; simp,by intro x; simp⟩
 add_mem':=by rintro f g ⟨hf,fU,fs⟩ ⟨hg,gU,gs⟩; exact ⟨Submodule.add_mem _ hf hg,fun x u=>by rw [map_add,map_add,fU x u,gU x u],fun x=>by rw [map_add,map_add,fs x,gs x]⟩
 smul_mem':=by rintro c f ⟨a,b,h⟩; exact ⟨ Submodule.smul_mem _ c a,fun x u=>by rw [map_smul,map_smul,b],fun x=>by rw [map_smul,map_smul,h]⟩
def cliff {I:Type*}(w:I→ℕ)(m:ℕ) : Module.End ℝ (Paper I ℝ):=∑i∈Finset.range (m+1),weightedHomogeneousComponent w i
lemma keeps_i {I:Type*}(w:I→ℕ)(m:ℕ)(p:Paper I ℝ)(a:I→₀ℕ): (cliff w m p).coeff a=if rankW w a≤ m then p.coeff a else 0:=by simp [cliff, LinearMap.sum_apply, MvPolynomial.coeff_sum, coeff_weightedHomogeneousComponent,rankW]
lemma safety {q:Sketch G n}(p:q∈ Ladder n d): cliff inkAge d q=q:=by
 ext i; rw [keeps_i]; split
 · rfl
 next h=> by_contra! g; exact h ((MvPolynomial.mem_restrictSupport_iff ℝ).mp p (mem_support_iff.mpr (Ne.symm g)))
lemma ledge {q:Sketch G n}:cliff inkAge d q∈ Ladder n d:=by
 refine (MvPolynomial.mem_restrictSupport_iff ℝ).mpr ?_; intro i hi; have hx:=mem_support_iff.mp hi; rw [keeps_i] at hx; split at hx
 · assumption
 contradiction
lemma au {q:Sketch G n}(h:Still q)(g:Solid q):cliff inkAge d q∈ Eidolon n d:=by
 refine ⟨ledge,fun x u=>?_,fun x=>?_⟩
 · unfold cliff; rw [LinearMap.sum_apply,map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>still_gr (w:=i) h x u
 unfold cliff; rw [LinearMap.sum_apply,map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>solid_gr (w:=i) g x

structure Tab (F:Frames G)(m:ℕ) where
 p:pLabel G
 k:ℕ
 g:k≤m
 hom:IsWeightedHomogeneous generation p k
 free:(Maxwell.freeTable F).Field m
 reads:realCast p=(RawLabels.physicalLabel F m free).val
 neutral: Neutral p
variable {F:Labels.Frames G}
def plank (n:ℕ)(z:Tab F d):Sketch G n:=cliff inkAge d (showP G n z.p)
lemma skilled (z: Tab F d):plank n z∈Eidolon n d:= au (stable z.neutral) (stow _)
lemma fill (q:Sketch G n)(h:q∈Eidolon n d):q∈ Submodule.span ℝ (Set.range (plank n (F:=F) (d:=d))):=by
 let T:=Submodule.span ℝ (Set.range (plank n (F:=F) (d:=d)))
 suffices hs:∀ k:ℕ,∀ p:Sketch G n,p∈Eidolon n d→ p∈hill inkAge (d+1-k)→p∈T by
    apply hs (d+1) q h; rw [Nat.sub_self]; exact (MvPolynomial.mem_restrictSupport_iff ℝ).mpr (fun _ _=>Nat.zero_le _)
 intro k; induction k with
 | zero=>
   intro p hp hq; suffices H:p=0 by rw [H]; exact Submodule.zero_mem _
   ext i; rw [coeff_zero]; by_contra! he
   have hb:p∈ Ladder n d:=hp.1; have hz:rankW inkAge i≤d:=(MvPolynomial.mem_restrictSupport_iff ℝ).mp hb (mem_support_iff.mpr he); have hh:=ranks hq (mem_support_iff.mpr he); omega
 | succ k ih=>
   intro p hp hq; by_cases he:d<k
   · apply ih p hp; have hh:d+1-k= d+1-(k+1):=by omega
     rw [hh]; exact hq
   let v:=d+1-(k+1)
   have hv:v≤d:=by unfold v; omega
   let P:= weightedHomogeneousComponent inkAge v p
   obtain ⟨r,b,hr,hU,hH,H⟩:= cardinality (q:=P) (solid_gr hp.2.2) (still_gr hp.2.1) (weightedHomogeneousComponent_mem ..) hv F
   let A: Tab F d:=⟨r,v,hv,hH,b,hr,hU⟩
   have hz: p-plank n A∈hill inkAge (d+1-k):=by
     refine (MvPolynomial.mem_restrictSupport_iff ℝ).mpr ?_; intro s hs
     let w:=rankW inkAge s; by_contra! hx; have hg:w≤v:=by change ¬_≤rankW inkAge s at hx; dsimp [w,v]; omega
     have hh:=mem_support_iff.mp hs; rw [coeff_sub,plank,keeps_i,if_pos (hg.trans hv)] at hh
     change _-coeff _ (showP G n r)≠0 at hh
     rcases eq_or_lt_of_le hg with hz|ht
     · have hu:= congrArg (MvPolynomial.coeff s) H.2; unfold P at hu; rw [coeff_weightedHomogeneousComponent,if_pos hz,coeff_weightedHomogeneousComponent,if_pos hz] at hu; exact hh (sub_eq_zero.mpr hu.symm)
     rw [disappears hq ht, disappears H.1 ht] at hh; simp at hh
   exact (sub_add_cancel p (plank n A)) ▸ (Submodule.add_mem _ (ih _ (Submodule.sub_mem _ hp (skilled _)) hz) (Submodule.subset_span ⟨A,rfl⟩))
lemma width_finite {I:Type*}[Finite I](i:I→ℕ)(s:ℕ)(hs:∀a:I, (1:ℕ) ≤ i a) : Set.Finite {v:I→₀ℕ|rankW i v ≤s}:=by
 let L:= {v:I→₀ℕ| rankW i v≤s}
 have he (v:L)(a:I) : v.val a≤ s:=by
    have h:v.val a≤ v.val a*i a:= le_mul_of_one_le_right (Nat.zero_le _) (hs a)
    by_cases hx:v.val a=0
    · simp [hx]
    exact le_trans h (le_trans (show _≤rankW i v.val from Finset.single_le_sum (f:=fun j=>v.val j • i j) (fun _ _=>Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)) v.property)
 let U(v:L)(a:I):Fin (s+1):= ⟨v.val a,Nat.lt_succ_of_le (he v a)⟩
 exact Finite.of_injective U (fun v w h=>Subtype.ext (Finsupp.ext fun i=> congrArg Fin.val (congrFun h i))) -- check
instance tall: FiniteDimensional ℝ (Ladder (G:=G) n d):=by
 letI: Finite {v: Sky G n→₀ℕ| rankW inkAge v≤d}:= width_finite _ d (fun a=>Nat.le_add_left 1 _)
 exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℝ _)
instance: FiniteDimensional ℝ ↥(Eidolon (G:=G) n d):= FiniteDimensional.of_injective (Submodule.inclusion (show Eidolon (G:=G) n d≤Ladder n d from fun _ p=>p.1)) (Submodule.inclusion_injective _)
lemma platen (n d:ℕ)(F:Frames G):∃ m:ℕ,∃ I:Fin m→ Tab F d,∃ e:Eidolon n d→ₗ[ℝ] (Fin m→ℝ), ∀ p:Eidolon (G:=G) n d,p.val=∑l,e p l • plank n (I l):=by
 -- choose finite spanning family by basis decomposition via fill
 let L:= Eidolon (G:=G) n d
 let u(v:Tab F d):L:=⟨plank n v,skilled _⟩
 let S: (Tab F d→₀ℝ)→ₗ[ℝ] L:= Finsupp.linearCombination ℝ u
 have H:∀ w:L,w∈S.range:=by
    intro w; have ht:=fill (F:=F) w.val w.property
    rw [← Finsupp.range_linearCombination] at ht
    obtain ⟨l,p⟩:=ht; refine ⟨l,Subtype.ext ?_⟩
    have hz:(L.subtype) (Finsupp.linearCombination ℝ u l)=Finsupp.linearCombination ℝ (fun i=>plank n i) l:=LinearMap.map_finsupp_linearCombination .. -- check
    exact hz.trans p
 let m:=Module.finrank ℝ L
 let B:= Module.finBasis ℝ L
 choose t ht using (fun i:Fin m=>H (B i))
 let J:Finset (Tab F d):=Finset.univ.biUnion fun i:Fin m=> (t i).support
 let V :=J.equivFin
 refine ⟨J.card,fun i=>(V.symm i).val, LinearMap.pi (fun i=>∑ k:Fin m,t k (V.symm i).val • B.coord k), ?_⟩
 intro p; change p.val=∑l,(∑k:Fin m,t k (V.symm l).val • B.coord k) p • _
 have he (k:Fin m):(B k).val= ∑ i:Fin J.card,t k (V.symm i).val • plank n ((V.symm i).val):=by
    rw [← ht k]; unfold S; rw [Finsupp.linearCombination_apply,Finsupp.sum,AddSubmonoidClass.coe_finsetSum]
    rw [Finset.sum_subset (s₂:=J), ← Finset.sum_attach]
    · refine Fintype.sum_equiv V _ _ fun v=>?_ ; rw [V.symm_apply_apply];rfl
    · intro i hi; exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hi⟩ -- check order
    intro i h h'; have H:t k i=0:=not_ne_iff.mp fun b=>h' (Finsupp.mem_support_iff.mpr b); simp only [H,zero_smul];rfl
 conv_lhs=> rw [← B.sum_repr p]
 rw [AddSubmonoidClass.coe_finsetSum]; simp only [Submodule.coe_smul,he, Finset.smul_sum,LinearMap.sum_apply, LinearMap.smul_apply,Finset.sum_smul,smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; congr 1; exact mul_comm ..
end YM.SchemeRG11.Outlook
