import YM.MSbar.CrossH.Cubes
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι:Type}[Fintype σ][DecidableEq σ][Fintype ι][DecidableEq ι]{c n: Side}
open Polynomial MvPolynomial Matrix Rolling
variable (l:σ→Site n)(L:ι→ Site n)(g:Ratio c n) {a b K:ℕ}
noncomputable def cities (K v:ℕ):=(v+v+1)^4*K
lemma dressP (h:Multiplicity l K)(j:Site n)(p:ℕ): (curbL l j p).card ≤ cities K p:=by
    let s:=curbL l j p; let W:=halo p {j}; have he:∀ i∈s,l i∈W:=by intro i hi; refine halo_spec.mpr ⟨j,Finset.mem_singleton_self j,?_⟩; rw [separation_comm]; exact Finset.mem_filter.mp hi|>.2
    have hx: (∑ i∈s,(1:ℕ))≤∑ j∈W,K:=by
         rw [← Finset.sum_fiberwise_of_maps_to he]; apply Finset.sum_le_sum; intro i _; simp only [Finset.sum_const, nsmul_eq_mul,mul_one]; refine (Finset.card_le_card ?_).trans (h i); exact Finset.filter_subset_filter _ (Finset.subset_univ s)
    rw [Finset.sum_const,Finset.sum_const,nsmul_eq_mul,mul_one,nsmul_eq_mul] at hx; exact hx.trans (Nat.mul_le_mul_right _ (by simpa using Corona.halo_size ({j}: Support n) p))
lemma embryo (h:Multiplicity l a)(hh:Multiplicity L b): Multiplicity (Sum.elim l L) (a+b):=by
    intro i; apply le_trans _ (Nat.add_le_add (h i) (hh i)); have he:(Finset.univ.filter fun t:σ ⊕ ι=>Sum.elim l L t=i)=(Finset.univ.filter fun t:σ=>l t=i).disjSum (Finset.univ.filter fun t:ι=>L t=i):=by ext x; cases x <;> simp
    rw [he,Finset.card_disjSum]
lemma flagC (t:σ→Site c)(h:Multiplicity t a): Multiplicity (g.embed ∘ t) a:=by
    intro i; apply le_trans _ (h (g.parent i)); apply Finset.card_le_card; intro v hv; simp only [Finset.mem_filter,Function.comp_apply,Finset.mem_univ,true_and] at *; rw [←hv,g.embed_parent]
lemma folk (x:ι→σ)(h:Surjective x)(hf:Injective x)(e:Multiplicity (l∘ x) K): Multiplicity l K:=by
   let p:ι≃σ:= Equiv.ofBijective x ⟨hf,h⟩; exact (show (l∘ x) ∘ p.symm = l from funext fun x=> congr_arg l (p.apply_symm_apply x)) ▸ e.comp p.symm.injective
lemma powerP (p: Side)(A: Type)[Fintype A]: Multiplicity (Prod.fst : Site p × A→ Site p) (Fintype.card A):=by
    intro i; apply (Finset.card_le_card_of_injOn (s:=Finset.univ.filter fun j: Site p × A=> j.1=i) (t:=Finset.univ) Prod.snd (fun _ _=>Finset.mem_univ _) _).trans_eq (Finset.card_univ ..)
    rintro ⟨x,j⟩ hx ⟨y,v⟩ hv he; exact Prod.ext ((Finset.mem_filter.mp hx|>.2).trans (Finset.mem_filter.mp hv|>.2).symm) he
open Gauge
lemma starM (G:Gauge)(n:Side): Multiplicity (Measuring.chart n G) (Fintype.card (Strand G)):=by
    let e: Site n × Strand G≃ Primary n G:=(Equiv.prodAssoc ..).symm; exact folk _ e e.surjective e.injective (powerP n (Strand G))
lemma syrupDown {z:Matrix σ ι ℝ}{a b v t:ℝ}(h:Syrup l L a K z b)(he:t≤a)(hb:b≤v): Syrup l L t K z v:=by
    have hp(i j) : skim l L t K i j≤ skim l L a K i j:=by unfold skim Measuring.factor; gcongr
    exact ⟨h.cash.trans hb,fun i=> (Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (hp i j) (abs_nonneg _)).trans ((h.leftP i).trans hb),fun j=> (Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (hp i j) (abs_nonneg _)).trans ((h.rightP j).trans hb)⟩
end YM.MSbar.CrossH
