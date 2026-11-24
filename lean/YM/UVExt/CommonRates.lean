import YM.UVExt.MainCauchy

/-! Anchored or free ray-jet comparisons, fixed period. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Laurent Lattice RG Wilson Precision Matrix
open scoped Topology ContDiff BigOperators Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option linter.unusedVariables false
variable {q : ℕ}
def Both {ι : Type*} [TopologicalSpace ι] (X X' : ℕ→ι) : Prop := ∃ L, Tendsto X atTop (𝓝 L) ∧ Tendsto X' atTop (𝓝 L)
def Joint (q : ℕ) (f g : ℕ→ℝ→E) := lucid f ∧ lucid g ∧ ∀ j≤q, Both (fun i=>fish j (f i)) (fun i=> fish j (g i))

lemma lucid_mul {f g : ℕ→ℝ→ℝ} (h : lucid f) (hf : lucid g) : lucid (f*g) := (h.and hf).mono fun i ⟨hr,h⟩=> hr.mul h
lemma joint_refl (u : ℝ→E) (h : ContDiffAt ℝ ∞ u 0) : Joint q (fun _=>u) (fun _=>u) := ⟨Eventually.of_forall (fun _=>h), Eventually.of_forall (fun _=>h),fun j _=>⟨_,tendsto_const_nhds,tendsto_const_nhds⟩ ⟩
lemma Joint.flip {f g : ℕ→ℝ→E} (h : Joint q f g) : Joint q g f := ⟨h.2.1,h.1,fun j hj=>(h.2.2 _ hj).elim fun _ ⟨hp,ht⟩=>⟨_,ht,hp⟩⟩
lemma Joint.agrees {f g f' g' : ℕ→ℝ→E} (h : Joint q f g) (h₁ : ∀ᶠ i in atTop,f i =ᶠ[𝓝 (0:ℝ)] f' i) (h₂ : ∀ᶠ i in atTop,g i =ᶠ[𝓝 (0:ℝ)]g' i) : Joint q f' g' := by
  refine ⟨(h.1.and h₁).mono (fun i ⟨hp,hr⟩=>hp.congr_of_eventuallyEq hr.symm),(h.2.1.and h₂).mono (fun i ⟨hp,hr⟩=>hp.congr_of_eventuallyEq hr.symm),?_⟩
  intro j hj; obtain ⟨L,H,H'⟩:=h.2.2 j hj
  exact ⟨L,H.congr' (h₁.mono fun i hr=>(hr.iteratedDeriv _).eq_of_nhds),H'.congr' (h₂.mono fun i hr=>(hr.iteratedDeriv _).eq_of_nhds)⟩
lemma Joint.add {f g u v : ℕ→ℝ→E} (h : Joint q f g) (ht : Joint q u v) : Joint q (f+u) (g+v) := by
   refine ⟨(h.1.and ht.1).mono (fun i ⟨h,hr⟩=>h.add hr), (h.2.1.and ht.2.1).mono (fun i ⟨h,hr⟩=>h.add hr),?_⟩
   intro j hj; obtain ⟨L,H,H'⟩:= h.2.2 j hj; obtain ⟨P,T,T'⟩:=ht.2.2 j hj
   exact ⟨L+P,(H.add T).congr' ((h.1.and ht.1).mono (fun i ⟨h₁,h₂⟩=>(iteratedDeriv_add (h₁.of_le (finite_cap _)) (h₂.of_le (finite_cap _))).symm)),(H'.add T').congr' ((h.2.1.and ht.2.1).mono (fun i ⟨h₁,h₂⟩=>(iteratedDeriv_add (h₁.of_le (finite_cap _)) (h₂.of_le (finite_cap _))).symm)) ⟩ -- expect finite_cap implicit issues
lemma Joint.mul {f f' g g' : ℕ→ℝ→ℝ} (h : Joint q f f') (hg : Joint q g g') : Joint q (f*g) (f'*g') := by
   obtain ⟨ha,hb,hR⟩:=h; obtain ⟨hc,hd,hQ⟩:=hg
   choose Y hT hT' using fun i:Fin (q+1)=>hR i.val (by omega)
   choose Z hV hV' using fun i:Fin (q+1)=>hQ i.val (by omega)
   let t (g : Fin (q+1)→ℝ) (i : ℕ) := if h:i≤q then g ⟨i,by omega⟩ else 0
   refine ⟨lucid_mul ha hc, lucid_mul hb hd, ?_⟩; intro k hk
   let A (i d) := (Nat.choose k d:ℝ)*fish d (f i)*fish (k-d) (g i)
   let A' (i d) := (Nat.choose k d:ℝ)*fish d (f' i)*fish (k-d) (g' i)
   let z d := (Nat.choose k d:ℝ)* (t Y d) * t Z (k-d)
   have he (d : ℕ) (h : d≤k) : Tendsto (fun i=>A i d) atTop (𝓝 (z d)) ∧ Tendsto (fun i=>A' i d) atTop (𝓝 (z d)) := by
     let ℓ : Fin (q+1) := ⟨d,by omega⟩; let ℓ' : Fin (q+1) := ⟨k-d,by omega⟩
     unfold z t; rw [dif_pos (by omega), dif_pos (by omega)]
     exact ⟨(Tendsto.const_mul (Nat.choose k d:ℝ) (hT ℓ)).mul (hV ℓ'), (Tendsto.const_mul (Nat.choose k d:ℝ) (hT' ℓ)).mul (hV' ℓ')⟩
   refine ⟨∑ d∈Finset.range (k+1), z d,?_ ,?_ ⟩
   · refine (tendsto_finsetSum _ fun d (hd : d∈Finset.range (k+1))=>(he d (Nat.lt_add_one_iff.mp (Finset.mem_range.mp hd))).1).congr' ?_
     exact ((ha.and hc).mono fun i ⟨h,h'⟩=> (iteratedDeriv_mul (h.of_le (finite_cap _)) (h'.of_le (finite_cap _)) : tag k (f i*g i)=∑ d∈_, A i _).symm)
   refine (tendsto_finsetSum _ fun d (hd : d∈Finset.range (k+1))=>(he d (Nat.lt_add_one_iff.mp (Finset.mem_range.mp hd))).2).congr' ?_
   exact ((hb.and hd).mono fun i ⟨h,h'⟩=> (iteratedDeriv_mul (h.of_le (finite_cap _)) (h'.of_le (finite_cap _)) : tag k (f' i*g' i)=∑ d∈_, A' i _).symm)

lemma Joint.sum {ι : Type*} (s : Finset ι) (f f' : ι→ℕ→ℝ→ℝ) (h : ∀ i∈s, Joint q (f i) (f' i)) : Joint q (∑ i∈s,f i) (∑ i∈s,f' i) := by
    classical
    induction s using Finset.cons_induction_on with
    | empty => simp only [Finset.sum_empty]; exact joint_refl _ contDiffAt_const
    | cons i s hi ih => rw [Finset.sum_cons,Finset.sum_cons]; apply (h i (Finset.mem_cons_self _ _)).add (ih fun b g=>h b (Finset.mem_cons_of_mem g))

lemma Joint.prod {ι : Type*} (s : Finset ι) (f f' : ι→ℕ→ℝ→ℝ) (h : ∀ i∈s, Joint q (f i) (f' i)) : Joint q (∏ i∈s,f i) (∏ i∈s,f' i) := by
    classical
    induction s using Finset.cons_induction_on with
    | empty => simp only [Finset.prod_empty]; exact joint_refl _ contDiffAt_const
    | cons i s hi ih => rw [Finset.prod_cons,Finset.prod_cons]; apply (h i (Finset.mem_cons_self _ _)).mul (ih fun b g=>h b (Finset.mem_cons_of_mem g))

lemma joint_mono {j} (h : j≤q) {f f' : ℕ→ℝ→E} (hr : Joint q f f') : Joint j f f' := ⟨hr.1,hr.2.1,fun i hi=>hr.2.2 _ (hi.trans h)⟩
lemma Joint.at_zero {f f' : ℕ→ℝ→E} (h : Joint q f f') : Both (f · 0) (f' · 0) := by
 obtain ⟨L,H,H'⟩ := h.2.2 0 (Nat.zero_le _)
 refine ⟨L,H,H'⟩

section finite
variable [CompleteSpace E] [FiniteDimensional ℝ E] {f g : ℕ→ℝ→E}
/-- Does not rely on the inner path being pinned. Outer function fixed on both sides and analytic at the common basepoint (not just merely `C^∞` by an `∞` reading in `ContDiffAt`). -/
lemma Both_comp (N : E→F) (q) (h : Joint q f g) {a} (hA : Tendsto (f · 0) atTop (𝓝 a)) (hB : Tendsto (g · 0) atTop (𝓝 a)) (ht : ContDiffAt ℝ ω N a) :
    Joint q (fun i=>N ∘ f i) (fun i=>N ∘ g i) := by

   have hi := hA.eventually (ht.eventually (by simp: (ω:ℕ∞ω)≠∞))
   have hi' := hB.eventually (ht.eventually (by simp: (ω:ℕ∞ω)≠∞))
   have hComp {y : ℕ→ℝ→E} (hS : ∀ᶠ i in atTop, ContDiffAt ℝ ω N (y i 0)) (hL : lucid y) : lucid (fun i=>N ∘ y i) := (hS.and hL).mono fun i hx=> (hx.1.of_le le_top).comp 0 hx.2
   refine ⟨hComp hi h.1,hComp hi' h.2.1,?_⟩; intro k hk
   choose Y hY hY' using (fun i:Fin (q+1)=>h.2.2 i.val (by omega))
   let Z l := if z:l≤q then Y ⟨l,by omega⟩ else 0
   have hY'' l (hl : l≤q) : Tendsto (fun i=>fish l (f i)) atTop (𝓝 (Z l)) ∧ Tendsto (fun i=>fish l (g i)) atTop (𝓝 (Z l)) := by unfold Z; rw [dif_pos hl]; exact ⟨hY _,hY' _⟩
   let val (v : ℕ→ℝ→E) (t : OrderedFinpartition k) i := iteratedFDeriv ℝ t.length N (v i 0) (partitionVal v t i)
   let U t := ∑ c: OrderedFinpartition k,val t c
   let L (c : OrderedFinpartition k) := iteratedFDeriv ℝ c.length N a (fun j=> Z (c.partSize j))
   have hn (c:OrderedFinpartition k) : Tendsto (val f c) atTop (𝓝 (L c)) ∧ Tendsto (val g c) atTop (𝓝 (L c)) := by
     have he := (ht.continuousAt_iteratedFDeriv (k:=c.length) (by simp)).tendsto
     have hp (i) := hY'' (c.partSize i) ((c.partSize_le i).trans (show k≤q from hk))
     have hQ : Continuous (uncurry (⇑) : (Tensor.T E F c.length × (Fin c.length→E)) → F) := view_cont
     exact ⟨hQ.continuousAt.tendsto.comp ((he.comp hA).prodMk_nhds (tendsto_pi_nhds.mpr (fun i=>(hp i).1))),hQ.continuousAt.tendsto.comp ((he.comp hB).prodMk_nhds (tendsto_pi_nhds.mpr (fun i=>(hp i).2)))⟩
   have hX {t : ℕ→ℝ→E} (hf : ∀ᶠ i in atTop,ContDiffAt ℝ ω N (t i 0)) (hL : lucid t) : (fun i=> fish k (N ∘ t i))=ᶠ[atTop] U t := (hf.and hL).mono fun i hx=> by
     have hz := iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hx.1.of_le (m:=(k:ℕ∞)) le_top) (hx.2.of_le (finite_cap _)) (n:=(k:ℕ∞ω)) le_rfl -- fix
     unfold U; simp only [Finset.sum_apply]; exact hz
   exact ⟨∑ c,L c, (tendsto_finsetSum _ (fun (i : OrderedFinpartition k) (_hi : i∈Finset.univ)=>(hn i).1) : Tendsto (fun d=>∑ i,val f i d) atTop (𝓝 (∑ i,L i))).congr' (by exact (hX hi h.1).mono fun i hi => by simpa only [U,Finset.sum_apply] using hi.symm),
                   (tendsto_finsetSum _ (fun (i : OrderedFinpartition k) (_hi : i∈Finset.univ)=>(hn i).2) : Tendsto (fun d=>∑ i,val g i d) atTop (𝓝 (∑ i,L i))).congr' (by exact (hX hi' h.2.1).mono fun i hi => by simpa only [U,Finset.sum_apply] using hi.symm)⟩
end finite
end YM.UVExt.Paths
