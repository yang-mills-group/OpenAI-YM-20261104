import YM.XSpace.Spoken
/-!
# Directions can be completely filled with remote probes
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter Maxwell Maxwell.Free
open scoped BigOperators Topology Classical
variable {G : Gauge} (C₀:G.ColorIndex) {S L :Finset E4} {h : ℕ}
private abbrev towards := 𝓝[>] (0:ℝ)
private lemma closer_pos (x : E4) {v : E4} (hv : v≠0) : ∀ᶠ t:ℝ in towards,x-t • v∉L:=by
  suffices h : ∀ᶠ t:ℝ in towards,∀ z∈L,x-t • v≠z by exact h.mono fun t ht hh=> ht _ hh rfl
  refine (eventually_all_finset L).mpr (fun z _=>?_); by_cases h:x=z
  · subst z; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    intro h; have hh : t • v=0:= sub_eq_self.mp h; exact smul_ne_zero (show t≠0 from (show 0<t from ht).ne') hv hh
  have he : Continuous (fun t:ℝ=>x-t • v):=by fun_prop
  have hK := he.continuousAt (x:=0) |>.continuousWithinAt (s:=Ioi 0)
  exact hK.eventually (isOpen_compl_singleton.mem_nhds (show x-(0:ℝ) • v ∈ ({z}ᶜ:Set E4) by simp [h]))

private lemma scales (p : Flavor h) (q : Flavor 0) {v:E4} (hv:v≠0) (x:E4) (t:ℝ) (ht:0<t) :
    fare C₀ p q (x-(x-t • v)) = t⁻¹^(4+h)*fare C₀ p q v := by rw [sub_sub_self]; exact (kernel_pole (flavor h C₀ p) (flavor 0 C₀ q)).degree t ht v hv
private lemma converges (p : Flavor h) (q :Flavor 0) (x z u : E4) (hx:x≠z) (k : ℕ): Tendsto (fun t=> t^(4+k)*fare C₀ p q (z-(x-t • u))) towards (𝓝 0):=by
  let f (t:ℝ):=z-(x-t • u); have he : f 0=z-x:=by simp [f]
  let g:=fare C₀ p q
  have hf : ContinuousAt f 0:=by unfold f; fun_prop
  have hh : ContinuousAt g (f 0):=he.symm ▸ ((kernel_pole (flavor h C₀ p) (flavor 0 C₀ q)).diff _ (sub_ne_zero.mpr hx.symm)).continuousAt
  have hk:= (((continuousAt_id.pow (4+k)).mul (hh.comp hf)).continuousWithinAt (s:=Ioi 0)).tendsto
  simpa [show id ^ (4 + k) * (g ∘ f) = fun t => t ^ (4 + k) * fare C₀ p q (z - (x - t • u)) from funext fun t=> by simp [g,f]] using hk
private lemma scaled_price {v:E4} (hv:v≠0) (x : (S:Set E4)) (Z:Supply S h) (a b:Fin (h+1))
    (l:∀ j,a<j→ Z x j=0) (q:Flavor 0) : Tendsto (fun t=> t^(4+a.val)*fare C₀ (Z x b) q (x.val-(x.val-t • v))) towards
        (𝓝 (if b=a then fare C₀ (Z x a) q v else 0)):=by
  rcases lt_trichotomy a b with hp|hp|hp
  · rw [if_neg (ne_of_gt hp)]; apply tendsto_const_nhds.congr'; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    rw [scales _ _ _ hv _ _ ht,l b hp, show fare C₀ (0:Flavor b) q v=0 from map_zero ((assay C₀ hv b 0).flip q),mul_zero,mul_zero]
  · subst b; rw [if_pos rfl]; apply tendsto_const_nhds.congr'; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    have hk := (show 0<t from ht).ne'; rw [scales _ _ _ hv _ _ ht,inv_pow,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hk),one_mul]
  rw [if_neg (ne_of_lt hp)]
  let j:= a.val-b.val
  have hj : 0<j:=by unfold j; omega
  have he : Tendsto (fun t :ℝ=> t^j*fare C₀ (Z x b) q v) towards (𝓝 0):=by
    simpa [zero_pow hj.ne', id_eq] using (((((continuousAt_id (x:=(0:ℝ))).pow j).mul_const (fare C₀ (Z x b) q v)).tendsto).mono_left  (nhdsWithin_le_nhds (a:=(0:ℝ)) (s:=Ioi 0)))
  apply he.congr'; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
  have hk:= (show 0<t from ht).ne'; rw [scales _ _ _ hv _ _ ht,inv_pow,show 4+a.val=j+(4+b.val) by unfold j; omega,pow_add, ← mul_assoc,mul_assoc (t^j) (t^(4+b.val)),mul_inv_cancel₀ (pow_ne_zero _ hk),mul_one]

lemma range_ind (S L:Finset E4) (h:ℕ) (Z : Supply S h) (hS : S⊆L) (ht : ∀ v:Ph,v.1∉ L → voice S h C₀ v Z=0): Z=0:=by
  have he (x : (S:Set E4)) (a : Fin (h+1)) (l:∀ j,a<j→ Z x j=0): Z x a=0:=by
    apply ranging C₀ (Z x a) 0; intro v hv q
    let g (z : (S:Set E4)) (b : Fin (h+1)) := fun t:ℝ=> t^(4+a.val) * fare C₀ (Z z b) q (z.val - (x.val - t • v))
    have hs : Tendsto (fun t=>∑ z:(S:Set E4), ∑ b : Fin (h+1), g z b t) towards (𝓝 (∑ z:(S:Set E4), if z=x then ∑ b : Fin (h+1), if b=a then fare C₀ (Z x a) q v else 0 else 0)) := by
      refine tendsto_finsetSum _ (fun z _=>?_); split_ifs with hx; subst z; exact tendsto_finsetSum _ fun i _=> scaled_price _ hv x Z a i l q
      rw [← show (∑ b:Fin (h+1),(0:ℝ))=0 from Finset.sum_const_zero]; refine tendsto_finsetSum _ fun i _=> converges _ _ _ x.val z.val v (fun e=> hx (Subtype.ext e.symm)) a.val
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
    refine tendsto_nhds_unique_of_eventuallyEq hs tendsto_const_nhds ?_
    filter_upwards [closer_pos (L:=L) x.val hv] with t h
    unfold g; simp_rw [← Finset.mul_sum];
    rw [← chorus C₀ _ (v:=(x.val-t • v,q)) (fun e=> h (hS e)) Z, ht _ h,mul_zero]
  funext x j; change Z x j=0
  induction j using WellFounded.induction (measure (fun j:Fin (h+1)=> h-j.val)).wf with
  | h j ih=> exact he _ _ fun i hi=> ih i (show h-i.val<h-j.val by omega)
instance supplyF (S : Finset E4) (h:ℕ): FiniteDimensional ℝ (Supply S h):=by
  letI : ∀ (i:Fin (h+1)), FiniteDimensional ℝ (Flavor i) := fun i=> inferInstance
  letI : FiniteDimensional ℝ ((i:Fin (h+1))→ Flavor i) := by infer_instance
  unfold Supply; infer_instance
lemma ranged (S L:Finset E4) (h:ℕ) (hs:S⊆L): Submodule.span ℝ {p | ∃ v:Ph,v.1∉L ∧ voice S h C₀ v=p} = ⊤:=by
  let V:=Submodule.span ℝ {p | ∃ v:Ph,v.1∉L ∧ voice S h C₀ v=p}
  change V=⊤
  have hp : V.dualCoannihilator=⊥:=by
    apply le_antisymm _ bot_le; intro x hx; apply (Submodule.mem_bot ..).mpr; exact range_ind C₀ S L h x hs (fun p he=> (Submodule.mem_dualCoannihilator _).1 hx _ (Submodule.subset_span (show _ from ⟨p,he,rfl⟩)))
  letI := supplyF S h
  apply Submodule.eq_top_of_finrank_eq; have he := Subspace.finrank_add_finrank_dualCoannihilator_eq V; rw [hp,finrank_bot,add_zero] at he; rw [he]; exact (Subspace.dual_finrank_eq ..).symm
end YM.XSpace.Legs
