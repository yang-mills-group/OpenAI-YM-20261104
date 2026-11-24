import YM.UVExt.TensorFlux

/-! Jet rendezvous at moving but anchored maps, not yet optimizing or gauging anything. All Taylor operations at zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Set Tensor OrderedFinpartition Real
open scoped Topology ContDiff BigOperators Classical
variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section single
variable {p : ℕ→ℝ→E} {P : ℕ→F→E}
abbrev Pinned (p : ℕ→F→E) := ∀ᶠ i : ℕ in atTop, p i 0=0

lemma lucid_pin (a : F) (h : lucid P) : lucid (fun i => fun x : ℝ => P i (x • a)) := by
  apply h.mono; intro k hk; exact ContDiffAt.comp (f:=fun z : ℝ=> z • a) 0 (show ContDiffAt ℝ ∞ _ _ by rw [zero_smul]; exact hk) (contDiffAt_id.smul contDiffAt_const)
lemma lucid_comp {f : ℕ→E→Y} (ha : lucid f) (hb : lucid P) (h : Pinned P) : lucid (fun i=> f i ∘ P i) := by
  filter_upwards [ha,hb,h] with k hk hl u; exact ContDiffAt.comp (f:=P k) 0 (u ▸ hk) hl

lemma faa_eq {q} (c : OrderedFinpartition q) (h : c.length ≥ q) (i) : c.partSize i=1 := by
  have hx := c.sum_sigma_eq_sum (fun _=> (1:ℕ))
  simp at hx
  have he := Finset.sum_erase_add _ (c.partSize) (Finset.mem_univ i)
  have hg : ∑ j∈ Finset.univ.erase i,1 ≤ _ := Finset.sum_le_sum fun j _=> c.partSize_pos j
  simp at hg
  have hi := c.partSize_pos i; omega

private lemma strict_self {k} (f : Fin k→Fin k) (h : StrictMono f) : f=id := by
  have hv (i : Fin k) (m:ℕ) : m ≤ i.val → m ≤ (f i).val := by
    induction m generalizing i with
    | zero => exact fun _=>Nat.zero_le _
    | succ m hm =>
       intro e; let x : Fin k := ⟨m,by omega⟩; have ht : (f x).val < (f i).val := h (show x < i by change m < i.val; omega)
       exact (hm x le_rfl).trans_lt ht
  funext i; apply Fin.ext; refine Nat.le_antisymm ?_ (hv i i.val le_rfl); on_goal 1 => by_contra! ht
  let e := Equiv.ofBijective f ⟨h.injective,h.injective.surjective_of_fintype (.refl _)⟩
  have g₁ : (∑ x : Fin k,(f x).val) = _ := Equiv.sum_comp e Fin.val
  have g₂ : (∑ (x:Fin k), x.val)<_ := Finset.sum_lt_sum (fun x _=> hv x _ le_rfl) ⟨i,Finset.mem_univ _,ht⟩
  exact False.elim (lt_irrefl _ (g₂.trans_eq g₁)) -- replace
set_option maxRecDepth 3000 in
lemma partition_top {k} (p : OrderedFinpartition k) (hp : p.length=k) : p = atomic k := by
  rcases p with ⟨n,s,h,emb,he,hs,hx,hD⟩; dsimp only at *; subst n
  let c: OrderedFinpartition k := ⟨k,s,h,emb,he,hs,hx,hD⟩
  obtain rfl : s=fun _=>1 := funext fun i=> faa_eq c (by rfl) i
  have hg : StrictMono (fun i=>emb i 0) := hs
  refine OrderedFinpartition.ext (x:=c) (y:=atomic k) (by rfl) (heq_of_eq (show c.partSize=(atomic k).partSize from rfl)) ?_
  refine heq_of_eq (funext fun i=>funext fun j=>?_); exact (congrArg (emb i) (show j=0 from by exact Subsingleton.elim ..)).trans (congr_fun (strict_self _ hg) i)

def partitionVal {q : ℕ} (P : ℕ→ℝ→E) (c : OrderedFinpartition q) i := fun j => fish (c.partSize j) (P i)

end single
variable {p p' : ℕ→ℝ→E} {b d : ℕ→F→E} 
set_option linter.unusedSectionVars false
section tee
variable {k : ℕ} [FiniteDimensional ℝ F] [CompleteSpace F] [FiniteDimensional ℝ Y] [CompleteSpace Y] {f g p q : ℕ→F→Y}
lemma Junction.congruent (h : Junction f p k) (he : ∀ᶠ i : ℕ in atTop, f i =ᶠ[𝓝 0] g i) (ht : ∀ᶠ i : ℕ in atTop, p i =ᶠ[𝓝 0] q i) : Junction g q k := by
  intro m hm; obtain ⟨z,hz,hw⟩ := h m hm; exact ⟨z,hz.congr' (he.mono fun i hi=>(hi.iteratedFDeriv ℝ m).eq_of_nhds),hw.congr' (ht.mono fun i hi=>(hi.iteratedFDeriv ℝ m).eq_of_nhds)⟩
lemma Junction.reversed (h : Junction f p k) : Junction p f k := by
  intro m hm; obtain ⟨z,hz,hw⟩ := h m hm; exact ⟨z,hw,hz⟩
lemma Junction.transitive {p' : ℕ→F→Y} (h : Junction f p k) (h' : Junction p p' k) : Junction f p' k := by
  intro m hm; obtain ⟨z,hz,hw⟩ := h m hm; obtain ⟨v,hv,hv'⟩ := h' m hm
  exact ⟨z,hz,(tendsto_nhds_unique hw hv) ▸ hv'⟩
lemma Junction.plus (h : Junction f p k) (h' : Junction g q k) (hf : lucid f) (hp : lucid p) (hg : lucid g) (hq : lucid q) :
    Junction (fun i=>f i+g i) (fun i=>p i+q i) k := by
  intro m hm; obtain ⟨z,hz,hw⟩ := h m hm; obtain ⟨v,hv,hv'⟩ := h' m hm
  exact ⟨z+v,(hz.add hv).congr' ((hf.and hg).mono fun i hi=>(iteratedFDeriv_add_apply (hi.1.of_le (finite_cap _)) (hi.2.of_le (finite_cap _))).symm),
     (hw.add hv').congr' ((hp.and hq).mono fun i hi=>(iteratedFDeriv_add_apply (hi.1.of_le (finite_cap _)) (hi.2.of_le (finite_cap _))).symm)⟩
lemma Junction.times (h : Junction f p k) (hf : lucid f) (hp : lucid p) {c d : ℕ→ℝ} {z : ℝ} (h₁ : Tendsto c atTop (𝓝 z)) (h₂ : Tendsto d atTop (𝓝 z)) :
    Junction (fun i=> c i • f i) (fun i=> d i • p i) k := by
  intro m hm; obtain ⟨Y,hz,hw⟩ := h m hm
  exact ⟨z • Y,(h₁.smul hz).congr' (hf.mono fun i hi=>(iteratedFDeriv_const_smul_apply (hi.of_le (finite_cap _))).symm),
    (h₂.smul hw).congr' (hp.mono fun i hi=>(iteratedFDeriv_const_smul_apply (hi.of_le (finite_cap _))).symm)⟩
end tee

/-- isolate the top outer jet term against a line family whose jets through k (used only below when needed) converge. -/
lemma faa_lead {f g : ℕ→E→F} {k : ℕ} (ha : lucid f) (hb : lucid g) (hp : lucid p) (hq : lucid p') (hpa : Pinned p) (hpb : Pinned p') (h : Junction f g (k-1)) (he : 1≤k)
    (Y : ℕ→E) (hk : ∃ U, Tendsto (fun i=> spray f k i) atTop (𝓝 U)) (hk' : ∃ U, Tendsto (fun i=>spray g k i) atTop (𝓝 U))
    (ht : ∀ m≤k, (Tendsto (fun i=>fish m (p i)) atTop (𝓝 (Y m))) ∧ Tendsto (fun i=>fish m (p' i)) atTop (𝓝 (Y m))) {d}
    (hD : Tendsto (fun i=> Tensor.diagonal (spray f k i) (Y 1) - Tensor.diagonal (spray g k i) (Y 1)) atTop (𝓝 d)) :
    Tendsto (fun i=> fish k (f i ∘ p i) - fish k (g i ∘ p' i)) atTop (𝓝 d) := by
  let val (h : ℕ→E→F) (t : ℕ→ℝ→E) (i : ℕ) (c : OrderedFinpartition k) := spray h c.length i (partitionVal t c i)
  have hEq {h : ℕ→E→F} {t : ℕ→ℝ→E} (h₁ : lucid h) (h₂ : lucid t) (hT : Pinned t) : ∀ᶠ i : ℕ in atTop,
     fish k (h i ∘ t i)=∑ c : OrderedFinpartition k, val h t i c := by
    filter_upwards [h₁,h₂,hT] with i hf hr ht
    unfold fish; rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (n:=k) _ (hr.of_le (finite_cap _)) le_rfl]
    · simp only [ht]; rfl
    rw [ht]; exact hf.of_le (finite_cap _)
  classical
  let credit (c : OrderedFinpartition k) := if c.length=k then d else 0
  have hY {q} (c : OrderedFinpartition q) (hq : q≤k) : Tendsto (fun i : ℕ=> partitionVal p c i) atTop (𝓝 fun j=>Y (c.partSize j)) := tendsto_pi_nhds.mpr fun i => (ht _ ((c.partSize_le i).trans hq)).1
  have hY' {q} (c : OrderedFinpartition q) (hq : q≤k) : Tendsto (fun i : ℕ=> partitionVal p' c i) atTop (𝓝 fun j=>Y (c.partSize j)) := tendsto_pi_nhds.mpr fun i => (ht _ ((c.partSize_le i).trans hq)).2
  /-have hTop {q} (c : OrderedFinpartition q) (hc : c.length=k) : (fun j=>Y (c.partSize j))=fun j=> Y 1 := funext fun i=> by rw [faa_eq (q:=q) c (by simpa [hc,q]) i] -/
  obtain ⟨U,hF⟩ := hk
  obtain ⟨V,hG⟩ := hk'
  have hΔ := tendsto_nhds_unique hD ((view_cont.continuousAt.tendsto.comp (hF.prodMk_nhds (tendsto_const_nhds (x:=fun _=>Y 1)))).sub (view_cont.continuousAt.tendsto.comp (hG.prodMk_nhds (tendsto_const_nhds (x:=fun _=>Y 1)))))
  have hV (c : OrderedFinpartition k) : Tendsto (fun i:ℕ=> val f p i c-val g p' i c) atTop (𝓝 (credit c)) := by
    by_cases hc : c.length=k
    · have hq (t : ℕ→ℝ→E) : partitionVal t c = fun i=>fun _=> fish 1 (t i) := funext fun i=>funext fun j=> by simp [partitionVal,faa_eq c hc.ge j]
      unfold val credit; rw [hq p,hq p', hc, if_pos rfl, hΔ]
      exact (view_cont.continuousAt.tendsto.comp (hF.prodMk_nhds (tendsto_pi_nhds.mpr (fun _=>(ht 1 he).1)))).sub (view_cont.continuousAt.tendsto.comp (hG.prodMk_nhds (tendsto_pi_nhds.mpr (fun _=>(ht 1 he).2))))
    have hh : c.length ≤ k-1 := by have ht := c.length_le; omega
    obtain ⟨W,hW,hZ⟩ := h _ hh
    simpa only [val,Function.comp_apply,sub_self,credit,if_neg hc] using ((view_cont.continuousAt.tendsto.comp (hW.prodMk_nhds (hY c le_rfl))).sub (view_cont.continuousAt.tendsto.comp (hZ.prodMk_nhds (hY' c le_rfl))))
  let cnt := (Finset.univ.filter fun c: OrderedFinpartition k=> c.length=k).card
  -- actually exactly one? There may be only atomic (length max), need show equality. Need cnt=1. Instead obtain all terms zero except atomic via uniqueness tool.
  apply Tendsto.congr' ?_ (show Tendsto (fun i=>∑ c : OrderedFinpartition k, (val f p i c-val g p' i c)) atTop (𝓝 d) from ?_)
  · filter_upwards [hEq ha hp hpa, hEq hb hq hpb] with i hi hk; change _=_; simp only [hi,hk,Finset.sum_sub_distrib]
  rw [show d=∑ c, credit c from ?_]
  · exact tendsto_finsetSum _ fun i _=>hV i
  rw [Finset.sum_eq_single (atomic k) (fun i _ h=>by
     unfold credit; rw [if_neg (fun he=>h (partition_top _ he))]) (by simp)]
  exact (if_pos (atomic_length k)).symm
end YM.UVExt.Paths
