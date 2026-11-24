import YM.UVExt.JoinPaths

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Set Real OrderedFinpartition Tensor
open Matrix
open scoped Topology ContDiff BigOperators Classical
variable {F B E Y : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section faa
 -- partition terms with too many curve derivatives die by stationary directional identities, before taking any limits.
variable {k : ℕ} (H : OrderedFinpartition k) {b : ℕ→F×B} {p : F×B→E}
lemma faa_double (hq : k=3 ∨ k=4) (i : Fin H.length) (hi : k-2 < H.partSize i) : H.length=1 ∨ H.length=2 := by
  have h := H.sum_sigma_eq_sum (fun _=> (1:ℕ)); simp at h
  have he := Finset.sum_erase_add _ (H.partSize) (Finset.mem_univ i)
  have hg : ∑ j∈ Finset.univ.erase i,1 ≤ _ := Finset.sum_le_sum fun j _=> H.partSize_pos j
  simp at hg
  exact (show 1≤H.length by have h:=Fin.pos i; omega).eq_or_lt |>.elim (fun t=> Or.inl t.symm) (fun h'=> Or.inr (by omega)) -- orientation eq?

lemma silent_block (hq : k=3 ∨ k=4) (hB : ∀ n≥2, (b n).1=0) {i : Fin H.length} (hi : k-2 < H.partSize i)
   (h : ContDiffAt ℝ k p 0) (hg : ∀ z : B, fderiv ℝ p 0 (0,z) = 0) (hp : ∀ z : B, iteratedFDeriv ℝ 2 p 0 ![b 1,(0,z)] = 0) :
   iteratedFDeriv ℝ H.length p 0 (b ∘ H.partSize)=0 := by
  rcases faa_double H hq i hi with hn|hn
  · cases H with | mk l a aph eb ea epr dp co =>
      dsimp only [OrderedFinpartition.length, partSize] at *; subst l
      have h₂ := hB (a i) (by omega)
      rw [iteratedFDeriv_one_apply, Function.comp_apply, ←Subsingleton.elim i 0,←Prod.eta (b (a i)),h₂,hg]
  have h' := h.of_le (m:=2) (by exact_mod_cast (show 2 ≤ k by omega))
  have hx := H.sum_sigma_eq_sum (fun _=> (1:ℕ)); simp at hx
  cases H with | mk l a aph eb ea epr dp co =>
      dsimp only [OrderedFinpartition.length, partSize] at *; subst l
      have hpA (j) : b (a j) = ((b (a j)).1,(b (a j)).2) := (Prod.eta _).symm
      rw [show b ∘ a =![b (a 0),b (a 1)] by ext1 i; fin_cases i <;> rfl] -- last rewrite only hx
      rw [Fin.sum_univ_two] at hx
      fin_cases i
      · change k-2 < a 0 at hi
        have hb₁ := hB (a 0) (by omega); have hb₂ : a 1=1 := by have := aph 1; omega
        rw [hb₂,←Prod.eta (b _),hb₁]
        refine Eq.trans ?_ (hp ((b (a 0)).2))
        have hh := Analysis.sym_Jet (h' : ContDiffAt ℝ (2:ℕ) p 0) (![b 1,(0,(b (a 0)).2)] : Fin 2→F×B) (Equiv.swap 0 1)
        refine Eq.symm <| (Eq.symm hh).trans (congr_arg _ ?_) -- expects reversed? inspect
        exact funext fun i=>by fin_cases i <;> simp
      change k-2 < a 1 at hi
      have hb₂ := hB (a 1) (by omega); have hb₁ : a 0=1 := by have := aph 0; omega
      rw [hb₁, ←Prod.eta (b (a 1)), hb₂,hp]
end faa

section composition
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y] [CompleteSpace E] [CompleteSpace Y]
variable {e e' : ℕ→ℝ→E} {f g : ℕ→E→Y} {q : ℕ}
private lemma faa_expands (p : ℕ→E→Y) (u : ℕ→ℝ→E) (h₁ : lucid p) (h₂ : lucid u) (h : Pinned u) : ∀ᶠ i : ℕ in atTop,
      fish q (p i ∘ u i)= (∑ c : OrderedFinpartition q, spray p c.length i (partitionVal u c i)) := by
    filter_upwards [h₁,h₂,h] with i hf hr ht
    unfold fish; rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (n:=q) _ (hr.of_le (finite_cap _)) le_rfl]
    · simp only [ht]; rfl
    rw [ht]; exact hf.of_le (finite_cap _)

lemma Junction.track (hh : Junction f g q) {X : ℕ→E} (ha : lucid f) (hb : lucid g) (hu : lucid e) (hv : lucid e') (hp : Pinned e) (ht : Pinned e')
    (he : ∀ m≤q, Tendsto (fun i=> fish m (e i)) atTop (𝓝 (X m)) ∧ Tendsto (fun i=>fish m (e' i)) atTop (𝓝 (X m))) :
    ∃ u:Y, Tendsto (fun i=>fish q (f i ∘ e i)) atTop (𝓝 u) ∧ Tendsto (fun i=>fish q (g i ∘ e' i)) atTop (𝓝 u) := by
  choose U hU hV using fun c : OrderedFinpartition q=> hh.evaluate c.length_le (partitionVal e c ·) (partitionVal e' c ·) (fun i=>(he _ (c.partSize_le i)).1) (fun i=>(he _ (c.partSize_le i)).2)
  exact ⟨∑ c : OrderedFinpartition q,U c,(tendsto_finsetSum _ fun c _=>hU c).congr' ((faa_expands f e ha hu hp).mono fun i hi=>hi.symm),
     (tendsto_finsetSum _ fun c _=>hV c).congr' ((faa_expands g e' hb hv ht).mono fun i hi=>hi.symm)⟩

-- lemma value_at (u : ℕ→Y) {A : T _ _ q} (h : Tendsto (fun _=> A) atTop (𝓝 A)) := h -- remove
variable {A B' : T E Y q}
lemma tensor_unique (h : Tendsto (spray f q) atTop (𝓝 A)) (he : Tendsto (spray g q) atTop (𝓝 B')) (ht : ∃ B, Tendsto (spray f q) atTop (𝓝 B) ∧ Tendsto (spray g q) atTop (𝓝 B)) : A=B' := ht.elim fun B ⟨h₁,h₂⟩=>(tendsto_nhds_unique h h₁).trans (tendsto_nhds_unique h₂ he)
lemma faa_transfer (hh : Junction f g (q-1)) {r : ℕ} (hr : 1 ≤ r) (ha : lucid f) (hb : lucid g) (hu : lucid e) (hv : lucid e') (hp : Pinned e) (ht : Pinned e')
    (hA : Tendsto (spray f q) atTop (𝓝 A)) (hB : Tendsto (spray g q) atTop (𝓝 B')) {X : ℕ→E}
    (he : ∀ m≤r, Tendsto (fun i=> fish m (e i)) atTop (𝓝 (X m)) ∧ Tendsto (fun i=>fish m (e' i)) atTop (𝓝 (X m)))
    (hq : ∀ c : OrderedFinpartition q, c.length < q → (∀ i, c.partSize i ≤ r) ∨ ∀ᶠ i in atTop,
      spray f c.length i (partitionVal e c i)=spray g c.length i (partitionVal e' c i)) :
    Tendsto (fun i=>fish q (f i ∘ e i) - fish q (g i ∘ e' i)) atTop (𝓝 (Tensor.diagonal A (X 1) - Tensor.diagonal B' (X 1))) := by
  let credit (c : OrderedFinpartition q) := if c.length=q then Tensor.diagonal A (X 1)-Tensor.diagonal B' (X 1) else 0
  let val (p : ℕ→E→Y) (e : ℕ→ℝ→E) (c : OrderedFinpartition q) (i:ℕ) := (spray p c.length i) (partitionVal e c i)
  have hval c : Tendsto (fun (i:ℕ)=>val f e c i - val g e' c i) atTop (𝓝 (credit c)) := by
    unfold val
    by_cases hc : c.length=q
    · have hpart (e : ℕ→ℝ→E) : (fun (i:ℕ)=>partitionVal e c i)=fun i=>fun _=>fish 1 (e i) := funext fun i=>funext fun j => by unfold partitionVal; rw [faa_eq c hc.ge j] -- replace
      unfold credit; rw [show partitionVal e c = _ from hpart e,show partitionVal e' c = _ from hpart e', hc,if_pos rfl]
      exact (view_cont.continuousAt.tendsto.comp (hA.prodMk_nhds (tendsto_pi_nhds.mpr fun _=>(he 1 hr).1))).sub (view_cont.continuousAt.tendsto.comp (hB.prodMk_nhds (tendsto_pi_nhds.mpr fun _=>(he 1 hr).2)))
    have hQ : c.length<q := by have h := c.length_le; omega
    rcases hq c hQ with h|h
    · obtain ⟨α,h₁,h₂⟩ := hh.evaluate (ρ:=c.length) (by omega) (partitionVal e c ·) (partitionVal e' c ·) (W:=fun i=>X (c.partSize i)) (fun i => (he _ (h i)).1) (fun i => (he _ (h i)).2)
      simpa only [credit,if_neg hc,sub_self] using h₁.sub h₂
    unfold credit; rw [if_neg hc]; exact tendsto_const_nhds.congr' (f₂:=fun (i:ℕ)=>_ - _) (h.mono fun i hi=>by simpa only [hi,sub_self])
  apply Tendsto.congr' ?_ (show Tendsto (fun i:ℕ=>∑ c:OrderedFinpartition q, (val f e c i-val g e' c i)) atTop (𝓝 _) from ?_)
  · filter_upwards [faa_expands (q:=q) f e ha hu hp, faa_expands (q:=q) g e' hb hv ht] with i hi hk; exact (show ∑ c : OrderedFinpartition q,(val f e c i - val g e' c i)= (∑ c : OrderedFinpartition q,val f e c i) - ∑ c:OrderedFinpartition q,val g e' c i from Finset.sum_sub_distrib ..).trans (by rw [hi,hk])
  rw [show (Tensor.diagonal A _-Tensor.diagonal B' (X 1)) =∑ c, credit c from ?_]
  · exact tendsto_finsetSum _ fun c _=> hval c
  rw [Finset.sum_eq_single (atomic q) (fun i _ h=> if_neg (show i.length≠q from fun hq=>h <| partition_top i hq)) (by simp)] -- orientation sum_eq_single term
  exact (if_pos (atomic_length q)).symm

variable [FiniteDimensional ℝ F] [CompleteSpace F]
lemma Junction.compose {p p' : ℕ→F→E} (h : Junction f g q) (h' : Junction p p' q) (ha : lucid f) (hb : lucid g) (hn : lucid p) (hN : lucid p') (hp : Pinned p) (hp' : Pinned p') : Junction (fun i=> f i ∘ p i) (fun i=>g i ∘ p' i) q := by
  refine viaDiag (lucid_comp ha hn hp) (lucid_comp hb hN hp') fun m hm v => ?_
  choose A h₁ h₂ using fun (j : Fin (q+1)) => junction_line h' hn hN (Fin.is_le j) v
  let X k := if h:k≤q then A ⟨k,by omega⟩ else 0
  refine (h.mono (by omega : m≤q)).track (X:=X) ha hb (lucid_pin v hn) (lucid_pin _ hN)
      (hp.mono fun i hi=> by simpa using hi) (hp'.mono fun i hi=> by simpa using hi) (fun k hk=> ?_)
  unfold X; rw [dif_pos (hk.trans hm)]; exact ⟨h₁ _,h₂ _⟩
-- lemma Junction.frozen (u : T E Y q) := u -- remove
lemma Junction.direction (h : Junction f g (q+1)) (v : E) (ha : lucid f) (hb : lucid g) : Junction (fun i=> Analysis.D v (f i)) (fun i=> Analysis.D v (g i)) q := by
  have hg {f : ℕ→E→Y} (ha : lucid f) : lucid (fun i=>Analysis.D v (f i)) := ha.mono fun i hi=> Analysis.dSmooth hi _ (by simp)
  refine viaDiag (hg ha) (hg hb) fun m hm u=>?_ -- shadow
  obtain ⟨z,h₁,h₂⟩ := h.evaluate (Nat.succ_le_succ hm) (fun _=> Fin.snoc (fun (_ : Fin m)=> u) v) (fun _=> Fin.snoc (fun (_ : Fin m)=> u) v) (fun _=>tendsto_const_nhds) (fun _=>tendsto_const_nhds)
  exact ⟨z,h₁.congr' (ha.mono fun i hi=>by dsimp only []; rw [ray_tag (Analysis.D v (f i)) ((Analysis.dSmooth hi _ (m:=WithTop.some ⊤) (by change ↑((⊤ : ℕ∞) + (1:ℕ∞)) ≤ (∞:ℕ∞ω); simp)).of_le (finite_cap m))]; exact Analysis.snoc_jet (hi.of_le (finite_cap (m+1))) _ _),h₂.congr' (hb.mono fun i hi=>by dsimp only []; rw [ray_tag (Analysis.D v (g i)) ((Analysis.dSmooth hi _ (m:=WithTop.some ⊤) (by change ↑((⊤ : ℕ∞) + (1:ℕ∞)) ≤ (∞:ℕ∞ω); simp)).of_le (finite_cap m))]; exact Analysis.snoc_jet (hi.of_le (finite_cap (m+1))) _ _)⟩
end composition
end YM.UVExt.Paths
