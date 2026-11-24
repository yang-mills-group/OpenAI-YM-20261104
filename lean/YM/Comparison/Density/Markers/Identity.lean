import YM.Comparison.Density.Markers.Matching
/-! Exact exponential restoration. Absolute convergence in NONZERO-marker
orders too. Never taking a log of a gas with flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Markers
open Function Lattice RG Wilson MeasureTheory Filter Marker Finset Pert.Attach
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable (p : BudgetPoint) (A : Activities G n) (K H : Supply R G n) (U : Config G n)

lemma packet_sn (b) : before p A K H U b = packet p A K b.toLeft U * ∏ i∈b.toRight, H i U:= by
  unfold before packet; split_ifs
  · exact prod_sum_eq_prod_toLeft_mul_prod_toRight b (bonds K H U)
  rw [zero_mul]

variable {K A H U p}

lemma finite_bill (s : Finset ℕ) (r : Finset ℕ) :
    ∑ i∈(s.disjSum r).powerset,before (R:=R) p A K H U i=
      (∑ b∈s.powerset,packet p A K b U)*(∏ j∈r, (1+H j U)):= by
  rw [prod_one_add,sum_mul_sum]; let Z:=s.disjSum r
  -- use existing split equiv; avoid dependent DecidableEq transports
  let e:= (@Finset.sumEquiv ℕ ℕ).toEquiv
  have he: Z.powerset=(s.powerset ×ˢ r.powerset).image e.symm:= by
    have ht : Z=e.symm (s,r):= rfl
    ext i
    constructor
    · intro hi; rw [mem_powerset] at hi; refine mem_image.mpr ⟨e i,mem_product.mpr ⟨?_,?_⟩,e.symm_apply_apply _⟩
      · apply mem_powerset.mpr; exact (@Finset.sumEquiv ℕ ℕ|>.monotone hi).1.trans (show Z.toLeft ⊆ s by simp [Z])
      apply mem_powerset.mpr; exact (@Finset.sumEquiv ℕ ℕ|>.monotone hi).2.trans (show Z.toRight ⊆ r by simp [Z])
    rintro h; obtain ⟨⟨v,w⟩,hv,rfl⟩:= mem_image.mp h
    obtain ⟨h₁,h₂⟩:=mem_product.mp hv; rw [mem_powerset,ht]
    exact (@Finset.sumEquiv ℕ ℕ|>.symm.monotone (show (v,w)≤(s,r) from ⟨mem_powerset.mp h₁,mem_powerset.mp h₂⟩))
  rw [show s.disjSum r= Z from rfl,he,sum_image e.symm.injective.injOn,sum_product]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> ?_
  rw [packet_sn,show (e.symm (i,j)).toLeft=i from congr_arg Prod.fst (e.apply_symm_apply (i,j)),show (e.symm (i,j)).toRight=j from congr_arg Prod.snd (e.apply_symm_apply (i,j))]

def mist (p : BudgetPoint) (A : Activities G n) (K : Supply R G n) (V : Config G n) := ∑' b, packet p A K b V

variable {w : V → ℝ}

lemma initial_sums (hw : ∀ i,0<w i) (h : Summable fun i=> Poly.price w (K i U))
    (he : Summable fun i=> Poly.price w (H i U)) :
    Summable (before (R:=R) p A K H U) := by
  let f:=fun i => Poly.price w (bonds K H U i)
  have hs : Summable f:=Summable.sum _ h he
  apply (Poly.budgeted hw (summable_finsetProd_of_summable_nonneg (f:=f) (fun i=> Poly.nonnegative hw _) hs) ?_).1
  intro i; unfold before; split; exact Poly.multiple hw _ _
  simp only [Poly.zero_price]; exact prod_nonneg fun i _=> Poly.nonnegative hw _

lemma mist_converges (hw : ∀ i, 0<w i) (h : Summable fun i => Poly.price w (K i U)) :
    HasSum (fun i=>packet (R:=R) p A K i U) (mist p A K U) := by
  let y:= fun i=>Poly.price w (K i U)
  have he : Summable (fun i:Finset ℕ=> ∏ j∈i,y j):= summable_finsetProd_of_summable_nonneg (fun i=> Poly.nonnegative hw _) h
  have hz i : Poly.price w (packet p A K i U) ≤ ∏ j∈i,y j:= by
    unfold packet; split; exact Poly.multiple hw _ _
    simp only [Poly.zero_price]; exact prod_nonneg fun i _=> Poly.nonnegative hw _
  exact (Poly.budgeted hw he hz).1.hasSum

variable [Fintype V]
attribute [local simp] Next.Rank.Exponential.part_sub

lemma magnify_add {a b : ℝ} {c d : Poly R} (hc : c.part R.quiet=0) (hd : d.part R.quiet=0) :
    magnify (a+b) (c+d) = magnify a c*magnify b d := by
  simp only [magnify,Real.exp_add,embedded_mul,Next.Rank.Exponential.pass_add _ _ hc hd]; ring
lemma one_magnify : magnify 0 (0:Poly R)=1:= by unfold magnify; rw [Real.exp_zero,embedded_one,one_mul,Next.Rank.Exponential.pass_zero]
private lemma counted {ι: Type} (s : Finset ι) (a : ι→ Poly R) {b : ι →ℝ} (h : ∀ i∈s,(a i).part R.quiet=0) :
    ∏ i∈s, (1+companion (b i) (a i)) = magnify (∑ i∈s,b i) (∑ i∈s,a i) := by
  induction s using Finset.induction_on with
  | empty=>rw [prod_empty,sum_empty,sum_empty,one_magnify]
  | insert i s hi ih=>
    have hm : ∀ i∈s,(a i).part R.quiet=0:= fun j hj=> h j (mem_insert_of_mem hj)
    rw [prod_insert hi,sum_insert hi,sum_insert hi,magnify_add (h i (mem_insert_self ..)) (by rw [Poly.part_sum]; exact sum_eq_zero hm), ih hm]; unfold companion; rw [add_sub_cancel]
lemma collected {h : ℕ → ℝ} {F : ℕ→ Poly R} (hw : ∀ i, 0<w i)
    (hK : Summable fun i => Poly.price w (K i U)) (hH : Summable fun i => Poly.price w (H i U))
    (hr : ∀ i,H i U=companion (h i) (F i)) (hz : ∀ i, (F i).part R.quiet=0)
    (ha : Summable h) (hf : Summable F) :
    HasSum (before p A K H U) (mist p A K U*magnify (∑' i,h i) (∑' i,F i)) := by
  let P:= before p A K H U
  let g:= mist p A K U*magnify (∑' i,h i) (∑' i,F i)
  have hs : Summable P:= initial_sums hw hK hH
  let b (i : Finset ℕ):= i.disjSum i
  have ht : Tendsto b atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun i j hij => ?_) ?_
    · intro a h; rcases a with a|a <;> simp [b] at * <;> exact hij h
    intro i; rcases i with j|j <;> exact ⟨{j},by simp [b]⟩
  have hb : Tendsto (fun i: Finset ℕ=> ∑ j∈(b i).powerset,P j) atTop (𝓝 g) := by
    simp_rw [b,P,finite_bill,hr, counted _ F (fun i _=> hz i)]
    have he : Tendsto (fun i:Finset ℕ=> magnify (∑ j∈i,h j) (∑ j∈i,F j)) atTop (𝓝 (magnify (∑' i,h i) (∑' i,F i))) := by
      apply Filter.Tendsto.mul
      · exact embedded_cont.continuousAt.tendsto.comp (Real.continuous_exp.continuousAt.tendsto.comp ha.hasSum)
      exact Poly.pass_cont.continuousAt.tendsto.comp hf.hasSum
    exact ((mist_converges hw hK (p:=p) (A:=A)).comp tendsto_finset_powerset_atTop_atTop).mul he
  have he : ∑' i,P i=g := tendsto_nhds_unique (hs.hasSum.comp (tendsto_finset_powerset_atTop_atTop.comp ht)) hb
  exact show HasSum P g from he ▸ hs.hasSum

lemma gas_eq {X : Corrections G n} {h : ℕ→ ℝ} {M : ℕ→ Poly R}
    (hw : ∀ i,0<w i) (hK : Summable fun i => Poly.price w (K i U)) (hH : Summable fun i => Poly.price w (H i U))
    (hr : ∀ i,H i U=companion (h i) (M i)) (hz : ∀ i,(M i).part R.quiet=0)
    (ha : Summable h) (hf : Summable M) (hX : ∀ i,K i U≠0 → (A.forced i).eligible p.threshold U)
    (hM : ∀ i,Healthy p.threshold (X.region i) U → H i U=0) (F : Activities G n) :
    mist p (Pert.Attach.attach A X p.threshold F) (chain p A X K H) U=
      mist p A K U*magnify (∑' i,h i) (∑' i,M i):= (full_cover hX hM F (collected hw hK hH hr hz ha hf)).tsum_eq
end YM.Comparison.Density.Markers
