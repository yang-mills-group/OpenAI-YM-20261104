import YM.Pert.Scale.Radial
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 640000
namespace YM.Pert.Scale
open Maxwell Set Topology Filter Function Tensor Analysis Wick Occ Extra.FD
open scoped Topology Classical ContDiff BigOperators
variable {G : Gauge}
lemma leg_stretch {j l : ℕ} {x : E4} (hx : x≠0) (p : Probe G j) (q : Probe G l) {t : ℝ} (ht : t≠0) :
    t^(j+l+4) * pairing (show t • x∈away from smul_ne_zero ht hx) p q = pairing (show x∈away from hx) p q := by
  have e : x∈away := hx; have f : t • x∈away := smul_ne_zero ht hx
  have h : (t^(j+l+4):ℝ) • pairing (G:=G) (j:=j) (l:=l) f = pairing e := by
     refine LinearMap.ext_on spans ?_
     rintro p ⟨u,c,i,a,rfl⟩
     refine LinearMap.ext_on spans ?_
     rintro q ⟨v,d,k,b,rfl⟩
     change t^(j+l+4) * pairing f _ _ = pairing e _ _
     rw [raw_mixed u v i a k b c d hx, raw_mixed u v i a k b c d (smul_ne_zero ht hx)]
     split_ifs
     · change t ^ (j+l+4) * ((-1)^l * _) = (-1)^l * _
       rw [mul_left_comm (t^_),show j+l+4=4+j+l by omega]
       exact congrArg ((-1)^l * ·) (((uncolored i a k b).coeff u).coeff v |>.stretch hx ht)
     simp
  exact congrArg (fun z => z p q) h

lemma bit_stretch (p q : Slot G) {x y : E4} (h : x≠y) {t : ℝ} (ht:t≠0) :
   (t:ℂ)^(costKey p+costKey q) * entry p q (t•x) (t•y)=entry p q x y := by
  unfold entry
  rw [← smul_sub]
  have he : costKey p+costKey q = p.1+q.1+4 := by unfold costKey; omega
  rw [he,← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact congrArg _ (leg_stretch (sub_ne_zero.mpr h) (coordinateLeg p) (coordinateLeg q) ht)

variable {n : ℕ}
lemma edge_stretch {W : Powers G n} (P : Matching W) (i : Occ W) {x : Points n} (hx : x∈conf n) {t : ℝ} (h:t≠0) :
    (t:ℂ)^(costKey i.probe+costKey (partner P i).probe) * edge (t•x) i (partner P i) = edge x i (partner P i) :=
  bit_stretch _ _ ((hx : Injective x.ofLp).ne (Ne.symm (different P i))) h

private lemma corners_tally {W : Powers G n} (P : Matching W) :
    (∑ i ∈ corners P, (costKey i.probe + costKey (partner P i).probe)) = ∑ i : Occ W, costKey i.probe := by
  rw [Finset.sum_add_distrib]
  have h₁ : (∑ i∈corners P,costKey (partner P i).probe)=∑ i∈(Finset.univ \ corners P),costKey i.probe := by
    refine Finset.sum_equiv (partner P) ?_ (fun _ _=>rfl)
    intro i; simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,orientation,not_not]
  rw [h₁,← Finset.sum_union Finset.disjoint_sdiff]
  simpa only [Finset.union_sdiff_self_eq_union, Finset.union_eq_right.mpr (Finset.subset_univ _)]

def ranks {W : Powers G n} : Occ W ≃ (Σ i : Fin n, Σ j : (W i).support, Fin (W i j.val)) where
  toFun p := ⟨p.label,⟨p.probe,Finsupp.mem_support_iff.mpr (show W p.label p.probe ≠ 0 from (lt_of_le_of_lt p.index.zero_le p.legit).ne')⟩,p.index,p.legit⟩
  invFun p := atSlot p.1 p.2.1 p.2.2 p.2.2.isLt
  left_inv _ := rfl
  right_inv _ := rfl

private lemma whole {W : Powers G n} :
    (∑ i : Occ W, costKey i.probe) = ∑ i, Finsupp.weight costKey (W i) := by
  exact (Fintype.sum_equiv ranks _ (fun p => costKey p.2.1.val) (fun _=>rfl)).trans (by
    simp only [Fintype.sum_sigma,Finsupp.weight_apply,Finsupp.sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    apply Finset.sum_congr rfl; intro i _
    exact (Finset.sum_attach _ (fun v => W i v • costKey v)))

private lemma graph_stretch {W : Powers G n} (P : Matching W) {x : Points n} (hx : x∈conf n) {t : ℝ} (h:t≠0) :
    (t:ℂ)^(∑ i : Occ W,costKey i.probe)*graph (t•x) P = graph x P := by
  rw [← corners_tally P, Occ.graph, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => edge_stretch P i hx h

lemma circuit (W : Powers G n) {x : Points n} (hx : x∈conf n) {t : ℝ} (h:t≠0) :
    (t:ℂ)^(∑ i, Finsupp.weight costKey (W i)) * monomial (t•x) W = monomial x W := by
  rw [← whole]
  simp_rw [Wick.monomial, Finset.mul_sum,graph_stretch _ hx h]

end YM.Pert.Scale
