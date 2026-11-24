import YM.MatchingLedger.Books.Jets

/-!
# Polynomial specialization and locality on germ stencils

Honest norm prices even when variables collide. Use with fixed-site charts in S-D. The support
statements here are for *Taylor polynomials* in coupling program, not for reclosure as
supported functions on actual fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books
open Function Filter Metric MvPolynomial
open PertExtension.Series
open scoped Classical Topology ContDiff BigOperators
variable {ι α : Type*}
section transfer
variable (f : ι→ Poly α)

lemma present (x:Field α)(p:Poly ι): read x (aeval f p)= read (fun i=>read x (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a=> rw [aeval_C,show algebraMap ℝ _ a=C a from rfl,read_C,read_C]
  | add p q hp hq=> rw [_root_.map_add, read_add, read_add,hp,hq]
  | mul_X p i hp=> rw [_root_.map_mul, aeval_X,read_mul,read_mul,hp, read_X]

private lemma morph (s : Token ι)(c:ℝ) : aeval f (monomial s c)= C c * ∏ i∈s.support,f i ^ s i := by rw [aeval_monomial]; rfl

lemma present_cost (p : Poly ι) {M:ℝ} (hm:1≤M) (d:ℕ) (he:p.totalDegree ≤ d) (h:∀ i∈p.vars, fare (f i) ≤ M) :
    fare (aeval f p) ≤ fare p * M^d:=by
  nth_rw 1 [p.as_sum]; rw [_root_.map_sum]; apply (fare_sum ..).trans; unfold fare; rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi=>?_; change fare (aeval f (monomial i (p.coeff i))) ≤ _; rw [morph]; apply (fare_mul ..).trans; rw [fare_C]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (fare_product ..).trans; apply le_trans (b:= M^heft i) _ (pow_le_pow_right₀ hm ((le_totalDegree hi).trans he)); unfold heft Finsupp.sum
  rw [← Finset.prod_pow_eq_pow_sum]; apply Finset.prod_le_prod (fun i _=> fare_nn _); intro j hj; exact (fare_pow ..).trans (pow_le_pow_left₀ (fare_nn _) (h _ ((mem_vars_iff_mem_support _).mpr ⟨_,hi,hj⟩)) _)

lemma present_degree (p : Poly ι) {d:ℕ} (h : ∀ i∈p.vars, (f i).totalDegree ≤ d) : (aeval f p).totalDegree ≤ p.totalDegree * d := by
  nth_rw 1 [p.as_sum]; rw [_root_.map_sum]; apply totalDegree_finsetSum_le; intro i hi
  rw [morph]
  apply (totalDegree_mul ..).trans; rw [totalDegree_C,zero_add]; apply (totalDegree_finsetProd ..).trans
  refine le_trans ?_ (Nat.mul_le_mul_right d (le_totalDegree hi)); unfold Finsupp.sum; rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j hj=> (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ (h _ ((mem_vars_iff_mem_support _).mpr ⟨_,hi,hj⟩))))

lemma present_vars [DecidableEq α] {s : Finset α} (p : Poly ι) (h : ∀ i∈p.vars,(f i).vars ⊆ s) : (aeval f p).vars ⊆ s := by
  nth_rw 1 [p.as_sum]; rw [_root_.map_sum]; refine Finset.Subset.trans (vars_sum_subset ..) (Finset.biUnion_subset.mpr ?_)
  intro i hi; rw [morph]; refine Finset.Subset.trans (vars_mul ..) (Finset.union_subset ?_ (Finset.Subset.trans (vars_prod _) (Finset.biUnion_subset.mpr ?_)))
  · simp
  exact fun j hj=> Finset.Subset.trans (vars_pow ..) (h _ ((mem_vars_iff_mem_support j).mpr ⟨_,hi,hj⟩))
end transfer

-- Freeze external B in this computation. Later project back to result with that same argument.
section external
variable (y : Field α)
def install : Poly (ι ⊕ α) →ₐ[ℝ] Poly ι := aeval (Sum.elim X (fun i=> C (y i)))
lemma install_read (x : Field ι)(p : Poly (ι ⊕ α)): read x (install y p)= read (Sum.elim x y) p:=by
  rw [install,present]; congr 2; funext i; cases i; exact read_X ..; exact read_C ..
lemma install_gradient (j : ι)(p : Poly (ι ⊕ α)) : pderiv j (install y p)= install y (pderiv (.inl j) p):=
  (aeval_sumElim_pderiv_inl p y j).symm
lemma install_degree (p : Poly (ι ⊕ α)) : (install y p).totalDegree≤p.totalDegree:= by
  apply (present_degree (d:=1) ..).trans (mul_one _).le; intro i _; cases i; exact (totalDegree_X _ (R:=ℝ)).le; exact (totalDegree_C (σ:=ι) _).trans_le (Nat.zero_le _)
lemma install_cost (p : Poly (ι ⊕ α))(M:ℝ)(hm:1≤M) (d:ℕ) (he:p.totalDegree ≤ d)(h:∀ i, Sum.inr i∈p.vars → ‖y i‖≤M) : fare (install y p) ≤ fare p*M^d:=
  present_cost _ p hm d he fun i hi=> by cases i with | inl q=> exact (fare_X q).trans_le hm | inr q=> exact (fare_C (ι:=ι) _).trans_le (h q hi)
lemma install_loc (p : Poly (ι ⊕ α)) (s : Finset ι) (h : ∀ i, Sum.inl i∈ p.vars → i∈s) : (install y p).vars ⊆ s:= by
  apply present_vars; intro i hi; cases i with
  | inl q=> exact (by simp [h q hi] : (MvPolynomial.vars (X q:Poly ι))⊆s)
  | inr q=> exact (by simp : MvPolynomial.vars (C (y q) : Poly ι)⊆s)
end external

section locality
variable [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι] (s : Finset ι)

def crop (x:Field ι) : Field ι := s.piecewise x (fun _=>0)
omit [Fintype ι] in
lemma crop_apply (x : Field ι) (i:ι): crop s x i= if i∈s then x i else 0 := rfl
def cropMap : Field ι →L[ℝ] Field ι:= ContinuousLinearMap.pi (fun i=> if i∈s then ContinuousLinearMap.proj i else 0)
omit [Fintype ι] in
lemma crop_true (x : Field ι) : cropMap s x=crop s x:= by ext i; by_cases h:i∈s <;> simp [cropMap,crop,h]
omit [Fintype ι] in
lemma crop_linear (x y : Field ι) (p t : ℝ) : crop s (p • x + t • y)=p • crop s x+t • crop s y := by simp_rw [← crop_true, _root_.map_add,_root_.map_smul]
-- general continuity at for right-composition (not whole-space Cⁿ assumption)
omit [DecidableEq ι] [DecidableEq α] in
lemma at_right (Y : Field ι →L[ℝ] Field α) (f : Field α→ℝ) (x : Field ι) {n : ℕ} (h : ContDiffAt ℝ n f (Y x)) :
    iteratedFDeriv ℝ n (f ∘ Y) x=(iteratedFDeriv ℝ n f (Y x)).compContinuousLinearMap (fun _=> Y):=by
  obtain ⟨s,hs,hx,h⟩ := h.contDiffOn' (show (n:WithTop ℕ∞)≤ n from le_rfl) (by simp)
  have h' : ContDiffOn ℝ n f s:= by simpa using! h
  have hu : Y ⁻¹' s∈𝓝 x := (hs.preimage Y.continuous).mem_nhds hx
  rw [← iteratedFDerivWithin_of_isOpen n (hs.preimage Y.continuous) hx, ContinuousLinearMap.iteratedFDerivWithin_comp_right Y h' hs.uniqueDiffOn (hs.preimage Y.continuous).uniqueDiffOn hx (le_refl _),iteratedFDerivWithin_of_isOpen n hs hx]

-- If factors through crop, tracking the Taylor polynomial costs no more variables than the
-- box. Need source geometry separately.
def Restricted (v : Field ι → ℝ) (s : Finset ι) : Prop := v =ᶠ[𝓝 0] (v ∘ crop s)
variable {s}

private lemma slots {v : Field ι→ℝ}{n:ℕ}(h:Restricted v s)(hp:ContDiffAt ℝ n v 0)(r : Fin n → ι)(j:Fin n)(hh:r j ∉ s):
    (iteratedFDeriv ℝ n v 0) (axis ∘ r)=0:=by
  have he : v =ᶠ[𝓝 0] (v ∘ cropMap s):= by simp_rw [Restricted,← _root_.funext (crop_true s)] at h; exact h
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, at_right (cropMap s) v 0 (by rw [_root_.map_zero]; exact hp), ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply ContinuousMultilinearMap.map_coord_zero _ j
  ext i; rw [crop_true, crop_apply]; split
  · rename_i hi; change axis (r j) i=0; rw [axis_part,if_neg (fun x:i=r j=>hh (x ▸ hi))]
  rfl

private lemma refuse {v : Field ι→ℝ}{n:ℕ}(h:Restricted v s)(hp:ContDiffAt ℝ n v 0)(r:Fin n→ι)(g: ¬ (∀ i,r i∈s)) :
    (iteratedFDeriv ℝ n v 0) (axis ∘ r)=0:= by push Not at g; obtain ⟨j,hj⟩:=g; exact slots h hp _ j hj

lemma packet_vars {v : Field ι→ℝ}{n:ℕ}(h:Restricted v s)(hp:ContDiffAt ℝ n v 0): (packet v n).vars ⊆ s := by
  unfold packet; rw [Algebra.smul_def]; refine Finset.Subset.trans (vars_mul ..)
    (Finset.union_subset (by simp) (Finset.Subset.trans (vars_sum_subset ..) (Finset.biUnion_subset.mpr ?_)))
  intro y _; by_cases he : ∀ i, y i∈s
  · rw [Algebra.smul_def]; apply Finset.Subset.trans (vars_mul ..)
    exact Finset.union_subset (by simp) (Finset.Subset.trans (vars_prod _) (Finset.biUnion_subset.mpr (fun i _=> by simp [he i])))
  rw [refuse h hp _ he,zero_smul]; simp

lemma packet_cost {v : Field ι→ℝ}{n:ℕ}(h:Restricted v s)(hp:ContDiffAt ℝ n v 0)(M:ℝ) (hm:‖iteratedFDeriv ℝ n v 0‖ ≤ M) :
    fare (packet v n) ≤ M*(s.card:ℝ)^n := by
  let H:=iteratedFDeriv ℝ n v 0; let W := fun y : Fin n→ι => H (axis ∘ y) • ∏ i:Fin n,(X (y i) : Poly ι)
  let p : ℝ:= (n.factorial:ℝ)⁻¹; have he := @_root_.Nat.factorial_pos n; have h1 : ‖p‖ ≤ 1:=by unfold p; rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast he)
  let T:= Fintype.piFinset (fun _ : Fin n => s)
  have hz : packet v n=p • ∑ i∈T, W i:=by
     change p • ∑ i, W i= _; apply congr_arg
     apply Eq.symm; apply Finset.sum_subset (Finset.subset_univ _); intro i _ hI; have he : ¬ ∀ j,i j∈s := fun h=> hI (Fintype.mem_piFinset.mpr h); unfold W H; rw [refuse h hp _ he,zero_smul]
  rw [hz]; apply (fare_scale ..).trans; apply le_trans (mul_le_of_le_one_left (fare_nn _) h1)
  refine (fare_sum ..).trans ((Finset.sum_le_sum (g:=fun _=>M) (fun i _=>?_)).trans_eq ?_)
  · apply (fare_scale ..).trans; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    · exact (H.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) (by refine le_trans (Finset.prod_le_prod (g:=fun _=> (1:ℝ)) (fun _ _=> norm_nonneg _) (fun i _=> norm_axis ..)) (by simp))).trans hm)
    apply (fare_product ..).trans; simp [fare_X]
  unfold T; rw [Finset.sum_const,nsmul_eq_mul,Fintype.card_piFinset]; simp [mul_comm]

end locality
end YM.MatchingLedger.Books
