import YM.RG06.Continuum.GaugeFix

/-!
# The polynomial identity quotient is exact on every smooth connection (here at center)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Function Tensor Labels Maxwell MvPolynomial
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d k :ℕ}{A:Connection G}

lemma rad_coeff (s:Smooth A)(k:ℕ)(z:E4) :
    ∑ i:Axis,z i • diagonal (Tensor.coeff (A i) k 0) z=
     (k.factorial:ℝ)⁻¹ • iteratedDeriv k (radTest A z) 0 := by
  have he(k:ℕ): (k:WithTop ℕ∞) ≤ ∞:=WithTop.coe_le_coe.mpr le_top
  have hs(i:Axis):ContDiffAt ℝ k (A i ∘ fun t:ℝ=> t • z) 0:= (ContDiff.contDiffAt (s i)).of_le (he k)|>.comp (f:=fun t:ℝ=>t • z) (0:ℝ) (contDiffAt_id.smul contDiffAt_const) -- x param explicit?
  unfold radTest; rw [iteratedDeriv_fun_sum (by exact fun i _=> ContDiffAt.const_smul (z i) (hs i)),Finset.smul_sum];
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [iteratedDeriv_fun_const_smul_field,YM.Next.Foundations.iteratedDeriv_on_line (show ContDiffAt ℝ k (A i) 0 from (ContDiff.contDiffAt (s i)).of_le (he _)),Tensor.diagonal,Tensor.coeff,smul_apply,smul_comm]
  rfl

/-- Encode a connection with its radial obstructions removed, into the existing `Labels.Taylor`
finite tower (zero elsewhere). -/
def snapshot (k:ℕ)(A:Connection G)(s:Smooth A)(h:killed k A): Labels.Jet G:=fun j=>
   if he:j+1<k then ⟨(fun i=> Tensor.coeff (A i) (j+1) 0),
      (fun i=> Tensor.coeff_symm ((ContDiff.contDiffAt (s i)).of_le (show (↑(j+1:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top))),
      (fun z=>by rw [rad_coeff s _ z,h _ he,smul_zero])⟩ else 0

lemma base_zero (_s:Smooth A)(h:killed k A)(hk:0 < k)(i:Axis): A i 0=0:=by
  have he:= h 0 hk (basis i)
  rw [iteratedDeriv_zero, radTest,zero_smul, Finset.sum_eq_single i] at he
  · simpa using he
  · intro b _ h; simp only [basis_eq, if_neg h,zero_smul]
  simp

lemma snapshot_tensor (s:Smooth A)(h:killed k A) {j d:ℕ}(hd:j+2 ≤ d)(hk:j+1<k)(i:Axis) :
    iteratedFDeriv ℝ (j+1) (A i) 0= iteratedFDeriv ℝ (j+1) (radField d (snapshot k A s h) i) 0:=by
  have H:(snapshot k A s h j).val i= Tensor.coeff (A i) (j+1) 0:=by unfold snapshot; rw [dif_pos hk]
  have he:= Raw.diagonal_calc i d (snapshot k A s h) j hd
  rw [H] at he
  exact smul_right_injective _ (show ((↑(j+1).factorial:ℝ)⁻¹)≠0 by positivity) he.symm
lemma snapshot_jet (s:Smooth A)(h:killed d A)(w : List Axis)(a:Axis)(hk:w.length+1 ≤ d) :
    derivative w (A a) 0= derivative w (radField d (snapshot d A s h) a) 0:=by
   cases w
   next=> simp [derivative,base_zero s h (i:=a) (by simp at hk; omega)]
   next i w=>
    rw [Raw.derivative_tensor (i::w) _ _ rfl (s a),Raw.derivative_tensor (i::w) _ _ rfl (rad_smooth d _ a)]
    simp only [List.length_cons,snapshot_tensor s h (i:=a) (d:=d) (j:=w.length) (by exact hk) (by simp only [List.length_cons] at hk; omega)]
lemma snapshot_read {p:Raw.Pol G}{n l:ℕ}(s:Smooth A)(h:killed d A)(hp:Tier Raw.measure (n,l) p)(ht:n ≤ d):
    Raw.read A 0 p= Raw.read (radField d (snapshot d A s h)) 0 p:=by
  conv_lhs=> rw [p.as_sum, map_sum]
  conv_rhs=> rw [p.as_sum, map_sum]
  refine Finset.sum_congr rfl fun b hb=> ?_; unfold Raw.read; rw [eval_monomial,eval_monomial]; refine congrArg _ ?_
  unfold Finsupp.prod; refine Finset.prod_congr rfl fun a ha=>?_ ; simp only
  rw [snapshot_jet s h a.chain a.primary (show a.chain.length+1 ≤ d from (Raw.scope hp (support_subset_vars_of_mem_support hb ha)).trans ht)]

lemma snapshot_cov {d j:ℕ}(g:ℝ)(s:Smooth A)(h:killed d A)(w:Fin j→Axis)(i k:Axis)(hk:j+2≤d): covJet g A w i k 0= covJet g (radField d (snapshot d A s h)) w i k 0:=by
  ext a; apply Complex.ofReal_injective
  let B:=radField d (snapshot d A s h)
  have hB:Smooth B:=rad_smooth d _
  change (↑(covJet g A w i k 0 a) : ℂ)=↑(covJet g B w i k 0 a)
  rw [← Raw.frame_eq A s, ← Raw.frame_eq B hB,Raw.coeff_rebuild g w i k a (j+1) le_rfl, map_sum,map_sum]
  refine Finset.sum_congr rfl fun b _=> ?_; rw [MvPolynomial.smul_eq_C_mul,map_mul,map_mul,snapshot_read s h (Raw.grade_frame w i k a b) hk]
  simp only [Raw.read,eval_C]; rfl -- done?

lemma snapshot_eval {d:ℕ}(g:ℝ)(s:Smooth A)(h:killed d A)(v:Form.Field G d):
    Form.actual g A 0 v.val=Form.actual g (radField d (snapshot d A s h)) 0 v.val:=by
  unfold Form.actual Form.applyTo
  rw [v.val.as_sum,map_sum,map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]; refine congrArg _ ?_
  simp_rw [Finsupp.prod]; refine Finset.prod_congr rfl fun a ha=>?_ ; unfold Form.coords Form.evaluate
  rw [snapshot_cov _ s h a.chain _ _ (Form.in_bounds v.property.1 hi _ ha)]

theorem cov_orbit (g:ℝ)(A:Connection G)(hg:g≠0)(h:Smooth A)(d:ℕ):∃ J:Labels.Jet G,∀ p:Form.Field G d,
    Form.actual g A 0 p.val=Form.actual g (radField d J) 0 p.val:=by
  obtain ⟨B,s,q,v⟩:= orbit g d hg A h
  refine ⟨snapshot d B s q,fun p=>?_⟩; apply Eq.trans _ (snapshot_eval _ s q p); exact congrArg (fun x=> Form.applyTo x p.val) v.symm

lemma smooth_kernel (g:ℝ)(hg:g≠0){d:ℕ}(p:Form.Field G d): p∈Form.radical G g d ↔ ∀ A:Connection G,Smooth A→Form.actual g A 0 p.val=0 := by
  rw [Form.radial_tests]; exact ⟨fun h A s=> (Exists.choose_spec (cov_orbit g A hg s d) p).trans (h _),fun e J=>e _ (rad_smooth d J)⟩
end YM.RG06.Continuum
