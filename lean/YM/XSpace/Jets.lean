import YM.FiniteVolumeClosure.A0bOriginals.Bare

/-! # Taylor series on real direction spaces (complex polynomial convention) -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Formal
open Function Set Filter MeasureTheory MvPolynomial
open scoped Topology InnerProductSpace BigOperators ContDiff
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (b : Module.Basis ι ℝ E)

def JetC (f : E → ℂ) := PowerSeries.mk fun k=>
  (k.factorial : ℂ)⁻¹ • ∑ i : Fin k → ι, C (iteratedFDeriv ℝ k f 0 (fun r=> b (i r))) * ∏ r, X (i r)

def test (x : E) := aeval (R:=ℂ) fun i=> (↑(b.equivFun x i):ℂ)
lemma using_test {p q : MvPolynomial ι ℂ} (h : ∀ x, test b x p=test b x q) : p=q := by
  apply MvPolynomial.funext_set (fun _=>Set.range Complex.ofReal) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose v hv using fun i=> hx i (Set.mem_univ _)
  obtain ⟨a,H⟩:=b.equivFun.surjective v
  specialize h a; unfold test at h; rw [H,show (fun i=>(↑(v i):ℂ))=x from _root_.funext hv] at h; exact h

lemma jet_value (f : E → ℂ) (k : ℕ) (x : E) : test b x (PowerSeries.coeff k (JetC b f))=
    (k.factorial:ℂ)⁻¹ * iteratedFDeriv ℝ k f 0 (fun _=>x) := by
  classical
  rw [JetC, PowerSeries.coeff_mk]; simp only [test,map_smul,map_sum,map_prod,map_mul, aeval_X, aeval_C,smul_eq_mul, Algebra.algebraMap_self_apply]
  congr 1
  let F := iteratedFDeriv ℝ k f 0
  have he := F.map_sum (fun (_ : Fin k) (i : ι) => b.repr x i • b i)
  simpa only [b.sum_repr, Module.Basis.equivFun_apply,F.map_smul_univ (fun _=>_) (fun _=>_), Complex.real_smul, smul_eq_mul,Complex.ofReal_prod,F,mul_comm] using he.symm

lemma jets_at {x : E} {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (L : D →L[ℝ] E) (f : E → ℂ) {z : D} {k : ℕ} (H : L z=x) (hf : ContDiffAt ℝ (k:ℕ∞ω) f x) :
    iteratedFDeriv ℝ k (f ∘ L) z = (iteratedFDeriv ℝ k f x).compContinuousLinearMap (fun _=>L) := by
  obtain ⟨s,hs,h⟩ := hf.contDiffOn (m:=(k:ℕ∞ω)) le_rfl (by simp)
  obtain ⟨t,ht,hT,hx⟩:=mem_nhds_iff.mp hs
  let U:=L ⁻¹' t; have he:=h.mono ht; have hv:=hT.preimage L.continuous
  have hu:L z∈t:=H.symm▸hx
  have hw:= L.iteratedFDerivWithin_comp_right he hT.uniqueDiffOn hv.uniqueDiffOn hu (show (↑k:ℕ∞ω) ≤ k from le_rfl)
  rw [H, iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn hf hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hv.uniqueDiffOn ((show ContDiffAt ℝ (↑k) f (L z) from H.symm▸hf).comp z L.contDiff.contDiffAt) hu] at hw; exact hw

lemma jet_ray (f : E → ℂ) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (x : E) :
    test b x (PowerSeries.coeff k (JetC b f))=
      (k.factorial:ℂ)⁻¹ * iteratedDeriv k (fun t : ℝ=>f (t • x)) 0 := by
  let L:ℝ→L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  rw [jet_value]; congr 1; rw [iteratedDeriv_eq_iteratedFDeriv]
  change _= iteratedFDeriv ℝ k (f ∘ L) 0 _; rw [jets_at L f (map_zero _) hf]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,L]

lemma jet_add {f g : E→ℂ} (hf : ContDiffAt ℝ ⊤ f 0) (hg : ContDiffAt ℝ ⊤ g 0) :
    JetC b (f+g)= JetC b f + JetC b g := by
  ext1 k; apply using_test b; intro x
  rw [_root_.map_add, _root_.map_add, jet_value, iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top), jet_value,jet_value]; simp [mul_add]

lemma jet_smul {f : E→ℂ} (hf : ContDiffAt ℝ ⊤ f 0) (a : ℂ) :
    JetC b (a • f) = PowerSeries.C (C a) * JetC b f := by
  ext1 k; apply using_test b; intro x
  rw [PowerSeries.coeff_C_mul,_root_.map_mul,jet_value,jet_value,iteratedFDeriv_const_smul_apply (hf.of_le le_top)]
  simp only [test, aeval_C, Algebra.algebraMap_self_apply,_root_.smul_apply,smul_eq_mul]; ring

lemma jet_mul {f g : E→ℂ} (hf : ContDiffAt ℝ ⊤ f 0) (hg : ContDiffAt ℝ ⊤ g 0) :
    JetC b (f*g)= JetC b f * JetC b g := by
  ext1 k; apply using_test b; intro x
  let F (f : E → ℂ) (t : ℝ):= f (t • x)
  have he (l : E → ℂ) (hl : ContDiffAt ℝ ⊤ l 0) (k : ℕ) :
      test b x (PowerSeries.coeff k (JetC b l)) =(k.factorial:ℂ)⁻¹ * iteratedDeriv k (F l) 0 := jet_ray b l k (hl.of_le le_top) x
  have hm (l : E → ℂ) (hl : ContDiffAt ℝ ⊤ l 0) : ContDiffAt ℝ k (F l) 0 := by
    apply ContDiffAt.comp (f:=fun t : ℝ=>t • x) _ _ (by fun_prop)
    rw [zero_smul]; exact hl.of_le le_top
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, _root_.map_sum, he (f*g) (hf.mul hg),show F (f*g)= F f * F g from rfl, iteratedDeriv_mul (hm f hf) (hm g hg),Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [_root_.map_mul, he f hf, he g hg]
  have hz : (↑(k.choose j):ℂ)*(j.factorial:ℕ)*(↑((k-j).factorial):ℂ)=(k.factorial:ℕ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    _ = ((k.factorial:ℂ)⁻¹ * ((k.choose j):ℂ))*iteratedDeriv j (F f) 0 * iteratedDeriv (k-j) (F g) 0 := by ring
    _ = _ := by
      have hh : (k.factorial:ℂ)⁻¹ * (k.choose j:ℂ)=(j.factorial:ℂ)⁻¹ * ((k-j).factorial:ℂ)⁻¹ := by field_simp [Nat.factorial_ne_zero]; linear_combination hz
      rw [hh]; ring

lemma jet_C (a : ℂ) : JetC b (fun _=>a)=PowerSeries.C (C a) := by
  ext1 k; apply using_test b; intro x
  rw [jet_value]; cases k <;> simp [test,iteratedFDeriv_const_of_ne]

end YM.XSpace.Formal
