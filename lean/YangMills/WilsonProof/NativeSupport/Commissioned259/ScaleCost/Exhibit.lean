import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Capital
/-! # Basis estimates for G.2 of the proof: column tariff then determinant tariff

Iteration on **real lengths**, not along an extraction or a moving family
of physical regulators. Norm prices only. Used to get polylog scope under G.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Set Function Asymptotics MeasureTheory PowerSeries Matrix
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land Register FVA2.Scale
open XSpace XSpace.Normalize O.Score O.Enh Dframe Comparing
open scoped Topology Classical BigOperators Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ}
    {B : ℝ→Frames G} {D : Route G}
    {d : ℕ} (hG : G.Simple)

abbrev tallyZ {I : Type*} [Fintype I] (v : I→ℂ) := ∑ i, ‖v i‖
private lemma tallyPos {I : Type*} [Fintype I] (v : I→ℂ) : 0 ≤ tallyZ v := Finset.sum_nonneg fun i _=>norm_nonneg _
lemma capacity (A : Operator G d) (v : Toon G d→ℂ) : tallyZ (A *ᵥ v) ≤ stiffness A*tallyZ v := by
  unfold stiffness tallyZ; rw [ Finset.sum_mul ]; refine Finset.sum_le_sum fun i _=>?_ ; unfold Matrix.mulVec dotProduct
  refine (norm_sum_le ..).trans ?_; rw [ Finset.sum_mul ]; exact Finset.sum_le_sum fun j _=> (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun k _=> norm_nonneg (v k)) (Finset.mem_univ j)) (norm_nonneg _))
lemma master {s : ℝ} (hp : 1 ≤ s) (v : Toon G d→ℂ) : tallyZ (engine G d (-Real.log s) *ᵥ v) ≤ s^d*tallyZ v := by
  have e := zero_lt_one.trans_le hp; unfold tallyZ; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_
  simp only [Matrix.mulVec,dotProduct, gear_cost,neg_neg,ite_mul,zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ,if_true,norm_mul,Real.exp_log e,Complex.norm_real,norm_pow,Real.norm_of_nonneg e.le]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp (size_le i)) (norm_nonneg _)
lemma keeping (A U : Operator G d) (v : Toon G d→ℂ) : tallyZ (A *ᵥ v) ≤ stiffness (A-U)*tallyZ v + tallyZ (U *ᵥ v) := by
  have e:A *ᵥ v= (A-U)*ᵥ v+U *ᵥ v:=by rw [Matrix.sub_mulVec, sub_add_cancel];
  refine e ▸ (le_trans ?_ (add_le_add (capacity (A-U) v) le_rfl))
  unfold tallyZ; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=> norm_add_le _ _
include hG
lemma safe (v : ℝ→Toon G d→ℂ) (h : Law V R B)
    (t : ℝ→ℝ) (hz : ∀ s:ℝ, coeff 1 (B s d)=0) (field : FieldQuote G B t D d 1)
    (he : ∀ᶠ r in late, ∀ T ≥ 1, T ≤ 2 → v r=actual D d r T *ᵥ v (r*T)) :
    Income (fun r=>r^d*tallyZ (v r)) := by
  obtain ⟨C,hC,H⟩:= fare_quadratic h hz field
  apply log_growth hG _ C hC.le
  filter_upwards [H,he,self_mem_nhdsWithin] with r h E u
  intro T hT hv; change 0 < r at u; have hi:=zero_lt_one.trans_le hT
  let z:=v (r*T); let Q:=tallyZ z; have hQ :=tallyPos z; let S:=C*g0 G r^2; have hS : 0 ≤ S:=by positivity
  have m : tallyZ (v r) ≤ (1+S)*(T^d*Q) := by
    rw [E T hT hv]; calc
      _ ≤ stiffness (actual D d r T-engine G d (-Real.log T))*Q+tallyZ (engine G d (-Real.log T)*ᵥ z) := keeping ..
      _ ≤ S*Q + T^d*Q := add_le_add (mul_le_mul_of_nonneg_right (h T hT hv) hQ) (master hT z)
      _ ≤ S*(T^d*Q)+T^d*Q := add_le_add (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hQ (one_le_pow₀ hT)) hS) le_rfl
      _ = _ := by ring
  have u' : 0 ≤ tallyZ (v r) := tallyPos _
  rw [ Real.norm_of_nonneg (mul_nonneg (pow_nonneg u.le _) u'), Real.norm_of_nonneg (mul_nonneg (pow_nonneg (mul_pos u hi).le _) hQ) ]
  change r^d*tallyZ (v r) ≤ (1+S)*(_*Q); exact (mul_le_mul_of_nonneg_left m (pow_nonneg u.le _)).trans_eq (by rw [mul_pow]; ring)

-- choose an ANCHOR f, but no assumption that it varies with r. account uses same phase & fields maps D.
def value (D : Route G) (d : ℕ) (f r : ℝ) : Operator G d := columns (D r f d)*engine G d (-Real.log r)
omit hG
lemma value_steps (h : Balances D) (f : ℝ) {r T : ℝ} (hr : 0 < r) (hT : 0 < T) : value D d f r=actual D d r T*value D d f (r*T)*engine G d (Real.log T) := by
  unfold value; rw [mul_assoc, mul_assoc, forward, actual, ← mul_assoc, composition' (D r (r*T) d) (D (r*T) f d), Real.log_mul hr.ne' hT.ne', neg_add]
  rw [show -Real.log r + -Real.log T + Real.log T= -Real.log r by ring,show D r (r*T) d ∘ₗ D (r*T) f d= D r f d from (h ..).symm]

-- adjust determinant controls over subdyadic steps using the explicit finite polynomial with Fare(T=1)
private lemma change_fee {I : Type*} {X : Filter I} {A : I→Operator G d} {w:I→ℝ} (hw : Tendsto w X (𝓝 0))
    (h : ∀ i j,(fun k=> (A k-1) i j)=O[X] w) : (fun i=> Matrix.det (A i)-1)=O[X] w := by
  let T:I→ℝ:=fun _=>1; have ht : ∀ᶠ i in X, 1 ≤ T i := Eventually.of_forall fun _=>le_rfl
  let B:Operator G d:=1
  have hh (i j) : Fare T X (fun _=>1) (fun k => A k i j) := Fare.bare (isBigO_const_of_tendsto
    (show Tendsto _ X (𝓝 (B i j)) from Tendsto.congr (fun k=>sub_add_cancel (A k i j) (B i j)) (by simpa only [Matrix.sub_apply,B,zero_add] using ( ( h i j ).trans_tendsto hw ).add (tendsto_const_nhds (x:=B i j)) )) one_ne_zero)
  have s : Fare T X w (fun i=> Matrix.det (A i)-Matrix.det B) := by
    simp_rw [Matrix.det_apply', ← Finset.sum_sub_distrib, ← mul_sub]
    refine Fare.sum ht fun i _=> Fare.cover (Fare.constant _) ?_
    refine (Fare.overall (g:=w) ht (fun j _=>hh _ _) (fun j _=> Fare.constant _) (fun j _=>?_) ).extend ?_
    ·
      refine (Fare.bare (h (i j) j)).extend ?_; exact Eventually.of_forall fun i=>(mul_one _).symm
    exact Eventually.of_forall fun i=>by simp
  obtain ⟨k,h⟩:=s; simpa [B,T,logs] using h
include hG
lemma tax (h : Law V R B) (t : ℝ→ℝ) (hz : ∀ s:ℝ, coeff 1 (B s d)=0)
    (field : FieldQuote G B t D d 1) : ∃ C : ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ 1, T ≤ 2 →
    ‖det (actual D d r T * engine G d (Real.log T))-1‖ ≤ C*g0 G r^2 := by
  obtain ⟨C,hC,H⟩:= fare_quadratic h hz field
  let I:= {i:ℝ×ℝ // 1 ≤ i.2 ∧ i.2 ≤ 2}; let r(i:I):=i.val.1; let T (i:I):= i.val.2; let X:=comap r late
  let F i:=actual D d (r i) (T i); let A i:= engine G d (Real.log (T i)); let E i:= engine G d (-Real.log (T i))
  let q (i:I):=g0 G (r i)^2
  have v (i : I) := i.property.1
  have u : (fun i=> stiffness (F i-E i))=O[X] q := by
    refine IsBigO.of_bound C ?_
    filter_upwards [(show Tendsto r X late from tendsto_comap).eventually H] with i z; rw [Real.norm_of_nonneg (stiffPos _),Real.norm_of_nonneg (show 0 ≤ q i by unfold q; positivity)]; exact z _ (v i) i.property.2
  have hQ : Tendsto q X (𝓝 0) := by simpa only [X,q,Function.comp_def,zero_pow (by norm_num : (2:ℕ)≠0)] using (((g0_zero hG).comp (tendsto_comap (f:=r))).pow 2)
  have hp : (stiffness ∘ A)=O[X] fun i=> (1:ℝ) := by
    refine matrixPay.mpr fun i j=> IsBigO.of_bound' ?_
    filter_upwards with k; have v : 1 ≤ T k := v k; have hp := zero_lt_one.trans_le v; unfold A; rw [gear_cost, norm_one]; split_ifs
    · rw [Complex.norm_real,Real.exp_neg,Real.exp_log hp,norm_pow,norm_inv,Real.norm_of_nonneg hp.le]; exact pow_le_one₀ (by positivity) ((inv_le_one₀ hp).mpr v)
    rw [norm_zero]; norm_num
  obtain ⟨K,hK,V⟩ : ∃ c > 0, IsBigOWith c X (fun i=>Matrix.det (F i*A i) -1) q := by
    apply IsBigO.exists_pos (change_fee hQ ?_)
    intro i j
    have he (k : I) : F k*A k-1=(F k-E k)*A k := by rw [sub_mul]; unfold E A; rw [forward,neg_add_cancel, origin]
    simp_rw [he, Matrix.mul_apply]
    exact IsBigO.sum fun l _=> ((matrixPay.mp u i l).mul (matrixPay.mp hp l j)).congr_right (fun _=>mul_one _)
  refine ⟨K,hK,(eventually_comap.mp V.bound).mono ?_⟩
  intro r h T ht hl; have i := h (⟨(r,T),ht,hl⟩:I) rfl
  exact i.trans_eq (congr_arg (_ * ·) (Real.norm_of_nonneg (by unfold q; positivity)))
lemma determinant (f : ℝ) (hD : Balances D) (h : Law V R B) (t : ℝ→ℝ) (hz : ∀ s:ℝ, coeff 1 (B s d)=0)
    (field : FieldQuote G B t D d 1) : Income (fun r=> ‖(det (value D d f r))⁻¹‖) := by
  obtain ⟨C,hC,H⟩:= tax hG h t hz field
  have h0 : Tendsto (fun i=>C*g0 G i^2) late (𝓝 0) := by simpa only [zero_pow (by norm_num : (2:ℕ)≠0), mul_zero] using ((g0_zero hG).pow 2).const_mul C
  refine log_growth hG _ (2*C) (by positivity) ?_
  filter_upwards [H,h0.eventually_lt_const (by norm_num : (0:ℝ)<1/2),self_mem_nhdsWithin] with r h t' hr T ht l
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
  let K:=det (actual D d r T*engine G d (Real.log T)); let u:= C*g0 G r^2; have hu : 0 ≤ u := by positivity
  have i := h T ht l
  change ‖K-1‖≤u at i; change u<1/2 at t'
  have z : 1-u ≤ ‖K‖ := by linarith [show 1-‖K‖≤‖K-1‖ by rw [norm_sub_rev,← norm_one (α:=ℂ)]; exact norm_sub_norm_le .. ]
  have p : 0 < 1-u := by linarith
  have w : ‖K⁻¹‖≤1+2*u := by
    rw [norm_inv]; apply (inv_anti₀ p z).trans; rw [inv_le_comm₀ p (by positivity)]
    rw [← one_div, div_le_iff₀ (by positivity)]; nlinarith
  have he : det (value D d f r)=det (value D d f (r*T)) * K := by rw [value_steps hD f hr (zero_lt_one.trans_le ht),det_mul,det_mul]; unfold K; rw [det_mul]; ring
  rw [he,_root_.mul_inv_rev,norm_mul,show (2*C)*g0 G r^2=2*u from mul_assoc ..]
  exact mul_le_mul_of_nonneg_right w (norm_nonneg _)
end YM.FVA2.GradedFar259.ScaleCost
