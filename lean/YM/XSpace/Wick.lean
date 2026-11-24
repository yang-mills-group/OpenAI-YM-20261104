import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Algebraic finite-dimensional Wick calculus
`heat` is exp(1/2 C ∂∂) on polynomials. We show it's a finite operation and
verify the single-leg contraction rule. Computing diagram coefficients by it
therefore uses ordinary Wick pairing. Works equally well with formal changes
of finite cutoffs (no estimates on the Gaussian or actual Haar integral in
this file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gauss
open MvPolynomial Function Filter
open scoped BigOperators
abbrev P (ι : Type*) := MvPolynomial ι ℝ
variable {ι : Type*} [Fintype ι]
abbrev Partial (i : ι) : Module.End ℝ (P ι) := (pderiv i).toLinearMap

omit [Fintype ι] in
theorem partial_commute (i j : ι) (p : P ι) : Partial i (Partial j p) = Partial j (Partial i p) := by
  change pderiv i (pderiv j p)=pderiv j (pderiv i p)
  by_cases hh : i=j; · rw [hh]
  ext m
  classical
  simp [coeff_pderiv, Finsupp.single_eq_of_ne, hh, Ne.symm hh, add_comm (Finsupp.single i 1), add_assoc, mul_comm, mul_left_comm, mul_assoc]

variable (K : Matrix ι ι ℝ)
def lap : Module.End ℝ (P ι) := (1/2:ℝ) • ∑ i, ∑ j, K i j • ((Partial i).comp (Partial j))
def neighbor (i : ι) : Module.End ℝ (P ι) := ∑ j, K i j • Partial j

lemma partial_lap (i : ι) (p : P ι) : Partial i (lap K p) = lap K (Partial i p) := by
  simp only [lap,LinearMap.smul_apply,LinearMap.sum_apply, map_smul,map_sum, LinearMap.comp_apply]
  apply congr_arg
  refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> ?_
  rw [partial_commute i a,partial_commute i b]

lemma lap_mul_X (hk : K.IsSymm) (p : P ι) (i : ι) :
    lap K (p*X i) = lap K p*X i + neighbor K i p := by
  classical
  have hP (t : P ι) (i j : ι) : Partial i (t * X j) = Partial i t * X j + if i=j then t else 0 := by
    change pderiv i (t*X j) = _
    rw [pderiv_mul]; split <;> simp_all [Ne.symm]
  unfold lap neighbor
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,hP,map_add,apply_ite (Partial _),map_zero,smul_ite,smul_zero,smul_add]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,ite_true,smul_add]
  -- inspect
  simp_rw [smul_mul_assoc,Finset.sum_mul]
  simp only [← smul_mul_assoc, add_assoc]
  have he (j : ι) : K j i=K i j := hk.apply _ _
  simp_rw [he]
  rw [← add_smul]; norm_num

lemma next_lap (i : ι) (p : P ι) : neighbor K i (lap K p) = lap K (neighbor K i p) := by
  simp only [neighbor,LinearMap.sum_apply,LinearMap.smul_apply,partial_lap,map_sum,map_smul]

def contractions (p : P ι) : ℕ → P ι
| 0=>p
| i+1=>(i+1 : ℝ)⁻¹ • lap K (contractions p i)

lemma contractions_mul (hk : K.IsSymm) (p : P ι) (i : ι) (k : ℕ) :
    contractions K (p*X i) (k+1) = contractions K p (k+1) * X i + neighbor K i (contractions K p k) := by
  induction k with
  | zero=> simp [contractions,lap_mul_X K hk]
  | succ k ih=>
    rw [contractions, ih, map_add, lap_mul_X K hk, ← next_lap]
    simp only [contractions, smul_add, smul_mul_assoc, map_smul]
    -- normalize scalars
    rw [add_assoc]; congr 1
    simp_rw [smul_smul]; rw [← add_smul]
    congr 1; push_cast; field_simp; ring

lemma contractions_kill (hk : K.IsSymm) (p : P ι) : ∀ᶠ k in atTop, contractions K p k=0 := by
  induction p using induction_on with
  | C x =>
    filter_upwards [eventually_ge_atTop 1] with k hk
    cases k
    · omega
    rename_i k
    induction k with
    | zero=> simp [contractions,lap]
    | succ k ih=> rw [contractions,ih (by omega),map_zero,smul_zero]
  | add p q hp hq=>
    filter_upwards [hp,hq] with k hp hq
    have he (j) : contractions K (p+q) j = contractions K p j + contractions K q j := by
      induction j with
      | zero=>rfl
      | succ j ih=> simp only [contractions, ih,map_add,smul_add]
    rw [he,hp,hq,add_zero]
  | mul_X p i hp=>
    obtain ⟨j,hj⟩:=eventually_atTop.mp hp
    filter_upwards [eventually_ge_atTop (j+1)] with k hk'
    cases k
    · omega
    rw [contractions_mul K hk,hj _ (by omega),hj _ (by omega)]; simp

lemma stationary (hk : K.IsSymm) (p : P ι) :
    ∃ q : P ι, ∀ᶠ k in atTop, ∑ l ∈ Finset.range k, contractions K p l=q := by
  obtain ⟨k,hk'⟩:=eventually_atTop.mp (contractions_kill K hk p)
  refine ⟨∑ l ∈ Finset.range k, contractions K p l, (eventually_ge_atTop k).mono fun j hj=>?_⟩
  exact Eq.symm (Finset.sum_subset (Finset.range_mono (show k≤j from hj)) (fun t _ ht=> hk' t (by simpa using ht)))

def heated (hk : K.IsSymm) (p : P ι) := (stationary K hk p).choose
lemma heated_spec (hk : K.IsSymm) (p : P ι) :
    ∀ᶠ k in atTop, ∑ l ∈ Finset.range k, contractions K p l = heated K hk p :=
  (stationary K hk p).choose_spec

def heat (hk : K.IsSymm) : Module.End ℝ (P ι) where
  toFun := heated K hk
  map_add' p q := by
    suffices he : ∀ᶠ k : ℕ in atTop, heated K hk (p+q) = heated K hk p + heated K hk q from he.exists.elim (fun _ h=>h)
    filter_upwards [heated_spec K hk p, heated_spec K hk q,heated_spec K hk (p+q)] with k hp hq ht
    rw [← ht,← hp,← hq,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _=>?_
    clear * - j p q K
    induction j with
    | zero=>rfl
    | succ j ih=>simp only [contractions,ih,map_add,smul_add]
  map_smul' c p := by
    suffices he : ∀ᶠ k : ℕ in atTop, heated K hk (c • p) = c • heated K hk p from he.exists.elim fun _ h=>h
    filter_upwards [heated_spec K hk p,heated_spec K hk (c • p)] with k hp ht
    rw [← ht,← hp,Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _=>?_
    clear * - j p c K
    induction j with
    | zero=>rfl
    | succ j ih=>rw [contractions, ih,map_smul,smul_comm,contractions]

lemma heat_spec (hk : K.IsSymm) (p : P ι) :
    ∀ᶠ k in atTop, ∑ l ∈ Finset.range k, contractions K p l = heat K hk p := heated_spec K hk p

lemma heat_mul_X (hk : K.IsSymm) (p : P ι) (i : ι) :
    heat K hk (p * X i) = heat K hk p * X i + neighbor K i (heat K hk p) := by
  have he (q : P ι) : ∀ᶠ k : ℕ in atTop, ∑ l ∈ Finset.range (k+1), contractions K q l = heat K hk q :=
    (tendsto_add_atTop_nat 1).eventually (heat_spec K hk q)
  suffices ∀ᶠ k : ℕ in atTop, heat K hk (p*X i)=heat K hk p*X i+neighbor K i (heat K hk p) from this.exists.elim fun _ h=>h
  filter_upwards [he p,he (p*X i),heat_spec K hk p] with k hp hx hy
  rw [← hx]; nth_rw 1 [← hp]; rw [← hy]
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (contractions K p)]
  simp_rw [contractions_mul K hk]; simp [contractions,Finset.sum_add_distrib,map_sum, add_mul,Finset.sum_mul,add_right_comm]

lemma heat_const (hk : K.IsSymm) (c : ℝ) : heat K hk (C c)=C c := by
  obtain ⟨k,hk',he⟩ := ((eventually_ge_atTop 1).and (heat_spec K hk (C c))).exists
  rw [← he,Finset.sum_eq_single 0]
  · rfl
  · rintro j hl h
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    induction j with
    | zero=> simp [contractions,lap]
    | succ j ih=> rw [contractions,ih (Finset.mem_range.mpr (lt_trans j.succ.lt_succ_self (Finset.mem_range.mp hl))) (by omega), map_zero,smul_zero]
  simp [show 0<k from hk']

lemma partial_heat (hk : K.IsSymm) (p : P ι) (i : ι) :
    Partial i (heat K hk p) = heat K hk (Partial i p) := by
  obtain ⟨k,hp,hq⟩:= ((heat_spec K hk p).and (heat_spec K hk (Partial i p))).exists
  rw [← hp,← hq,map_sum]; apply Finset.sum_congr rfl; intro l hl; clear hl
  induction l with
  | zero=>rfl
  | succ l ih=> rw [contractions,map_smul,partial_lap,ih,contractions]

def wick (hk : K.IsSymm) : P ι →ₗ[ℝ] ℝ := (aeval (R:=ℝ) (0:ι→ℝ)).toLinearMap.comp (heat K hk)
lemma wick_C (hk : K.IsSymm) (c : ℝ) : wick K hk (C c)=c := by simp [wick,heat_const]
lemma wick_one (hk : K.IsSymm) : wick K hk 1=1 := by simpa using wick_C K hk 1
lemma wick_mul_X (hk : K.IsSymm) (p : P ι) (i : ι) :
    wick K hk (p * X i) = ∑ j,K i j * wick K hk (Partial j p) := by
  simp [wick,heat_mul_X,neighbor,LinearMap.sum_apply,partial_heat,map_sum]
end YM.XSpace.Gauss
