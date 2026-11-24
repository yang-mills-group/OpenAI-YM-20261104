import YM.FiniteVolumeClosure.A0bOriginals.Bare

/-! # Parity of the regulated bare diagrams -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff
namespace Gauss
open MvPolynomial
variable {ι : Type*} [Fintype ι]

def reversal (ι : Type*) : P ι →ₐ[ℝ] P ι := aeval (-X)

@[simp] lemma reversal_X (i : ι) : reversal ι (X i) = - X i := by simp [reversal]
@[simp] lemma reversal_C (c : ℝ) : reversal ι (C c) = C c := by simp [reversal]

lemma partial_reversal (p : P ι) (i : ι) : Partial i (reversal ι p) = -reversal ι (Partial i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c=> simp
  | add p q hp hq=> simp only [map_add, hp, hq, neg_add_rev]; rw [add_comm]
  | mul_X p j h=>
    have he (q : P ι) : Partial i (q*X j) = Partial i q*X j+q * (if j=i then 1 else 0) := by
      change pderiv i (q*X j)=_
      rw [pderiv_mul]; split <;> simp_all [Ne.symm]
    simp [mul_neg,map_mul,map_add,map_neg, h, he, apply_ite (reversal ι)]

lemma wick_reversal (p : P ι) (K : Matrix ι ι ℝ) (hk : K.IsSymm) :
    wick K hk (reversal ι p)=wick K hk p := by
  have hl (p : P ι) : lap K (reversal ι p) = reversal ι (lap K p) := by
    simp only [lap, LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
      LinearMap.comp_apply,partial_reversal,map_neg,neg_neg]
  have he (p : P ι) (k : ℕ) : contractions K (reversal ι p) k = reversal ι (contractions K p k) := by
    induction k with
    | zero=>rfl
    | succ k ih=> simp only [contractions,ih,hl,map_smul]
  obtain ⟨k,hp,hr⟩:= ((heat_spec K hk p).and (heat_spec K hk (reversal ι p))).exists
  have hq (q : P ι) : aeval (0:ι → ℝ) (reversal ι q)=aeval (0:ι → ℝ) q := by
    induction q using induction_on with
    | C c=>simp
    | add p q h g=> simp only [map_add, h,g]
    | mul_X=> simp
  simp only [wick,LinearMap.comp_apply,hq]
  rw [← hp,← hr]
  simp [he,hq]
end Gauss

namespace Regulator.Tree
open Gauss
variable {R : Regulator} (T : R.Tree) (G : Gauge)

def twice : T.Bare G →+* T.Bare G :=
  (PowerSeries.map (reversal (T.Idx G)).toRingHom).comp (PowerSeries.rescale (-1))

lemma twice_coeff (p : T.Bare G) (k : ℕ) : PowerSeries.coeff k (T.twice G p) =
    ((-1:ℝ)^k) • (reversal _ (PowerSeries.coeff k p)) := by
  simp [twice, PowerSeries.coeff_map, PowerSeries.coeff_rescale,Algebra.smul_def]

lemma fixed_exp (p : T.Bare G) (h : T.twice G p=p) : T.twice G (formalExp p)=formalExp p := by
  ext1 k
  rw [twice_coeff,formalExp,PowerSeries.coeff_mk]
  simp only [map_smul,map_sum,Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [smul_comm,← twice_coeff,map_pow,h]

lemma row_sign (f : T.Array G → ℝ) (k : ℕ) : reversal (T.Idx G) (taylor (T.basisT G) f k)=
    ((-1:ℝ)^k) • (taylor (T.basisT G) f k) := by
  simp only [taylor,map_smul,map_sum,map_mul,map_prod,reversal_X,reversal_C]
  rw [smul_comm]; simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _=> ?_
  rw [Finset.prod_neg,Finset.card_univ,Fintype.card_fin]
  simp only [Algebra.smul_def,map_pow,map_neg,map_one]; rw [mul_left_comm (MvPolynomial.C _)]

theorem vertices_parity : T.twice G (T.vertices G)= T.vertices G := by
  ext1 k
  rw [twice_coeff,vertices]
  simp only [PowerSeries.coeff_mk]
  split
  · simp
  rw [map_neg,row_sign]
  simp [smul_smul, pow_add,← mul_pow]

lemma haar_parity : T.twice G (T.jacobi G)= T.jacobi G := by
  ext1 k
  rw [twice_coeff,jacobi]
  simp [row_sign,smul_smul,← mul_pow]

theorem weight_parity : T.twice G (T.weight G)= T.weight G := by
  rw [weight,map_mul,haar_parity,fixed_exp T G _ (T.vertices_parity G)]

lemma terms_parity (p : T.Bare G) : T.terms G (T.twice G p)=PowerSeries.rescale (-1) (T.terms G p) := by
  ext1 k
  simp [terms, twice_coeff,rule,wick_reversal,PowerSeries.coeff_rescale]

lemma diagrams_parity (p : T.Bare G) : T.diagrams G (T.twice G p)=PowerSeries.rescale (-1) (T.diagrams G p) := by
  have he : PowerSeries.rescale (-1) (T.vacuum G) = T.vacuum G := by rw [vacuum,← terms_parity,weight_parity]
  apply (IsUnit.mul_left_inj (PowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (PowerSeries.constantCoeff (T.vacuum G)) by rw [T.vacuum_zero]; exact isUnit_one))).mp
  rw [T.normalized]
  nth_rw 1 [← T.weight_parity G]
  rw [← map_mul,terms_parity,← he,← map_mul,T.normalized]
end Regulator.Tree
end YM.XSpace
