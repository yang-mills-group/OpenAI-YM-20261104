import YM.FiniteVolumeClosure.A0bOriginals.Hessian
import YM.XSpace.Wick
import YM.LocalH.Haar
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Feynman rules at the flat saddle, before cutoff removal

All-order *finite regulator* bare lattice perturbation theory. Real
coefficients, extend external labels complex-multilinearly when needed.
Uses the physical Haar factors before Taylor extraction and divides by the
common vacuum series. `leg_rule` is ordinary Wick pairing: single coordinate
leg contraction recurses with multiplicity (pderiv). This is not a
convergence claim as the regulator is removed, nor yet a choice of
position renormalization / coupling. This construction doesn't use a
single exact Wilson correlation kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius Matrix InnerProductSpace BigOperators ContDiff

section Poly
open MvPolynomial Gauss
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (b : Module.Basis ι ℝ E)

def taylor (f : E → ℝ) (n : ℕ) : P ι :=
  (n.factorial : ℝ)⁻¹ • ∑ k : Fin n → ι, C (iteratedFDeriv ℝ n f 0 (fun i=> b (k i))) * ∏ i : Fin n,X (k i)

lemma taylor_read (f : E → ℝ) (n : ℕ) (x : E) : aeval (b.equivFun x) (taylor b f n) =
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _ => x) := by
  classical
  unfold taylor; simp only [map_smul,map_sum,map_mul,map_prod,aeval_C,aeval_X,smul_eq_mul, Algebra.algebraMap_self_apply]
  congr 1
  let F := iteratedFDeriv ℝ n f 0
  symm
  have he := F.map_sum (fun (_ : Fin n) (i : ι) => b.repr x i • b i)
  simpa only [b.sum_repr, Module.Basis.equivFun_apply, F.map_smul_univ (fun _=>_) (fun _=>_), smul_eq_mul,F, mul_comm] using he -- inspect
end Poly

/-- coefficient of exp(positive-order vertices), by finite sum over insertions -/
def formalExp {S : Type*} [CommSemiring S] [Algebra ℝ S] (p : PowerSeries S) :=
  PowerSeries.mk fun k=> ∑ j ∈ Finset.range (k+1), (j.factorial : ℝ)⁻¹ • PowerSeries.coeff k (p^j)

@[simp] lemma formalExp_cc {S : Type*} [CommSemiring S] [Algebra ℝ S] (p : PowerSeries S) : PowerSeries.constantCoeff (formalExp p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [formalExp]

namespace Regulator.Tree
open Gauss Precision
variable {R : Regulator} (T : R.Tree) (G : Gauge)
abbrev Idx := Fin (Module.finrank ℝ (T.Array G))
def basisT := Module.finBasis ℝ (T.Array G)

def precision : Matrix (T.Idx G) (T.Idx G) ℝ := Matrix.of fun i j=>
  iteratedFDeriv ℝ 2 T.action 0 ![T.basisT G i, T.basisT G j]

lemma precision_Q (v w : T.Idx G → ℝ) : v ⬝ᵥ (T.precision G *ᵥ w) =
    let e := (T.basisT G).equivFun.symm; T.Q G (e v) (e w) := by
  let b := T.basisT G
  rw [← T.flat_hessian.2.2]
  change _ = iteratedFDeriv ℝ 2 T.action 0 ![b.equivFun.symm v, b.equivFun.symm w]
  rw [b.equivFun_symm_apply,b.equivFun_symm_apply]
  simp only [precision, b, Matrix.mulVec, dotProduct, Matrix.of_apply,iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_sum,map_smul, sum_apply, smul_apply,Finset.mul_sum,smul_eq_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=>?_ ; ring

lemma precision_pos : (T.precision G).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j; simp only [precision,Matrix.conjTranspose_apply,Matrix.of_apply,star_trivial,T.flat_hessian.2.2]; unfold Q; apply congr_arg (·/2); exact Finset.sum_congr rfl fun k _=> real_inner_comm ..
  intro v hv; rw [star_trivial,precision_Q]; exact T.definite _ (fun h=>hv ((T.basisT G).equivFun.symm.injective (h.trans (map_zero _).symm)))

def covariance := (T.precision G)⁻¹
lemma covariance_pos : (T.covariance G).PosDef := (T.precision_pos G).inv
lemma covariance_symm : (T.covariance G).IsSymm := by
  have he := (T.covariance_pos G).isHermitian
  ext i j; exact congr_fun (congr_fun he i) j

abbrev Poly := P (T.Idx G)
/-- Coupling variable here is the common bare `g_N`. -/
abbrev Bare := PowerSeries (T.Poly G)

def rule := wick (T.covariance G) (T.covariance_symm G)

theorem leg_rule (p : T.Poly G) (i : T.Idx G) :
    T.rule G (p*MvPolynomial.X i) = ∑ j:T.Idx G,T.covariance G i j*T.rule G (Partial j p) := wick_mul_X ..

-- raw Taylor coefficients; use smooth fields or shifted nonnegative series.
def mark (F : R.Configuration G → ℝ) : T.Bare G := PowerSeries.mk (taylor (T.basisT G) (F ∘ T.expLinks))

def vertices : T.Bare G := PowerSeries.mk fun n=> if n=0 then 0 else - taylor (T.basisT G) T.action (n+2)

def patch (G : Gauge) := (YM.LocalH.actual G).choose
lemma patch_live : LocalRatio (patch G) := (YM.LocalH.actual G).choose_spec

def relativeHaar (A : T.Array G) := ∏ l:T.Mobile,(patch G).J (A l)
lemma uses_haar : ContDiffAt ℝ ω (T.relativeHaar G) 0 := by
  unfold relativeHaar; generalize (Finset.univ : Finset T.Mobile)=s
  classical
  induction s using Finset.induction with
  | empty=> simp; exact contDiffAt_const
  | insert l s hs ih=>
    simp_rw [Finset.prod_insert hs]; apply ContDiffAt.mul _ ih
    exact ContDiffAt.comp (g:=(patch G).J) (f:=fun a:T.Array G=>a l) _ ((patch_live _).germ 0 (Metric.mem_ball_self (patch_live _).patch)) (contDiffAt_apply ..)

def jacobi : T.Bare G := PowerSeries.mk (taylor (T.basisT G) (T.relativeHaar G))

def weight : T.Bare G := T.jacobi G * formalExp (T.vertices G)

lemma weight_zero : PowerSeries.constantCoeff (T.weight G)=1 := by
  simp only [weight, map_mul, formalExp_cc,mul_one]
  rw [jacobi,← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  apply MvPolynomial.funext; intro x
  obtain ⟨v,rfl⟩ := (T.basisT G).equivFun.surjective x
  rw [← MvPolynomial.aeval_eq_eval,taylor_read]
  simp [relativeHaar,(patch_live _).anchored]

def terms (p : T.Bare G) : PowerSeries ℝ := PowerSeries.mk fun k => T.rule G (PowerSeries.coeff k p)
lemma terms_cc (p : T.Bare G) : PowerSeries.constantCoeff (T.terms G p) = T.rule G (PowerSeries.constantCoeff p) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,terms,PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply]

def vacuum : PowerSeries ℝ := T.terms G (T.weight G)

@[simp] lemma vacuum_zero : PowerSeries.constantCoeff (T.vacuum G)=1 := by
  rw [vacuum,terms_cc,weight_zero,rule]; exact wick_one ..

def diagrams (p : T.Bare G) := (T.terms G (p * T.weight G)) * (T.vacuum G)⁻¹

theorem normalized (p : T.Bare G) : T.diagrams G p * T.vacuum G=T.terms G (p * T.weight G) := by
  rw [diagrams, mul_assoc, PowerSeries.inv_mul_cancel, mul_one]; simp

@[simp] lemma diagrams_one : T.diagrams G 1=1 := by rw [diagrams, one_mul]; exact PowerSeries.mul_inv_cancel (T.vacuum G) (by rw [vacuum_zero]; exact one_ne_zero)

lemma leading (p : T.Bare G) : PowerSeries.constantCoeff (T.diagrams G p) = T.rule G (PowerSeries.constantCoeff p) := by
  simpa only [map_mul,vacuum_zero,mul_one,terms_cc,weight_zero] using
    congrArg PowerSeries.constantCoeff (T.normalized G p)
end Regulator.Tree
end YM.XSpace
