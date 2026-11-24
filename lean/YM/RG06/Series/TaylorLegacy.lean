import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Operator Taylor convention

Ordinary (factorial divided), at zero, over the reals, to apply directly to
stencils on real matrix Lie colors. `Nat → R` notation allows also the
noncommutative holonomy products (always **left to right**). No assertion
about the regulator-dependent density, convergence in coupling, or exchanging
limits with derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Series
open Function NormedSpace
open scoped Topology BigOperators ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A test function's coefficients; independent stencil series are defined
**separately** by local rules (exponential letter coefficients, products,
and linear combinations). -/
def tcoeff (f : ℝ → E) (n : ℕ) : E :=
  (n.factorial : ℝ)⁻¹ • iteratedDeriv n f 0

@[simp] theorem tcoeff_zero (f : ℝ → E) : tcoeff f 0 = f 0 := by simp [tcoeff]

@[simp] theorem tcoeff_one (f : ℝ → E) : tcoeff f 1 = deriv f 0 := by simp [tcoeff]

theorem iterated_from_tcoeff (f : ℝ → E) (n : ℕ) :
    iteratedDeriv n f 0 = (n.factorial : ℝ) • tcoeff f n := by
  rw [tcoeff, smul_inv_smul₀ (show (n.factorial : ℝ) ≠ 0 by positivity)]

@[simp] theorem tcoeff_const (c : E) (n : ℕ) :
    tcoeff (fun _ : ℝ => c) n = if n = 0 then c else 0 := by
  cases n <;> simp [tcoeff,iteratedDeriv_const]

@[simp] theorem tcoeff_zero_fun (n : ℕ) : tcoeff (fun _ : ℝ => (0:E)) n = 0 := by simp

theorem tcoeff_add {f g : ℝ → E} (n : ℕ)
    (hf : ContDiffAt ℝ (n:ℕ) f 0) (hg : ContDiffAt ℝ (n:ℕ) g 0) :
    tcoeff (fun t => f t + g t) n = tcoeff f n + tcoeff g n := by
  simp only [tcoeff,iteratedDeriv_fun_add (f:=f) (g:=g) hf hg,smul_add]

theorem tcoeff_sum {I : Type*} (s : Finset I) (f : I → ℝ → E) (n : ℕ)
    (hf : ∀ i∈s,ContDiffAt ℝ (n:ℕ) (f i) 0) :
    tcoeff (fun t => ∑ i∈s,f i t) n = ∑ i∈s,tcoeff (f i) n := by
  rw [tcoeff,iteratedDeriv_fun_sum hf,Finset.smul_sum]; rfl

@[simp] theorem tcoeff_neg (f : ℝ → E) (n : ℕ) :
    tcoeff (fun t=> -f t) n = -tcoeff f n := by simp [tcoeff]

theorem tcoeff_sub {f g : ℝ → E} (n : ℕ)
    (hf : ContDiffAt ℝ (n:ℕ) f 0) (hg : ContDiffAt ℝ (n:ℕ) g 0) :
    tcoeff (fun t=> f t - g t) n = tcoeff f n - tcoeff g n := by
  simp_rw [sub_eq_add_neg]; rw [tcoeff_add (f:=f) (g:=fun t=> -g t) _ hf (ContDiffAt.neg hg), tcoeff_neg]

@[simp] theorem tcoeff_smul_real (c : ℝ) (f : ℝ → E) (n : ℕ) :
    tcoeff (fun t=> c • f t) n = c • tcoeff f n := by
  simp only [tcoeff,iteratedDeriv_fun_const_smul_field,smul_comm c]

lemma tcoeff_clm (L : E →L[ℝ] F) {f : ℝ → E} (n : ℕ) (hf : ContDiffAt ℝ (n:ℕ) f 0) :
    tcoeff (fun t => L (f t)) n = L (tcoeff f n) := by
  simp only [tcoeff,L.map_smul]; apply congrArg
  have he : (fun t => L (f t))=L ∘ f := rfl
  simp only [he,iteratedDeriv_eq_iteratedFDeriv,ContinuousLinearMap.iteratedFDeriv_comp_left L (f:=f) hf le_rfl]; rfl

lemma tcoeff_linear [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] F) {f : ℝ → E} (n : ℕ) (hf : ContDiffAt ℝ (n:ℕ) f 0) :
    tcoeff (fun t => L (f t)) n = L (tcoeff f n) := by
  -- prefer explicit rewrite
  simpa only [LinearMap.coe_toContinuousLinearMap'] using!
    (tcoeff_clm (LinearMap.toContinuousLinearMap L) n hf)

section R
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def conv (f g : ℕ → R) (n : ℕ) := ∑ i∈Finset.range (n+1), f i * g (n-i)

lemma cast_mul (n : ℕ) (x : R) : (n:R) * x = (n:ℝ) • x := by
  rw [Algebra.smul_def]; simp

lemma factorial_choose (n i : ℕ) (hi : i ≤ n) :
    (n.factorial : ℝ)⁻¹ * (n.choose i : ℝ) =
      (i.factorial : ℝ)⁻¹ * ((n-i).factorial : ℝ)⁻¹ := by
  have h : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n-i).factorial : ℝ) = (n.factorial : ℝ) :=
    mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp
  exact h

lemma tcoeff_mul {f g : ℝ → R} (n : ℕ)
    (hf : ContDiffAt ℝ (n:ℕ) f 0) (hg : ContDiffAt ℝ (n:ℕ) g 0) :
    tcoeff (fun t=> f t * g t) n = conv (tcoeff f) (tcoeff g) n := by
  simp only [tcoeff,conv,iteratedDeriv_fun_mul (f:=f) (g:=g) hf hg,Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [cast_mul,smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
    factorial_choose n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]

lemma tcoeff_list_prod (l : List (ℝ→R)) (n : ℕ)
    (h : ∀ f∈l,ContDiffAt ℝ (n:ℕ) f 0) :
    let oneJet := fun k : ℕ=> if k=0 then (1:R) else 0
    tcoeff (fun t => (l.map (fun f => f t)).prod) n = (l.map tcoeff).foldr conv oneJet n := by
  -- each multiplication uses coefficients indexed from zero up to n
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons,List.foldr_cons]
    rw [tcoeff_mul (f:=a) (g:=fun t=> (l.map (fun f=> f t)).prod) _ (h _ (by simp))]
    · apply Finset.sum_congr rfl fun i hi=>?_ -- reduce conv with delta
      have ge : (↑(n-i) : WithTop ℕ∞) ≤ (↑n:WithTop ℕ∞):= Nat.cast_le.mpr (Nat.sub_le n i)
      rw [ih (n-i) fun f hf=> (h f (List.mem_cons_of_mem _ hf)).of_le ge]
    suffices ∀ (l : List (ℝ→R)), (∀ f∈l, ContDiffAt ℝ (n:ℕ) f 0) →
        ContDiffAt ℝ (n:ℕ) (fun t=> (l.map (fun f=> f t)).prod) 0 by
      exact this l fun f hf=>h _ (by simp [hf])
    intro q
    induction q with
    | nil=> intro; simp; exact contDiffAt_const
    | cons a q hq=> intro h; simp only [List.map_cons,List.prod_cons]; exact (h a (by simp)).mul (hq fun f hf=>h _ (by simp [hf]))

variable [CompleteSpace R]
lemma exp_iters (a : R) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ=> exp (t • a)) = fun t=> exp (t • a) * a^n := by
  induction n with
  | zero=> simp
  | succ n ih=>
    ext1 t
    rw [iteratedDeriv_succ,ih]
    simpa only [mul_assoc, ← pow_succ'] using ((hasDerivAt_exp_smul_const a t).mul_const (a^n)).deriv

@[simp] lemma tcoeff_exp (a : R) (n : ℕ) :
    tcoeff (fun t : ℝ=> exp (t • a)) n = (n.factorial:ℝ)⁻¹ • a^n := by
  unfold tcoeff; rw [exp_iters]; dsimp only; simp
end R

section C
open PowerSeries
variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
def taylorSeries (f : ℝ→R) := PowerSeries.mk (R:=R) (tcoeff f)
@[simp] lemma taylorSeries_coeff (f : ℝ→R) (n) : coeff n (taylorSeries f)=tcoeff f n := by simp [taylorSeries]
@[simp] lemma taylorSeries_const (c : R) : taylorSeries (fun _=>c)=C c := by
  ext1 n;by_cases h : n=0 <;> simp [PowerSeries.coeff_C,h]

omit [NormedAlgebra ℝ R] in
lemma convolution_ps (p q : PowerSeries R) (n) :
    coeff n (p*q) = conv (fun i=> coeff i p) (fun i=> coeff i q) n := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> coeff i p * coeff j q) n]
  rfl

lemma taylorSeries_add {f g : ℝ→R} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    taylorSeries (fun t=>f t+g t)=taylorSeries f+taylorSeries g := by
  ext1 n
  have he : (n:WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (by exact le_top (a:=(n:ℕ∞)))
  simp only [taylorSeries_coeff,map_add,tcoeff_add n (hf.of_le he) (hg.of_le he)]

lemma taylorSeries_mul {f g : ℝ→R} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    taylorSeries (fun t=>f t*g t)=taylorSeries f*taylorSeries g := by
  ext1 n; have he : (n:WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (by exact le_top (a:=(n:ℕ∞)))
  simp only [convolution_ps,taylorSeries_coeff,tcoeff_mul n (hf.of_le he) (hg.of_le he)]
end C
end YM.RG06.Series
