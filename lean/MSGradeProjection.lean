import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import FormalConversion

/-! Componentwise projections onto the engineering weights of gauge-invariant
curvature polynomials. A gauge rotation acts separately on each jet order, so
it commutes with the weighted dilation of a tower. Comparing coefficients of
the dilation parameter shows that each component remains gauge invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section

namespace YangMills.Matching.Grade
open Set
open scoped BigOperators Classical

variable {g : GaugeGroup}

private def ray (B : Maxwell.Coordinates g) (A : B.Tower) (p : B.Pol) : Polynomial ℂ :=
  MvPolynomial.aeval (fun i : B.Key =>
    Polynomial.C (((B.basis i.1).repr (A i.1) i.2 : ℝ) : ℂ) *
      Polynomial.X ^ (i.1 + 2)) p

private theorem rayEval (B : Maxwell.Coordinates g) (A : B.Tower) (p : B.Pol) (t : ℝ) :
    (ray B A p).eval (t : ℂ) = B.eval (fun j => (t ^ (j+2)) • A j) p := by
  let z (i : B.Key) : Polynomial ℂ :=
    Polynomial.C (((B.basis i.1).repr (A i.1) i.2 : ℝ) : ℂ) * Polynomial.X ^ (i.1+2)
  have h :
      (Polynomial.aeval (t : ℂ)).comp (MvPolynomial.aeval z) =
        B.eval (fun j => (t ^ (j+2)) • A j) := by
    ext i : 1
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, Maxwell.Coordinates.eval, MvPolynomial.aeval_X]
    dsimp only [z]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_pow]
    exact mul_comm _ _
  exact DFunLike.congr_fun h p

private theorem rayInvariant (B : Maxwell.Coordinates g) (d : ℕ) (p : B.Pol)
    (hp : B.Admissible d p) (u : g.image) (A : B.Tower) :
    ray B (fun j => B.rotate u j (A j)) p = ray B A p := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine (infinite_range_of_injective Complex.ofReal_injective).mono ?_
  rintro _ ⟨t, rfl⟩
  change Polynomial.eval (t : ℂ) (_ - _) = 0
  rw [Polynomial.eval_sub, rayEval, rayEval]
  apply sub_eq_zero.mpr
  simpa only [map_smul] using hp.2 u (fun j => (t ^ (j+2)) • A j)

private theorem coeffRay {σ : Type*} (w : σ → ℕ) (z : σ → ℂ) (h : ℕ)
    (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (z i) * Polynomial.X ^ w i) p).coeff h =
      MvPolynomial.aeval z (MvPolynomial.weightedHomogeneousComponent w h p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial m a =>
    have hm := MvPolynomial.isWeightedHomogeneous_monomial w m a rfl
    have hprod : m.prod (fun i n => (Polynomial.C (z i) * Polynomial.X ^ w i) ^ n) =
        Polynomial.C (m.prod (fun i n => z i ^ n)) * Polynomial.X ^ Finsupp.weight w m := by
      simp only [Finsupp.prod, mul_pow, ← map_pow, ← pow_mul, Finset.prod_mul_distrib,
        ← map_prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum,
        nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
    rw [MvPolynomial.aeval_monomial, hprod]
    change (Polynomial.C a * (_ * _)).coeff h = _
    rw [← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    by_cases he : Finsupp.weight w m = h
    · subst h
      rw [hm.weightedHomogeneousComponent_same, MvPolynomial.aeval_monomial]
      simp
    · rw [hm.weightedHomogeneousComponent_ne h (Ne.symm he), map_zero]
      simp [he]

private theorem admissible_component (B : Maxwell.Coordinates g) (d h : ℕ) (p : B.Pol)
    (hp : B.Admissible d p) :
    B.Admissible d (MvPolynomial.weightedHomogeneousComponent (fun i : B.Key => i.1 + 2) h p) := by
  constructor
  · have hd := hp.1
    rw [MvPolynomial.mem_restrictSupport_iff] at hd ⊢
    intro m hm
    apply hd
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    simp [hz]
  · intro u A
    have eqn := congrArg (fun f : Polynomial ℂ => f.coeff h) (rayInvariant B d p hp u A)
    let w (i : B.Key) := i.1 + 2
    let z (V : B.Tower) (i : B.Key) := (((B.basis i.1).repr (V i.1) i.2 : ℝ) : ℂ)
    exact (coeffRay w (z (fun j => B.rotate u j (A j))) h p).symm.trans
      (eqn.trans (coeffRay w (z A) h p))

/-- The weight-`h` component of a field at cutoff `d`, in the same field space. -/
def project (B : Maxwell.Reference g) (d h : ℕ) : B.sector d →ₗ[ℂ] B.sector d :=
  ((MvPolynomial.weightedHomogeneousComponent (R := ℂ) (fun i : B.toCoordinates.Key => i.1 + 2) h).comp
    (B.sector d).subtype).codRestrict (B.sector d) (fun p =>
      (B.sector_iff d _).mpr (admissible_component B.toCoordinates d h p.val ((B.sector_iff d _).mp p.property)))

theorem project_val (B : Maxwell.Reference g) (d h : ℕ) (p : B.sector d) :
    (project B d h p).val =
      MvPolynomial.weightedHomogeneousComponent (fun i : B.toCoordinates.Key => i.1 + 2) h p.val := rfl

/-- The sum of the diagonal engineering-weight blocks of a field endomorphism. -/
def diagonal (B : Maxwell.Reference g) (d : ℕ) (T : B.sector d →ₗ[ℂ] B.sector d) :
    B.sector d →ₗ[ℂ] B.sector d :=
  ∑ i : Fin (d+1), (project B d i.val).comp (T.comp (project B d i.val))

attribute [local irreducible] project diagonal

theorem diagonal_preserves (B : Maxwell.Reference g) (d : ℕ) (T : B.sector d →ₗ[ℂ] B.sector d)
    (h : ℕ) (p : B.sector d) (hp : Homogeneous B h p.val) :
    Homogeneous B h (diagonal B d T p).val := by
  let w := fun i : B.toCoordinates.Key => i.1 + 2
  have hw : MvPolynomial.IsWeightedHomogeneous w p.val h :=
    fun {m} hm => hp m (MvPolynomial.mem_support_iff.mpr hm)
  have block (i : Fin (d+1)) : ((project B d i (T (project B d i p))).val)
      ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w h := by
    by_cases hi : (i : ℕ) = h
    · rw [hi, project_val]
      exact MvPolynomial.weightedHomogeneousComponent_mem w (T (project B d h p)).val h
    · have hz : project B d i p = 0 := by
        apply Subtype.ext
        change (project B d i p).val = 0
        rw [project_val]
        exact hw.weightedHomogeneousComponent_ne i.val hi
      rw [hz, map_zero, map_zero]
      exact Submodule.zero_mem _
  have hsum : MvPolynomial.IsWeightedHomogeneous w (diagonal B d T p).val h := by
    change (diagonal B d T p).val ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w h
    simp only [diagonal, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_sum]
    exact Submodule.sum_mem _ (fun i _ => block i)
  exact fun m hm => hsum (MvPolynomial.mem_support_iff.mp hm)


theorem diagonal_id (B : Maxwell.Reference g) (d : ℕ) :
    diagonal B d LinearMap.id = LinearMap.id := by
  ext1 p
  apply Subtype.ext
  ext1 m
  let w := fun i : B.toCoordinates.Key => i.1 + 2
  change (diagonal B d LinearMap.id p).val.coeff m = p.val.coeff m
  simp only [diagonal, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_sum, MvPolynomial.coeff_sum, project_val,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hm : p.val.coeff m = 0
  · simp [hm]
  have hs := ((B.sector_iff d _).mp p.property).1
  rw [MvPolynomial.mem_restrictSupport_iff] at hs
  have hd : Finsupp.weight w m ≤ d :=
    hs (MvPolynomial.mem_support_iff.mpr hm)
  let i : Fin (d+1) := ⟨Finsupp.weight w m, Nat.lt_succ_of_le hd⟩
  rw [Finset.sum_eq_single i]
  · simp [i, w]
  · intro j _ hj
    have hne : Finsupp.weight w m ≠ j.val := fun e => hj (Fin.ext e.symm)
    simp [w] at hne
    simp [hne]
  · simp

end YangMills.Matching.Grade
