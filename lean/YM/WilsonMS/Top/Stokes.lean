import YM.WilsonMS.Top.Acyclic

/-!
# Which Wick computations satisfy integration by parts for the *free* BV differential?

Stay in `Raw`, so that the client can use this on the literal left-derivative
Feynman symbols in the repo. Recall View K uses covariance `2*K`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS
open MS MS.Koszul MS.Cylinder MS.Book MS.Swirl MS.Orbit MS.Orbit.Cog Finset

variable {A I : Type} [Fintype A] [Fintype I] {p : Sector A} {B : Bonded p I} {S F : Raw A ℂ}
  {K : Grain A}

/-- Weight of `D y ∘ D x` in the Laplacian. -/
def lapEntry (B : Bonded p I) (x y : A) : ℂ :=
  open Classical in ∑ i : I, if B.dual i = x ∧ B.plain i = y then B.fee i else 0

lemma lap_weights (U : A → A → ℂ) :
    ∑ i : I, B.fee i * U (B.dual i) (B.plain i) = ∑ x : A, ∑ y : A, lapEntry B x y * U x y := by
  classical
  have hx (i : I) :
    ∑ x : A, ∑ y : A, (if B.dual i = x ∧ B.plain i = y then B.fee i else 0) * U x y =
      B.fee i * U (B.dual i) (B.plain i) := by
    rw [Finset.sum_eq_single_of_mem (B.dual i) (by simp)]
    · rw [Finset.sum_eq_single_of_mem (B.plain i) (by simp), if_pos (by simp)]
      intro z _ hz
      rw [if_neg (fun t => hz t.2.symm), zero_mul]
    intro z _ hz
    exact Finset.sum_eq_zero (fun j _ => by rw [if_neg (fun t => hz t.1.symm), zero_mul])
  simp only [lapEntry, Finset.sum_mul]
  symm
  simp_rw [show
      ∀ x : A,
        (∑ y : A, ∑ i : I, (if B.dual i = x ∧ B.plain i = y then B.fee i else 0) * U x y) =
          ∑ i : I, ∑ y : A, (if B.dual i = x ∧ B.plain i = y then B.fee i else 0) * U x y
      from fun _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [hx]

lemma lap_view : View K (B.BV F) = ∑ x : A, ∑ y : A, lapEntry B x y * View K (D y (D x F)) := by
  rw [← lap_weights (B := B) (fun x y => View K (D y (D x F)))]
  simp only [Bonded.BV, loop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul, diffPair_apply]

omit [Fintype I] in
lemma one_leg (F : Raw A ℂ) (hr : Book.rank 1 F) : F = ∑ a : A, F [a] • atLetter a := by
  classical
  ext l
  rw [Finset.sum_apply]
  rcases l with _ | ⟨i, _ | s⟩
  · rw [hr [] (by simp)]
    symm
    exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
  · rw [Finset.sum_eq_single_of_mem i (by simp)]
    · rw [Pi.smul_apply, speaks]
      simp
    intro j _ hj
    rw [Pi.smul_apply, notNamed _ (Ne.symm hj), smul_zero]
  rw [hr _
      (by
        rw [mod_int]
        simp
        omega)]
  symm
  exact Finset.sum_eq_zero (fun _ _ => mul_zero _)

lemma deriv_view (h : Quadratic B S) (hc : Clear p K) (hk : Cog.Sym p K) (hf : Symm p F)
    (hL : F ∈ Mini A) :
    View K (classicalD B S F) =
      ∑ x : A, ∑ y : A, (∑ z : A, letterD B S x [z] * Chill K z y) * View K (D y (D x F)) := by
  classical
  rw [h.classical_vector, vectorField_eq, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  nth_rw 1 [one_leg _ (h.promotesField.rank i)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    ibpV _ hc hk (hf.drop i) (miD hL i), Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Low-rank Ward matrix. (An ordered, not necessarily graded-symmetric
matrix. Only its graded symmetrization counts.) -/
def ward (K : Grain A) (B : Bonded p I) (S : Raw A ℂ) (x y : A) : ℂ :=
  lapEntry B x y + ∑ z : A, letterD B S x [z] * Chill K z y

/-- Integration by parts on bounded-valence vertices; criterion on actual
propagator and the quadratic exponent. -/
lemma stokes (h : Quadratic B S) (hc : Clear p K) (hk : Cog.Sym p K)
    (hw : ∀ i j, ward K B S i j + cross (p i) (p j) * ward K B S j i = 0) (hf : Symm p F)
    (hL : F ∈ Mini A) : View K (quantumD B S F) = 0 := by
  classical
  let W (i j : A) := View K (D j (D i F))
  have H : View K (quantumD B S F) = ∑ x : A, ∑ y : A, ward K B S x y * W x y := by
    unfold W
    rw [quantum_apply, map_add, add_comm, lap_view, deriv_view h hc hk hf hL]
    simp only [ward, add_mul, Finset.sum_add_distrib]
  let u (x y : A) := ward K B S x y * W x y
  have he x y : u x y = -u y x := by
    unfold u
    rw [eq_neg_of_add_eq_zero_left (hw x y), show W x y = cross (p x) (p y) * W y x from ?_]
    · rw [neg_mul, mul_mul_mul_comm, cross_cross, one_mul]
    unfold W
    rw [hf.commute, map_smul]
    rfl
  rw [H]
  change (∑ x : A, ∑ y : A, u x y) = 0
  apply two_nsmul_eq_zero.mp
  rw [two_nsmul]
  apply eq_neg_iff_add_eq_zero.mp
  calc
    _ = ∑ x : A, ∑ y : A, -u y x :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl fun _ _ => he ..)
    _ = _ := by
      simp_rw [Finset.sum_neg_distrib]
      rw [Finset.sum_comm]

end YM.WilsonMS
