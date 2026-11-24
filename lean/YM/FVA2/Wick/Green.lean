import YM.FVA2.Wick.Pull

/-!
# Factor a possibly singular graded Wick covariance (as in Master on the inversion quotient)

If `C H C = -C`, know the *exact* range of C, and have graded symmetry, testing the action
matrix H on a basis of that range suffices. Purely bilinear (no complex conjugation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset MS MS.Koszul MS.Orbit MS.Orbit.Cog
open scoped BigOperators Matrix
variable {A B : Type} [Fintype A] [Fintype B]

omit [Fintype A] in
private theorem mat_ext (x y : Matrix A B ℂ) (h : ∀ v, x *ᵥ v = y *ᵥ v) : x=y := by
  classical exact Matrix.toLin'.injective (LinearMap.ext (fun i=>by rw [Matrix.toLin'_apply,Matrix.toLin'_apply,h]))
private theorem mat_factor (x : Matrix A A ℂ) (y : Matrix A B ℂ)
    (h : ∀ v, ∃ u, x *ᵥ u = y *ᵥ v) : ∃ L : Matrix A B ℂ, x*L=y := by
  choose u hu using h
  classical
  refine ⟨Matrix.of fun i j => u (Pi.single j 1) i,?_⟩
  ext i j
  specialize hu (Pi.single j 1); rw [Matrix.mulVec_single_one] at hu
  exact congr_fun hu i

private theorem left_exists [DecidableEq A] [DecidableEq B] (x : Matrix A B ℂ)
    (h : ∀ u v, x *ᵥ u=x *ᵥ v → u=v) : ∃ y : Matrix B A ℂ, y*x=1 := by
  let L := Matrix.toLin' x
  have inj : Function.Injective L := fun i j he => h i j (by rwa [← Matrix.toLin'_apply,← Matrix.toLin'_apply])
  refine ⟨LinearMap.toMatrix' L.leftInverse,mat_ext _ _ (fun i => ?_)⟩
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,Matrix.one_mulVec]
  exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr inj) i

omit [Fintype B] in
private theorem side_range (x : Matrix A A ℂ) (p : Sector A)
    (hs : Cog.Sym p x) (ht : Clear p x) (u : A→ℂ) : ∃ v, x *ᵥ v = xᵀ *ᵥ u := by
  refine ⟨fun i=> (cross (p i) true : ℂ) * u i,funext fun i=> ?_⟩
  unfold Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl fun j _=> ?_
  change _ = x j i * u j
  rw [hs j i]
  by_cases h : x i j=0
  · simp [h]
  rw [ht i j h]; cases h:p j <;> simp [h]

-- can use existing Green validity without proving SPD/rank again.
theorem factor_matrix (D : Matrix A B ℂ) (C H : Matrix A A ℂ) (p : Sector A)
    (hs : Cog.Sym p C) (ht : Clear p C) (he : C*H*C = -C)
    (hd : ∀ x y, D *ᵥ x=D *ᵥ y → x=y)
    (hr : ∀ u, (∃ x, C *ᵥ x=u) ↔ ∃ y, D *ᵥ y=u)
    [DecidableEq B] (cov : Matrix B B ℂ)
    (hm : (Dᵀ*H*D)*cov = -1) : C = D*cov*Dᵀ := by
  classical
  obtain ⟨y,hy⟩ := left_exists D hd
  have hc {x : Matrix A A ℂ} (h : ∀ v, ∃ u, D *ᵥ u = x *ᵥ v) : D*y*x=x := by
    apply mat_ext; intro v; obtain ⟨u,H⟩ := h v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,← H,Matrix.mulVec_mulVec u y, hy, Matrix.one_mulVec]
  have hi : D*y*C=C := hc (fun v=> (hr _).mp ⟨v,rfl⟩)
  have hj : C*(yᵀ*Dᵀ)=C := by
    have hv : D*y*Cᵀ=Cᵀ := hc (fun v => (hr _).mp (side_range _ p hs ht v))
    rw [← Matrix.transpose_mul, ← Matrix.transpose_inj]; simpa using hv
  let S := y*C*yᵀ
  have hp : D*S*Dᵀ=C := by
    unfold S; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,hi, Matrix.mul_assoc, hj]
  have hd' : C * H * D = -D := by
    obtain ⟨L,rfl'⟩:= mat_factor C D fun v=> (hr _).mpr ⟨v,rfl⟩
    rw [← rfl', ← Matrix.mul_assoc, he]; simp
  suffices hs : S * (Dᵀ*H*D) = -1 by
    have h := congr_arg (·*cov) hs
    rw [Matrix.mul_assoc,hm] at h
    simp at h
    rw [← h]; exact hp.symm
  have ha : y * (C * H * D)= -1 := by rw [hd']; simp [hy]
  rw [← hp] at ha
  calc
    _ = y * ( D * S * Dᵀ * H * D) := by simp only [← Matrix.mul_assoc, hy, Matrix.one_mul]
    _ = -1 := ha
end YM.FVA2.Wick
