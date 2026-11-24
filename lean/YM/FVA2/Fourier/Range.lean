import YM.FVA2.Fourier.MomentRange

/-! # Exact range and green relations for the `Master` covariance

This identifies its rank in Fourier coordinates. Position form follows in PositionRange. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset
open YM.MS YM.MS.Koszul YM.MS.Plane YM.MS.Landau YM.MS.City YM.MS.Tone YM.MS.Momentum
open YM.MS.Orbit Cog YM.MS.Swirl YM.MS.Swirl.Near YM.Lattice
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}
local notation "E" => FixedMode G n
local notation "C" => G.ColorIndex

/-- Twice the Grain of the MS covariance (the physical Wick contraction). -/
def kernel (G : Gauge) (n : Side) (b : Bool) : Matrix (FixedMode G n) (FixedMode G n) ℂ :=
  Matrix.of (Chill (Master G n b))
local notation "S" => kernel G n false
local notation "K" => kernel G n true

lemma kernel_straight (a b : BH G) (p q : Site n) :
    S (a,p) (b,q) = if q= -p then scaleZ n * Bass G a b (Coord p) else 0 := by
  change Chill (mat n (FinalK G)) (a,p) (b,q)= _
  split_ifs with h
  · subst h; exact ChillK ..
  exact chillOff a b p q h

lemma kernel_phase : (iota G n).phase S := by
  intro i j
  simp only [kernel, Matrix.of_apply, Chill]
  rw [show Master G n false = mat n (FinalK G) from rfl, riverOK (G:=G) BankK.pin BankK.gov i j,
    mul_assoc 2]
lemma kernel_cascade : Matrix.of ((iota G n).Cascade S) = K := by
  ext i j
  simp only [kernel, Matrix.of_apply, Master, Paper, Cascade, imageV, imageW, Pi.add_apply,
    if_true, if_false, Bool.false_eq_true, Chill, mul_add]; rw [mul_assoc]

lemma kernel_chc :
    let H := Matrix.of fun i j : E => pay true * flatH G n [i,j]
    K * H * K = -K := by
  intro H
  ext i j
  have he := (planeS (G:=G) (n:=n) (b:=true) (fun _ => 1)).reads i j
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_mul] at he
  simp only [Matrix.mul_apply, Matrix.neg_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact he

lemma kernel_clear (b : Bool) : Clear σbranch (kernel G n b) := fun i j h =>
  zeroM b _ _ (right_ne_zero_of_mul (show 2 * Master G n b i j ≠ 0 from h))
lemma kernel_symm (b : Bool) : Sym σbranch (kernel G n b) := by
  intro i j; simp only [kernel, Matrix.of_apply, Chill]; rw [paySym b i j]; ring

/-- Midpoint convention on the Fourier leg vectors; useful for testing the range. -/
def mid (p : Site n) (c : C) (v : E→ℂ) (i : Atom Axis) : ℂ :=
  (flag (i,c) (Coord p))⁻¹ * v ((i,c),p)

theorem by_tail (p : Site n) (c : C) (v : E → ℂ) :
    mid p c (S *ᵥ v) = tailMatrix p *ᵥ (fun i => scaleZ n * (flag (i,c) (-(Coord p))) * v ((i,c),-p)) := by
  funext i; unfold mid Matrix.mulVec dotProduct
  let f := flag (i,c) (Coord p)
  simp only [Fintype.sum_prod_type (α₁ := BH G), kernel_straight, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type (α₁ := Atom Axis), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single c]
  · unfold Bass Landau.choir
    simp only [if_true]; change f⁻¹ * (_ * (f * _ * tailMatrix p i j) * _) = _
    have hn : f ≠ 0 := nonza ((i,c),Coord p)
    field_simp
  · intro b _ hb; unfold Bass; simp [Landau.choir,Ne.symm hb]
  exact fun h => (h (Finset.mem_univ _)).elim

lemma kernel_modes (v : E→ℂ) : (∃ x, S *ᵥ x = v) ↔ ∀ p c, Integrates p (mid p c v) := by
  constructor
  · rintro ⟨x,rfl⟩ p c; rw [by_tail]; exact integrates_tail ..
  intro h
  choose x hx using fun p c => (tail_range ..).mp (h p c)
  let F (a : BH G) (q : Site n) := (scaleZ n * (flag a (-(Coord q))))⁻¹
  let g (i : E) := F i.1 (-i.2) * x (-i.2) i.1.2 i.1.1
  refine ⟨g,funext fun ⟨⟨a,c⟩,p⟩ => ?_⟩
  have hb (i : Atom Axis) : scaleZ n * flag (i,c) (-Coord p) * g ((i,c),-p) = x p c i := by
    unfold g F
    simp only [neg_neg, ← mul_assoc]
    rw [mul_inv_cancel₀ (show scaleZ n * flag (i,c) (-Coord p) ≠ 0 from mul_ne_zero (scale_ne n) (nonza _)), one_mul]
  have hu : mid p c (S *ᵥ g) = mid p c v := by rw [by_tail,funext hb,hx]
  exact mul_left_cancel₀ (inv_ne_zero (nonza ((a,c),Coord p))) (congr_fun hu a)

-- General Cascade image. Uses covariance phase to close range. Comes with factor 2 from
-- inversion projection; no fixed-mode exceptions.
section cascade
variable {A : Type} [Fintype A] {q : Sector A} (I : Cog q) (L : Matrix A A ℂ) (h : I.phase L)
local notation "Z" => Matrix.of (I.Cascade L)

include h in
theorem cascade_range (v : A→ℂ) : (∃ x, Z *ᵥ x = v) ↔
    (∃ x, L *ᵥ x = v) ∧ ∀ x, v (I.mode x) = v x * I.spin x := by
  constructor
  · rintro ⟨a,rfl⟩
    constructor
    · refine ⟨fun i => a i + I.spin i * a (I.mode i), funext fun i => ?_⟩
      unfold Matrix.mulVec dotProduct
      simp only [Matrix.of_apply, Cascade, imageW, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; congr 1
      let f j := L i j * (I.spin j * a (I.mode j)); change ∑ j, f j = _
      rw [← Equiv.sum_comp I.axis f]; refine Finset.sum_congr rfl fun j _ => ?_
      change f (I.mode j) = _; unfold f; rw [show I.mode (I.mode j) = j from I.perm j, mul_assoc]
    intro i; unfold Matrix.mulVec dotProduct; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    change I.Cascade L (I.mode i) j * a j = I.Cascade L i j * a j * _
    rw [Rc h i j, mul_right_comm]
  rintro ⟨⟨x,rfl⟩,he⟩
  have hv (i : A) : (Z *ᵥ x) i = 2 * (L *ᵥ x) i := by
    unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply, Cascade, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    simp_rw [image_u h i, show ∀ j, L (I.mode i) j * I.spin (I.mode i) * x j =
      L (I.mode i) j * x j * I.spin (I.mode i) from fun j => mul_right_comm ..]
    rw [← Finset.sum_mul]
    change (L *ᵥ x) i + (L *ᵥ x) (I.mode i) * _ = _
    rw [he,mul_assoc,I.holo i,mul_one,two_mul]; rfl
  refine ⟨(2 : ℂ)⁻¹ • x,funext fun i => ?_⟩
  rw [Matrix.mulVec_smul, Pi.smul_apply, hv, smul_eq_mul]; ring
end cascade

/-- Range before putting the external fields in position basis. -/
theorem in_range (v : E → ℂ) : (∃ x, K *ᵥ x = v) ↔
    (∀ p c, Integrates p (mid p c v)) ∧ ∀ a p, v (a,-p) = v (a,p) * switch (a,Coord p) := by
  rw [← kernel_cascade, cascade_range _ _ kernel_phase, kernel_modes]
  refine and_congr Iff.rfl ⟨fun h a p => h (a,p), ?_⟩; rintro h ⟨a,p⟩; exact h a p
end YM.FVA2.Fourier
