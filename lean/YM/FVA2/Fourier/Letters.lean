import YM.FVA2.Fourier.Range
/-! Scalar Fourier translation for the letters on the inversion torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset Lattice
open YM.MS YM.MS.Plane YM.MS.Koszul YM.MS.City YM.MS.Tone YM.MS.Landau YM.MS.Momentum YM.MS.Orbit
open scoped BigOperators Matrix ComplexConjugate
variable {G : Gauge} {n : Side}
local notation "C" => G.ColorIndex
local notation "T" => Site n
local notation "E" => FixedMode G n
local notation "K" => kernel G n true

/-- DFT of a single position leg coefficient. -/
def hat (n : Side) : (Site n→ℂ) ≃ₗ[ℂ] (Site n→ℂ) := by
  let m := (Bloch.F n).mulVecLin
  let M := ((scaleZ n) • (Bloch.F n)ᴴ).mulVecLin
  refine LinearEquiv.ofLinear M m ?_ ?_
  all_goals apply LinearMap.ext; intro v
  · change ((scaleZ n) • (Bloch.F n)ᴴ) *ᵥ ((Bloch.F n) *ᵥ v)=v
    rw [Matrix.mulVec_mulVec, Matrix.smul_mul, ← Matrix.star_eq_conjTranspose,
      Bloch.coGram n, smul_smul, scale_val, inv_mul_cancel₀ (pow_ne_zero _ (Bloch.side_ne n)),
      one_smul, Matrix.one_mulVec]
  change Bloch.F n *ᵥ (((scaleZ n) • (Bloch.F n)ᴴ) *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, ← Matrix.star_eq_conjTranspose,
    Bloch.gram n, smul_smul, scale_val, inv_mul_cancel₀ (pow_ne_zero _ (Bloch.side_ne n)),
    one_smul, Matrix.one_mulVec]

lemma hat_at (f : T→ℂ) (p : T) : hat n f p = scaleZ n * ∑ x, (Bloch.cell p x)⁻¹ * f x := by
  change (((scaleZ n) • (Bloch.F n)ᴴ) *ᵥ f) p = _
  rw [Matrix.smul_mulVec]; unfold Matrix.mulVec dotProduct
  change scaleZ n * _ = _
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_; change conj (Bloch.cell j p) * _ = _
  rw [Bloch.cell_duality j, Bloch.cell_bar]
lemma pack_hat (v : E→ℂ) (a : BH G) (p : T) :
    (toFreq G n *ᵥ v) (a,p) = hat n (fun x => v (a,x)) p := by rw [hat_at, pack_at]

lemma hat_addTranslate (f : T→ℂ) (x p : T) :
    hat n (fun i => f (i+x)) p = Bloch.cell p x * hat n f p := by
  rw [hat_at,hat_at, mul_left_comm]; congr 1
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight x) (fun i => Bloch.cell p x * ((Bloch.cell p i)⁻¹ * f i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = Bloch.cell p x * ((Bloch.cell p (j+x))⁻¹ * f (j+x)); rw [Bloch.cell_add]; field_simp
lemma cell_reflect (x p : T) : Bloch.cell (-p) x = (Bloch.cell p x)⁻¹ := by
  rw [Bloch.cell_duality (-p), Bloch.cell_inverse, Bloch.cell_duality x]
lemma hat_reflect (f : T→ℂ) (p : T) : hat n (fun i => f (-i)) p = hat n f (-p) := by
  rw [hat_at, hat_at]; congr 1
  rw [← Equiv.sum_comp (Equiv.neg T) (fun i => (Bloch.cell (-p) i)⁻¹ * f i)]
  exact Finset.sum_congr rfl fun j _ => by simp only [Equiv.neg_apply,Bloch.cell_inverse,cell_reflect,inv_inv]

lemma hat_div (f : Axis→T→ℂ) (p : T) :
    hat n (fun x => ∑ i, (f i x - f i (x-step i))) p = Complex.I *
      ∑ i, freq p i * ((midpoint p i)⁻¹ * hat n (f i) p) := by
  let t i x := f i (x + -step i)
  rw [show (fun x => ∑ i, (f i x - f i (x-step i))) = ∑ i, (f i - t i) from by
    funext x; simp [t, Finset.sum_apply, sub_eq_add_neg], map_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, Pi.sub_apply, show hat n (t i) p = _ from hat_addTranslate (f i) (-step i) p]
  rw [Bloch.cell_inverse, ← mul_assoc, ← mul_assoc, ← div_hat]
  ring

lemma hat_grad (f : T → ℂ) (p : T) (i : Axis) :
    hat n (fun x => f x - f (x+step i)) p =
      -(Complex.I * freq p i) * midpoint p i * hat n f p := by
  let t x := f (x+step i)
  change hat n (f-t) p=_
  rw [← grad_hat,map_sub,Pi.sub_apply,show hat n t p = _ from hat_addTranslate f (step i) p]; ring

lemma hat_inv (f : T → ℂ) (a : BH G) (p : T) :
    hat n (fun x => sgn a * f (-x-shiftBase a)) (-p) = switch (a,Coord p) * hat n f p := by
  let b x := f (-x)
  rw [show (fun x : T => sgn a * f (-x-shiftBase a)) = sgn a • (fun x : T => b (x+shiftBase a)) from by
    funext x; simp [b,sub_eq_add_neg,add_comm (-x)], map_smul, Pi.smul_apply,
    hat_addTranslate b, hat_reflect, neg_neg, cell_reflect, switch_at]; exact (mul_assoc ..).symm

lemma hat_zero (f : T → ℂ) : hat n f 0 = scaleZ n * ∑ x, f x := by rw [hat_at]; simp [Bloch.cell]
lemma all_off {f : T → ℂ} (h : ∀ p : T, hat n f p = 0) : f=0 := (hat n).injective (by rw [map_zero]; exact funext h)
end YM.FVA2.Fourier
