import YM.FVA2.Fourier.Char
import YM.MS.Swirl.TickH

/-! # Range of the Fourier kernel at one momentum

`U` is a vector in **midpoint** phase convention; here we only see the unrestricted Torus.
A ∈ transverse, K along a gradient, B absent. The singular p=0 condition matters: `c` too
is integrated only on mean-zero modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset
open YM.MS YM.MS.Plane YM.MS.Landau YM.MS.City YM.MS.Tone YM.MS.Momentum
open YM.MS.Orbit YM.MS.Swirl.Near
open YM.Lattice
open Complex (I)
open scoped BigOperators Matrix
variable {n : Side}
local notation "A" => Landau.gauge
local notation "U" => (Atom Axis → ℂ)

/-- The midpoint covariance before color copies. -/
def tailMatrix (p : Site n) : Matrix (Atom Axis) (Atom Axis) ℂ :=
  Matrix.of fun a b => Tail a b (wave (Coord p))
local notation "T" => tailMatrix
local notation "π" => precision

structure Integrates (p : Site n) (v : U) : Prop where
  trans : ∑ i, freq p i * v (A i) = 0
  axial : ∃ z : ℂ, ∀ i, v (anti i) = freq p i * z
  closed : v gaugeC = 0
  removed : p=0 → v=0

variable (p : Site n) (v : U)
lemma tail_A (i : Axis) : (T p *ᵥ v) (A i) = ((wave (Coord p)).sq : ℂ)⁻¹ ^2 *
    ∑ j, (π i j (wave (Coord p)) : ℂ) * v (A j) := by
  unfold Matrix.mulVec dotProduct
  simp only [tailMatrix, Matrix.of_apply, Landau.gauge, Fintype.sum_prod_type (α₁ := Option Axis),
    Fintype.sum_option, Fintype.sum_bool]
  simp only [Tail, zero_mul, add_zero, zero_add,
    Complex.ofReal_div, Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [div_eq_mul_inv, inv_pow]; ring

lemma tail_anti (i : Axis) : (T p *ᵥ v) (anti i) = freq p i * (I * v ghost / (wave (Coord p)).sq) := by
  unfold Matrix.mulVec dotProduct
  simp only [tailMatrix, Matrix.of_apply, anti, Fintype.sum_prod_type (α₁ := Option Axis),
    Fintype.sum_option, Fintype.sum_bool]
  simp only [Tail, zero_mul, add_zero, zero_add, Finset.sum_const_zero, Complex.ofReal_div]
  unfold freq ghost; ring
lemma tail_B : (T p *ᵥ v) gaugeC = 0 := by
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero; intro j _; rcases j with ⟨_|i,_|_⟩ <;> exact zero_mul _
lemma tail_c : (T p *ᵥ v) ghost = (I / (wave (Coord p)).sq) * ∑ j, freq p j * v (anti j) := by
  unfold Matrix.mulVec dotProduct
  simp only [tailMatrix, Matrix.of_apply, ghost, Fintype.sum_prod_type (α₁ := Option Axis),
    Fintype.sum_option, Fintype.sum_bool]
  simp only [Tail, zero_mul, add_zero, zero_add, Complex.ofReal_div, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  unfold freq anti; ring

theorem integrates_tail : Integrates p (T p *ᵥ v) where
  trans := by
    let x (i j : Axis) := (π i j (wave (Coord p)) : ℂ)
    let a := ((wave (Coord p)).sq : ℂ)⁻¹ ^ 2
    have h i j : freq p i * (a * (x i j * v (A j))) = x j i * freq p i * (a * v (A j)) := by
      unfold x; rw [realK i j]; ring
    dsimp [a,x] at h
    simp_rw [tail_A, Finset.mul_sum, h]
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, trans_freq, zero_mul, Finset.sum_const_zero]
  axial := ⟨ _, tail_anti p v⟩
  closed := tail_B p v
  removed hp := by
    subst p; funext i
    have hw : (wave (Coord (0:Site n))).sq = 0 := by rw [← Complex.ofReal_inj]; push_cast; rw [← freq_square]; simp
    unfold Matrix.mulVec dotProduct tailMatrix
    simp only [Matrix.of_apply, zeroShift _ _ hw, zero_mul, Pi.zero_apply, Finset.sum_const_zero]

private lemma tail_open (h : Integrates p v) {r : ℂ} (hr : ∀ i, v (anti i)=freq p i * r)
    (hp : p ≠ 0) :
    let s := ((wave (Coord p)).sq : ℂ)
    let u : U := fun x => match x with
      | (some _, false) => s * v x
      | (some i, true) => -I * freq p i * v ghost
      | (none, false) => -I * s * r
      | (none, true) => 0
    T p *ᵥ u = v := by
  intro s u
  have hn : s≠0 := wave_sq_ne hp
  have ht (i : Axis) : u (A i) = s * v (A i) := rfl
  have hb i : u (anti i) = -I * freq p i * v ghost := rfl
  have hc : u ghost = -I * s * r := rfl
  have hw : ∀ i : Axis, s⁻¹ ^ 2 * (∑ j, (π i j (wave (Coord p)):ℂ) * u (A j)) = v (A i) := by
    intro i
    have hh : ∀ j, (π i j (wave (Coord p)) : ℂ) * (s * v (A j)) =
       s * ((if i=j then s else 0) * v (A j) - freq p i * (freq p j * v (A j))) := fun j => by
      rw [mul_left_comm _ s, precision_f, sub_mul, mul_assoc (freq p i)]
    simp_rw [ht]; dsimp [s] at hh ⊢; simp_rw [hh]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, h.trans]
    simp only [mul_zero, sub_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    field_simp [wave_sq_ne hp]
  funext i
  rcases i with ⟨_|i,_|_⟩
  · change (T p *ᵥ u) ghost = _
    rw [tail_c]
    simp_rw [hb]
    have he j : freq p j * (-I * freq p j * v ghost) = freq p j * freq p j * (-I * v ghost) := by ring
    simp_rw [he, ← Finset.sum_mul, freq_square]
    change I / s * (s * _) = v ghost
    field_simp; simp
  · change (T p *ᵥ u) gaugeC = v gaugeC; rw [tail_B, h.closed]
  · change (T p *ᵥ u) (A i) = _
    rw [tail_A]; exact hw i
  · change (T p *ᵥ u) (anti i) = v (anti i)
    rw [tail_anti,hc,hr i]
    change freq p i * (I * (-I * s * r) / s) = _
    field_simp; simp

theorem tail_range : Integrates p v ↔ ∃ x, T p *ᵥ x = v := by
  constructor
  · intro h; by_cases hp : p=0
    · exact ⟨0, (Matrix.mulVec_zero _).trans (h.removed hp).symm⟩
    obtain ⟨r, hr⟩ := h.axial
    exact ⟨_, tail_open p v h hr hp⟩
  rintro ⟨x,rfl⟩; exact integrates_tail p x

end YM.FVA2.Fourier
