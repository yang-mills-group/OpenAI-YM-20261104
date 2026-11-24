import YM.Integration.WilsonThermometerFrozenCopies

/-! Restoring the raw Laurent grade on a copied socket keeps its numerical
upper coupling fixed throughout the subsequent lower reversion. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFrozenRevaluation
open Finset Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarGradedScene
open scoped Classical BigOperators

private theorem scale (d a : ℕ) (paid : a≤d+1) (g τ u : ℝ) (clock : u≠0) :
    (u^(d+1))⁻¹*((g/τ)^a*u^(d+1-a)) = (g/u)^a*(τ⁻¹)^a := by
  have split : u^(d+1) = u^(d+1-a)*u^a := by
    rw [←pow_add,Nat.sub_add_cancel paid]
  rw [split]
  simp only [mul_inv_rev,div_eq_mul_inv,inv_pow]
  have path := (pow_ne_zero (d+1-a) clock)
  field_simp [path,clock]
  rw [div_pow,div_pow,mul_comm (u^a),div_mul_cancel₀ _ (pow_ne_zero a clock)]

variable {G : Gauge} (R : Run G) {V T : Type}
  (d : V→ℕ) (g τ : ℝ) (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)
  {f : Side} (i : Entry R d) (u : ℝ) (x : T) (z : Site f) (U : Config G f)

theorem divided (clock : u≠0) :
    ((u^(d (root R d i)+1) : ℝ):ℂ)⁻¹ * WilsonThermometerFrozenCopies.word R d g τ v t i u x z U =
      (((g/u)^(pole R d i):ℝ):ℂ) *
      (t (root R d i) x * scalar R d 1 1 v i * ((τ⁻¹^(pole R d i):ℝ):ℂ) *
       ↑((raw R d i).unmasked U z)) := by
  have h := congrArg Complex.ofReal (scale (d (root R d i)) (pole R d i)
    (Nat.le_succ_of_le (pole_grade R d i)) g τ u clock)
  simp only [Complex.ofReal_mul,Complex.ofReal_inv] at h
  unfold WilsonThermometerFrozenCopies.word
  simp only [Complex.ofReal_mul]
  linear_combination (t (root R d i) x * scalar R d 1 1 v i * ↑((raw R d i).unmasked U z))*h

theorem at_birth (live : g≠0) :
    ((g^(d (root R d i)+1):ℝ):ℂ)⁻¹ * WilsonThermometerFrozenCopies.word R d g τ v t i g x z U =
      t (root R d i) x * scalar R d 1 1 v i * ((τ⁻¹^(pole R d i):ℝ):ℂ) *
       ↑((raw R d i).unmasked U z) := by
  rw [divided R d g τ v t i g x z U live,div_self live,one_pow,Complex.ofReal_one,one_mul]

end YM.Integration.WilsonThermometerFrozenRevaluation
