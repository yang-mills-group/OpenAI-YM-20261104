import YM.MSbar.Wave.Rider
import YM.Integration.WilsonPosteriorProjectionTaylor
import YM.Analysis.Homogeneous
import YM.MSbar.Cacao.Acre

/-! The real sampled comparison is to the complete original clock reading
of the independent emitted bank. The formal radial rows are its actual
homogeneous components, with the degree cutoff furnished by that bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionBank
open Finset MSbar MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal MSbar.Wave
open LocalLTE.Weft WilsonPosteriorProjectionTaylor MvPolynomial
open scoped BigOperators Classical
variable {ι : Type} [Fintype ι]

def component (p : ℕ) (g : ℝ) (T : PowerSeries (Pot ι)) (z : View ι) (k : ℕ) :=
  ∑ i ∈ range (p+1), g^i * MvPolynomial.eval z (homogeneousComponent k (PowerSeries.coeff i T))

theorem clock (p M : ℕ) (g : ℝ) (T : PowerSeries (Pot ι))
    (degree : ∀ i≤p, (PowerSeries.coeff i T).totalDegree ≤ 2*M) (z : View ι) (s : ℝ) :
    taste p (picture (s • z) T) g = ∑ k : J M, component p g T z k.val * s^k.val := by
  unfold taste picture
  simp only [PowerSeries.coeff_map]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => component p g T z k * s^k) (2*M+1)]
  have graded (i : ℕ) (hi : i < p+1) :
      MvPolynomial.eval (s • z) (PowerSeries.coeff i T) =
        ∑ k ∈ range (2*M+1), s^k * MvPolynomial.eval z (homogeneousComponent k (PowerSeries.coeff i T)) := by
    have expand := congrArg (MvPolynomial.eval (s • z)) (buys (2*M) (PowerSeries.coeff i T) (degree i (by omega)))
    rw [map_sum] at expand
    simpa only [hene s 0] using expand.symm
  calc
    _ = ∑ i ∈ range (p+1), g^i * ∑ k ∈ range (2*M+1), s^k *
      MvPolynomial.eval z (homogeneousComponent k (PowerSeries.coeff i T)) := by
        apply sum_congr rfl
        intro i hi
        rw [graded i (mem_range.mp hi)]
    _ = _ := by
      unfold component
      simp only [mul_sum,sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro i _
      ring

def reading (p : ℕ) (g : ℝ) (T : PowerSeries (Pot ι)) (z : View ι) := taste p (picture z T) g

theorem regular (p : ℕ) (g : ℝ) (T : PowerSeries (Pot ι)) (j : ℕ) :
    ContDiff ℝ j (reading p g T) := by
  unfold reading taste picture
  simp only [PowerSeries.coeff_map]
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((vent (PowerSeries.coeff i T)).of_le (by simp))

theorem diagonal (p M : ℕ) (g : ℝ) (T : PowerSeries (Pot ι))
    (degree : ∀ i≤p, (PowerSeries.coeff i T).totalDegree ≤ 2*M) (z : View ι) (j : J M) :
    Tensor.diagonal (Tensor.coeff (reading p g T) j.val 0) z = component p g T z j.val := by
  have expansion : (fun s : ℝ => reading p g T (s • z)) =
      fun s => ∑ k : J M, component p g T z k.val * s^k.val := funext (clock p M g T degree z)
  have deriv := Next.Foundations.iteratedDeriv_on_line (regular p g T j.val).contDiffAt z
  rw [expansion] at deriv
  have smooth (a : J M) : ContDiffAt ℝ j.val (fun s : ℝ => component p g T z a.val * s^a.val) 0 := by fun_prop
  rw [iteratedDeriv_fun_sum (f:=fun (a : J M) (s : ℝ) => component p g T z a.val * s^a.val)
    (fun i _ => smooth i)] at deriv
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero] at deriv
  have count (i : J M) : j.val=i.val ↔ i=j := ⟨fun h => Fin.ext h.symm,fun h => h ▸ rfl⟩
  simp only [count] at deriv
  have one : (∑ i : J M, component p g T z i.val *
        ((if i=j then i.val.factorial else 0 : ℕ) : ℝ)) =
      component p g T z j.val * j.val.factorial := by
    rw [sum_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [one] at deriv
  change ((j.val.factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ j.val (reading p g T) 0))
    (fun _ => z) = _
  rw [smul_apply,smul_eq_mul,show (iteratedFDeriv ℝ j.val (reading p g T) 0)
    (fun _ => z) = _ from deriv.symm]
  field_simp

end YM.Integration.WilsonPosteriorProjectionBank

