import YM.FormalOPE.RG10.FlatFeed

/-! Native degree shifts (useful e.g. for the Laurent prefactors of field stencils). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open MeasureTheory PowerSeries
open scoped BigOperators

def delay {X : Type*} (d : ℕ) (f : Kernel X) : Kernel X := fun x => PowerSeries.X ^ d * f x
lemma row_delay {X : Type*} (d n) (f : Kernel X) :
    row n (delay d f) = if d ≤ n then row (n-d) f else 0 := by
  by_cases h : d ≤ n <;> funext x <;> simp [row, delay, coeff_X_pow_mul', h]
lemma delay_mul {X : Type*} (f g : Kernel X) (i j : ℕ) :
    delay (i + j) (f * g) = delay i f * delay j g := by
  funext x
  simp only [delay, pow_add, Pi.mul_apply]; ring
@[simp] lemma delay_zero {X : Type*} (f : Kernel X) : delay 0 f = f := by
  funext x; simp [delay]
lemma delay_inj {X : Type*} (d : ℕ) : Function.Injective (@delay X d) := by
  intro f b h; funext x; ext n : 1
  have h := congr_fun (congr_arg (row (d+n)) h) x
  rw [row_delay, row_delay, if_pos (by omega), if_pos (by omega), show d+n-d=n by omega] at h
  exact h

/-- Forget the discarded degrees of `A`; in uses for Laurent lowering we will prove first that
this recovers the FULL original `A` after multiplying by `X^d`. -/
def lower (d : ℕ) (A : Series) : Series := PowerSeries.mk fun n => PowerSeries.coeff (d + n) A

lemma lower_delay (A : Series) (d : ℕ) : lower d (PowerSeries.X^d * A) = A := by
  ext; simp [lower, coeff_X_pow_mul']

namespace FlatFeed
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E)
    (W : Vertices (Θ × E)) (f : Kernel (Θ × E)) (d : ℕ)

@[simp] lemma mean_zero : F.mean 0 = 0 := by simp [mean]

lemma average_delay : F.average (delay d f) = X^d * F.average f := by
  ext n : 1
  rw [coeff_X_pow_mul', average_coeff, average_coeff, row_delay]
  split <;> simp

lemma funded_of_delay (h : F.Funded (delay d f)) : F.Funded f := by
  intro n
  specialize h (d+n)
  rwa [row_delay, if_pos (by omega), show d+n-d=n by omega] at h

lemma step_delay : F.step W (delay d f) = X^d * F.step W f := by
  rw [step, ← delay_mul_right, average_delay, step, mul_assoc]
where delay_mul_right : delay d (W.weight * f) = W.weight * delay d f := by
        simpa only [zero_add, delay_zero] using delay_mul W.weight f 0 d
end FlatFeed
end YM.FormalOPE.RG10
