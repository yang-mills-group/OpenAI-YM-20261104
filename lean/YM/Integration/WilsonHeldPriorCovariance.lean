import YM.Integration.WilsonHeldHaarCofactor
import YM.Integration.ActualNormalizedPush

/-! The signed, centered insertion on the original positive Wilson
conditional. All source factors share the same prior and held field. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldPriorCovariance

open Set MeasureTheory Lattice Wilson RG
open scoped Classical

variable {G : Gauge} (C : Family G) {N n j : ℕ}
local notation "fine" => Config G (C.side (j+1) n)
local notation "coarse" => Config G (C.side j n)
local notation "ν" => prior G (C.side (j+1) n)
local notation "Q" => C.path.rep N n (j+1)
local notation "Q'" => C.path.rep N n j

theorem represented (X : fine → ℂ) (V : coarse) :
    actualAverage C (N := N) X V = WilsonHeldHaarCofactor.conditional C.path N n j X V := by
  rw [actualAverage_push]
  simp only [WilsonHeldHaarCofactor.conditional, Complex.real_smul, Complex.ofReal_inv,
    div_eq_mul_inv, mul_comm]

/-- Center after drawing the fresh mark under the very same held Wilson field. -/
def connected (A B : fine → ℂ) (V : coarse) : ℂ :=
  actualAverage C (N := N) (fun U => A U * (B U - actualAverage C (N := N) B V)) V

theorem original (A B : fine → ℂ) (V : coarse)
    (old : Integrable (fun U => actualConditionalDensity C N n j V U • A U) ν)
    (joint : Integrable (fun U => actualConditionalDensity C N n j V U • (A U * B U)) ν) :
    connected C (N := N) A B V = actualAverage C (N := N) (fun U => A U * B U) V -
      actualAverage C (N := N) A V * actualAverage C (N := N) B V := by
  let d := actualConditionalDensity C N n j V
  let b := actualAverage C (N := N) B V
  change (∫ U, d U • (A U * (B U - b)) ∂ν) =
    (∫ U, d U • (A U * B U) ∂ν) - (∫ U, d U • A U ∂ν) * b
  calc
    _ = ∫ U, d U • (A U * B U) - (d U • A U) * b ∂ν := by
      apply integral_congr_ae
      apply ae_of_all
      intro U
      simp only [Complex.real_smul]
      ring
    _ = _ := by rw [integral_sub joint (old.mul_const b), integral_mul_const]

/-- Signed connected contribution of an old component on its original event.
The full K numerator is multiplied by the centered fresh field before Haar
integration. -/
theorem held (E : Set fine) (A F B : fine → ℂ) (V : coarse)
    (old : ∀ U ∈ E, ((Q).eval U : ℂ) * A U = F U) :
    connected C (N := N) (E.indicator A) B V =
      (∫ U, E.indicator (fun W => (((C.path.levels.clock.op j n).density (C.path.β N n (j+1))) W V : ℂ) *
        (B W - actualAverage C (N := N) B V) * F W) U ∂ν) / ((Q').eval V : ℂ) := by
  let c := fun U => B U - actualAverage C (N := N) B V
  have eq : (fun U => E.indicator A U * c U) = E.indicator (fun U => c U * A U) := by
    funext U
    by_cases h : U ∈ E <;> simp [h, mul_comm]
  unfold connected
  rw [represented]
  change WilsonHeldHaarCofactor.conditional C.path N n j (fun U => E.indicator A U * c U) V = _
  rw [eq]
  exact WilsonHeldHaarCofactor.held C.path N n j E A F c old V

end YM.Integration.WilsonHeldPriorCovariance

