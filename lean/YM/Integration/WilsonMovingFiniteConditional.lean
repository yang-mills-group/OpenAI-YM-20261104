import YM.Integration.WilsonMovingIndependentWick
import YM.Integration.WilsonMovingExponentialConvention
import YM.Integration.WilsonMovingPolynomialPull
import YM.Integration.WilsonConditionalTaylorWick

/-! A finite normalized formal forest conditional equals the actual moving
Wick emission on its own earlier action. No matching of output coefficients
is assumed. The true input drift, Hessian and every coarse coordinate remain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingFiniteConditional
open Function PowerSeries Matrix FormalBulk08 Jets Orb Wick Series MSbar.Cacao
open WilsonMovingIndependentWick
open scoped Classical Matrix BigOperators
variable {V I : Type} [Fintype V] [DecidableEq V] (H : Hull V I)

def lift (I V : Type) [DecidableEq V] : Matrix (V ⊕ I) V ℝ :=
  fun j k => Sum.elim (fun v => if v=k then 1 else 0) (fun _ => 0) j

def mean (y : Rays I) : Rays (V ⊕ I) := Sum.elim (fun v => traceP y (H.drift v)) y

theorem full (x : Rays V) (y : Rays I) :
    mean H y + lift I V *ᵥ x = Sum.elim (fun v => x v + traceP y (H.drift v)) y := by
  funext j
  cases j <;> simp [mean,lift,Matrix.mulVec,dotProduct,add_comm]

theorem input (y : Rays I) (T : Pap (V ⊕ I)) :
    observe y (toInk H T) =
      PowerSeries.map (WilsonMovingWickCoefficient.affine (lift I V) (mean H y)).toRingHom T := by
  apply WilsonMovingPolynomialPull.detected
  intro x
  rw [direction,← full H x y]
  ext n
  rw [glimpse_coeff,glimpse_coeff,PowerSeries.coeff_map]
  exact (WilsonMovingWickCoefficient.evaluated (lift I V) (mean H y) x (coeff n T)).symm

def interaction (p : Pap (V ⊕ I)) := p - C (coeff 0 p)

omit [Fintype V] [DecidableEq V] in
theorem origin (p : Pap (V ⊕ I)) : Kind (interaction p) := by
  simp [Kind,interaction]

theorem weight (y : Rays I) (p : Pap (V ⊕ I)) (h : Solved H p) :
    observe y (Series.expan (Orb.positive H p)) =
      PowerSeries.map (WilsonMovingWickCoefficient.affine (lift I V) (mean H y)).toRingHom
        (Spring (interaction p)) := by
  unfold observe
  rw [map_expan _ (Orb.plur H p h), WilsonMovingIndependentWick.centered H p h]
  change expan (observe y (toInk H (interaction p))) = _
  rw [input, ← map_expan _ (origin p), WilsonMovingExponentialConvention.exp _ (origin p)]

theorem quotient [Fintype I] [DecidableEq I] (y : Rays I) (p q : Pap (V ⊕ I)) (h : Solved H p) :
    glimpse y (Orb.flag H p q) =
      WilsonConditionalTaylorWick.quotient (lift I V) (mean H y) H.saddle.q (interaction p) q := by
  let W := WilsonConditionalTaylorWick.contract (lift I V) (mean H y) H.saddle.q (Spring (interaction p))
  let Q := WilsonConditionalTaylorWick.contract (lift I V) (mean H y) H.saddle.q (q * Spring (interaction p))
  have unit := WilsonMovingIndependentWick.unit H y p h
  rw [weight H y p h] at unit
  change coeff 0 W = 1 at unit
  have invert : W * PowerSeries.invOfUnit W 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,unit]; rfl)
  have form := WilsonMovingIndependentWick.deposited H y p q h
  dsimp only at form
  rw [weight H y p h, input H y q] at form
  have law : W * glimpse y (Orb.flag H p q) = Q := by
    change _ = beam (Wick.moment H.saddle.q) (PowerSeries.map _ (q*Spring (interaction p)))
    rw [map_mul,mul_comm (PowerSeries.map _ q)]
    exact form
  change _ = Q * PowerSeries.invOfUnit W 1
  rw [← law,mul_comm W _,mul_assoc,invert,mul_one]

theorem emitted [Fintype I] [DecidableEq I] (y : Rays I) (p q : Pap (V ⊕ I))
    (h : Solved H p) (sym : H.saddle.q.IsSymm) (pos : H.saddle.q.PosDef) (k : ℕ) :
    Through k (WilsonMovingNormalizedBank.view (mean H y) (growP (interaction p) q
      (lift I V*H.saddle.q*(lift I V).transpose) (k+1))) (glimpse y (Orb.flag H p q)) := by
  rw [quotient H y p q h]
  exact WilsonConditionalTaylorWick.response (lift I V) (mean H y) H.saddle.q
    sym pos (interaction p) q (origin p) k

end YM.Integration.WilsonMovingFiniteConditional
end
