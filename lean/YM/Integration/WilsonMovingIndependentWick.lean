import YM.Integration.WilsonMarkedFiniteWickDefect
import YM.Integration.WilsonMovingWickCoefficient

/-! The fixed finite forest's independent marked equation on numerical
coarse directions. The affine shift is the true full drift; the two finite
Gaussian expectations share the original action and Gaussian precision. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingIndependentWick
open Function PowerSeries MeasureTheory FormalBulk08 Series Jets Wick Orb
open scoped Classical BigOperators
variable {V I : Type} [Fintype V] [DecidableEq V] (H : Hull V I)

def entry : V ⊕ I → MvPolynomial V (MvPolynomial I ℝ) :=
  Sum.elim (fun v => MvPolynomial.X v + MvPolynomial.C (H.drift v))
    (fun i => MvPolynomial.C (MvPolynomial.X i))

theorem entered (T : Pap (V ⊕ I)) :
    toInk H T = PowerSeries.map (MvPolynomial.aeval (entry H)).toRingHom T := by
  have h : fueled H = PowerSeries.C ∘ entry H := by
    funext i
    cases i <;> simp [fueled, entry, boost]
  rw [toInk, h, roam, const_insertAt, pure_map]

theorem centered (p : Pap (V ⊕ I)) (solved : Solved H p) :
    Orb.positive H p = toInk H (p-C (coeff 0 p)) := by
  change coeff 0 (toInk H p) = _ at solved
  calc
    _ = toInk H p - C (coeff 0 (toInk H p)) := by
      rw [solved]
      simp only [Orb.positive,boost,PowerSeries.map_C,map_add]
      abel
    _ = _ := by rw [entered,entered]; simp only [map_sub,PowerSeries.map_C,PowerSeries.coeff_map]

def observe (y : I→ℝ) (T : Ink V I) :=
  PowerSeries.map (MvPolynomial.map (MvPolynomial.eval y)) T

theorem direction (x : Rays V) (y : Rays I) (T : Pap (V ⊕ I)) :
    glimpse x (observe y (toInk H T)) =
      glimpse (Sum.elim (fun v => x v + traceP y (H.drift v)) y) T := by
  ext n
  rw [glimpse_coeff,observe,PowerSeries.coeff_map,entered,PowerSeries.coeff_map,glimpse_coeff]
  have h := Orb.toInk_value x y H (C (coeff n T))
  have dy : (MvPolynomial.aeval y).toRingHom = MvPolynomial.eval y := by
    ext i <;> simp
  simpa only [entered, PowerSeries.map_C,PowerSeries.coeff_zero_C, Orb.duplex_def,dy] using h

theorem covariance (y : I→ℝ) (T : Ink V I) :
    glimpse y (beam (variation H.saddle I).call T) =
      beam (Wick.moment H.saddle.q) (observe y T) := by
  ext n
  rw [glimpse_coeff,coeff_beam,coeff_beam,observe,PowerSeries.coeff_map]
  change MvPolynomial.eval y (Wick.moment _ (coeff n T)) = _
  rw [Wick.moment_map]
  have h : (fun i j => MvPolynomial.eval y ((variation H.saddle I).q i j)) = H.saddle.q := by
    funext i j
    change MvPolynomial.eval y (MvPolynomial.C (H.saddle.q i j)) = _
    rw [MvPolynomial.eval_C]
  rw [h]

theorem deposited (y : I→ℝ) (p q : Pap (V ⊕ I)) (solved : Solved H p) :
    let W := observe y (Series.expan (Orb.positive H p))
    let T := observe y (toInk H q)
    beam (Wick.moment H.saddle.q) W * glimpse y (Orb.flag H p q) =
      beam (Wick.moment H.saddle.q) (W*T) := by
  dsimp only
  have h := congrArg (glimpse y) (Orb.normalization H p solved q)
  rw [map_mul,vocal,covariance,covariance] at h
  simpa only [observe,map_mul] using h

theorem unit (y : I→ℝ) (p : Pap (V ⊕ I)) (solved : Solved H p) :
    coeff 0 (beam (Wick.moment H.saddle.q) (observe y (Series.expan (Orb.positive H p)))) = 1 := by
  rw [← covariance,glimpse_coeff]
  change traceP y (coeff 0 (vocal H p)) = 1
  rw [Orb.voice H p solved]
  exact map_one _

end YM.Integration.WilsonMovingIndependentWick
end
