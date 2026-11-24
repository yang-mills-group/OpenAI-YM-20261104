import YM.Integration.WilsonMeasuredPublicEntranceCheapOrder
import YM.Integration.WilsonMeasuredOnlyHard

/-! The compensated peer product on the actual measured and canonical Wilson
hosts. The two forced bills of the signed return stay with their own gases. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCheapField
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Multi QuadraticLocal QuadraticLocal.Earn Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredCoefficientTransport WilsonThermometerUnitFilingFieldRange WilsonOriginalAlternativeHearing
open WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V : Type} {N p t b : ℕ} (d : V → ℕ)
variable (W : Rep G (R.family.side t p)) (same : W.eval=(R.family.path.rep N p t).eval)
    (o : V → Site (R.family.side t p))
    (X Y A B : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side t p))

def regular (R : Run G) (d : V → ℕ) {t p : ℕ}
    (W : Rep G (R.family.side t p)) (o : V → Site (R.family.side t p))
    (X : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side t p))
    (v : V) (U : Config G (R.family.side t p)) : ℂ :=
  (X v).exponentialEntry (o v) (R.family.localSection (d v)) W U

def charge (R : Run G) (d : V → ℕ) {t p : ℕ}
    (W : Rep G (R.family.side t p))
    (X : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side t p))
    (v : V) (U : Config G (R.family.side t p)) : ℂ := account (X v) W U

include same in
theorem original
    (sheet : ∀ v U, (X v).density (o v) (R.family.localSection (d v)) (R.family.path.rep N p t) U-(Y v).density (o v) (R.family.localSection (d v)) W U =
      (A v).density (o v) (R.family.localSection (d v)) (R.family.path.rep N p t) U+(B v).density (o v) (R.family.localSection (d v)) W U) (vs : List V) (U : Config G (R.family.side t p)) :
    let x := fun v => regular R d (R.family.path.rep N p t) o X v U
    let y := fun v => regular R d W o Y v U
    let e := fun v => regular R d (R.family.path.rep N p t) o A v U + regular R d W o B v U
    let hard := fun v => charge R d (R.family.path.rep N p t) X v U - charge R d W Y v U -
      charge R d (R.family.path.rep N p t) A v U - charge R d W B v U
    ((R.family.path.rep N p t).eval U:ℂ)*((vs.map x).prod-(vs.map y).prod) =
      ((R.family.path.rep N p t).eval U:ℂ)*route x (fun v => x v-e v) e vs -
        route y (fun v => x v-e v) hard vs := by
  apply WilsonMeasuredPublicEntranceCheapOrder.original
  intro v
  have h := sheet v U
  change _ * (_ - (_ - (_ + _))) = _ - _ - _ - _
  unfold regular charge
  simp only [Coefficient.density, account, same] at h ⊢
  linear_combination -h

def fare (R : Run G) (d : V → ℕ) {t p : ℕ} (W : Rep G (R.family.side t p))
    (X : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side t p))
    (v : V) (M : ℝ) : ℝ :=
  cost G (d v) W.p.threshold * (R.family.labels.level (d v)).coeffSize (X v).x + M

theorem heard (top : t ≤ N) (lower : b ≤ t)
    (κ₀ κ₁ M a z : V → ℝ)
    (px : ∀ v, (X v).remBound (o v) (R.family.path.rep N p t) (κ₀ v) (M v))
    (pa : ∀ v, (A v).remBound (o v) (R.family.path.rep N p t) (κ₀ v) (a v))
    (pb : ∀ v, (B v).remBound (o v) W (κ₁ v) (z v))
    (vs : List V) (T : Config G (R.family.side b p)) :
    let x := fun U v => regular R d (R.family.path.rep N p t) o X v U
    let e := fun U v => regular R d (R.family.path.rep N p t) o A v U + regular R d W o B v U
    let n := fun v => fare R d (R.family.path.rep N p t) X v (M v)
    let δ := fun v => fare R d (R.family.path.rep N p t) A v (a v) + fare R d W B v (z v)
    ‖held R.family N p (fun U => ((R.family.path.rep N p t).eval U:ℂ)*
      route (x U) (fun v => x U v-e U v) (e U) vs) lower T‖ ≤
      route n (fun v => n v+δ v) δ vs := by
  dsimp only
  rw [normalized R.family N p R.makes top _ lower]
  apply actualTransport_norm_le R.family R.makes top _ lower
  intro U
  have nz : ((R.family.path.rep N p t).eval U:ℂ) ≠ 0 := by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson top U).ne'
  simp only [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ nz, one_mul]
  apply price
  · intro v
    exact point R (d v) (R.family.path.rep N p t) (X v) (o v) (px v) U
  · intro v
    exact (norm_add_le ..).trans (add_le_add (point R (d v) (R.family.path.rep N p t) (A v) (o v) (pa v) U)
      (point R (d v) W (B v) (o v) (pb v) U))

end YM.Integration.WilsonMeasuredPublicEntranceCheapField
end
