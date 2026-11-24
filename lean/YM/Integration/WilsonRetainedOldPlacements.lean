import YM.Integration.WilsonRetainedFiledVacuum
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming

/-! Occupied placements of the filed old action in the same compact Wilson numerator.
The parameter counts occurrences of old vertices. The measured coupling remains fixed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedOldPlacements
open Function Filter Lattice Laurent Bloch Wilson RG RG.Supply Precision Exterior Tree
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open IterationFour IterationFour.Vacuum Comparison.RG02 Marker WilsonLimitConstruction
open ConnectedActivityE6.Coat OriginalMarkedRunAction
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] {Γ : Census V} (R : Run G)
variable {J : Request V} {A : NumericSchedule R.family J}
variable {d : LocalFormal.Datum R.family Γ} (F : FundedSpringFineInlet.Inlet J A d)
variable (Z : SeriesA G) {σ C : ℝ} (D : RunFundedPeriodAction.PeriodData Z J.order σ C)
local notation "P₀" => FundedSpringPeriodPlan.plan R F Z σ C D
local notation "n₀" => R.family.side d.level d.period
local notation "Y" => R.family.path.rep d.cutoff d.period d.level
set_option quotPrecheck false in
local notation "B₀" => (R.family.path.levels.params d.level).clip
local notation "α₀" => R.alloy.B.kin.alpha d.cutoff d.level

/-- The quadratic normalization and every signed filed curvature at this site. -/
def vertex (g : ℝ) (x : Site n₀) (U : Config G n₀) : ℝ :=
  α₀ * secondAt (B₀) (Y).path x U + springAt R d.cutoff d.period d.level J.order Z g x U

theorem filed (simple : G.Simple) (g : ℝ) (U : Config G n₀) :
    WilsonRetainedFiledVacuum.filed R (P₀) d.level g U =
      ∑ x : Site n₀, vertex R (J:=J) (d:=d) Z g x U := by
  have h := filed_sites R F Z D g U
  have b := (bare_sites (B₀) (Y).path U).1
  unfold WilsonRetainedFiledVacuum.filed
  dsimp only
  rw [actual_pitch R simple (P₀) d.below g]
  change (α₀)*secondTerm (B₀) (Y).path U + springReading R (P₀) d.level g U = _
  rw [h,b,Finset.mul_sum]
  simp only [vertex,Finset.sum_add_distrib]

/-- The ungraded part of the original numerator. The old vacuum difference and
the original gas are retained as fields on the same compact configuration. -/
def base (g : ℝ) (U : Config G n₀) : ℝ :=
  Real.exp ((Y).v * Fintype.card (Site n₀) - (Y).path.inChannels (Y).clip (Y).p (Y).beta U -
    ((Y).activities.additive (Y).p U - WilsonRetainedFiledVacuum.filed R (P₀) d.level g U)) *
    (Y).activities.gas (Y).p U

/-- Each selected old occurrence is placed in the same physical configuration. -/
def weight (g : ℝ) (U : Config G n₀) (t : ℝ) : ℝ :=
  base R F Z D g U * Real.exp (t * ∑ x : Site n₀, -vertex R (J:=J) (d:=d) Z g x U)

theorem original (simple : G.Simple) (g : ℝ) (U : Config G n₀) :
    weight R F Z D g U 1 = (Y).eval U := by
  unfold weight base Rep.eval Rep.exponent
  rw [Finset.sum_neg_distrib, ←filed R F Z D simple g U,one_mul]
  rw [mul_right_comm,←Real.exp_add]
  congr 2
  ring

/-- The complete, field-dependent compact kernel and signed test are shared by
all occurrences, including repeated placements at the same root. -/
theorem coefficients {c : Side} (S : StepData c n₀) (held : Config G c)
    (φ : Config G n₀ → Config G c → ℂ) (g : ℝ) (U : Config G n₀) (k : ℕ) :
    let a := fun x : Site n₀ => -vertex R (J:=J) (d:=d) Z g x U
    let v := base R F Z D g U * S.density (Y).beta U held
    ((v * (∑ x, a x)^k : ℝ) : ℂ) * φ U held =
      ∑ s : Fin k → Site n₀, ((v * ∏ i : Fin k, a (s i) : ℝ) : ℂ) * φ U held := by
  intro a v
  have words : (∑ x, a x)^k = ∑ s : Fin k → Site n₀, ∏ i : Fin k, a (s i) := by
    simpa using (Fintype.prod_sum (fun (_ : Fin k) (x : Site n₀) => a x))
  rw [words,Finset.mul_sum,Complex.ofReal_sum,Finset.sum_mul]

private theorem expDerivative (b a : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ => b * Real.exp (u*a)) t =
      (b*a^k) * Real.exp (t*a) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,funext ih]
    have ha : HasDerivAt (fun u : ℝ => u*a) a t := by
      simpa using (hasDerivAt_id t).mul_const a
    rw [(ha.exp.const_mul (b*a^k)).deriv,pow_succ]
    ring

/-- Derivatives of the unnormalized numerator count the ordered old
occurrences. The exterior field, the original tag law and the signed test
are shared by the entire derivative. -/
theorem graded {c : Side} (S : StepData c n₀) (held : Config G c)
    (φ : Config G n₀ → Config G c → ℂ) (g : ℝ) (U : Config G n₀) (k : ℕ) :
    let a := fun x : Site n₀ => -vertex R (J:=J) (d:=d) Z g x U
    let v := base R F Z D g U * S.density (Y).beta U held
    ((iteratedDeriv k (weight R F Z D g U) 0 * S.density (Y).beta U held : ℝ) : ℂ) *
      φ U held =
      ∑ s : Fin k → Site n₀, ((v * ∏ i : Fin k, a (s i) : ℝ) : ℂ) * φ U held := by
  intro a v
  have h := coefficients R F Z D S held φ g U k
  dsimp only at h
  unfold weight
  rw [expDerivative]
  simp only [zero_mul,Real.exp_zero,mul_one]
  rw [mul_right_comm]
  exact h

end YM.Integration.WilsonRetainedOldPlacements
