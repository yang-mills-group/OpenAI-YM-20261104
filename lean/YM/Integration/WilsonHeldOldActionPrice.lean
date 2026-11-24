import YM.Integration.WilsonHeldRetainedActionRate

/-! Centered log-action replacement, including rough upper configurations,
with the whole originally retained compatible forced activity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldOldActionPrice
open Filter Function Set MeasureTheory Lattice RG Wilson Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per k grade : ℕ} (live : k<N)
local notation "Q" => R.family.path.rep N per k
local notation "P" => approximation R (p:=per) live grade
local notation "A" => remainder R (p:=per) live grade
local notation "point" => R.alloy.B.a.budget k
local notation "g" => regulatorRun R.family N per (k+1)

theorem oscillation (proof : Comparison R (p:=per) live grade)
    (S : Support (R.family.side k per)) (U V : Config G (R.family.side k per))
    (agrees : OriginalMarkedLocalDifference.Outside S U V) :
    |(Real.log ((Q).eval U)-Real.log ((Q).eval V))-
      (Real.log ((P).eval U)-Real.log ((P).eval V))| ≤
      OriginalMarkedLocalPurchase.fee R.alloy.B.a k S ((Real.sqrt 2*g)^(grade+1)) := by
  have ratio (W : Config G (R.family.side k per)) :
      Real.log ((Q).eval W)-Real.log ((P).eval W) = -(A).additive point W := by
    have ident := congrArg Real.log (OriginalMarkedRunCovariance.factor R live proof W)
    unfold OriginalMarkedRunCovariance.weight at ident
    rw [Real.log_mul (OriginalMarkedRunCovariance.keep_positive R live proof W).ne'
      (Real.exp_pos _).ne',Real.log_exp] at ident
    linarith only [ident]
  have id : (Real.log ((Q).eval U)-Real.log ((Q).eval V))-
      (Real.log ((P).eval U)-Real.log ((P).eval V)) = -((A).additive point U-(A).additive point V) := by
    linarith only [ratio U,ratio V]
  rw [id,abs_neg]
  exact OriginalMarkedLocalDifference.variation (A) point proof.posterior.cut.regular proof.posterior.cut.boundE
    (OriginalMarkedLocalPurchase.width R.alloy.B.a) (OriginalMarkedLocalPurchase.width_pays R.alloy.B.a k)
    S U V agrees

theorem purchased (simple : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (money : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (d q grade : ℕ) (order : 2*d+q+1≤grade) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ j : ℕ in atTop, ∀ N per (hi : j+1<N) (S : Support (R.family.side (j+1) per)),
      (S.card : ℝ) ≤ R.family.path.levels.clock.hatBeta (j+1)^d →
      let Q₁ := R.family.path.rep N per (j+1)
      let P₁ := approximation R (p:=per) hi grade
      ∀ U V, OriginalMarkedLocalDifference.Outside S U V →
      |(Real.log (Q₁.eval U)-Real.log (Q₁.eval V))-(Real.log (P₁.eval U)-Real.log (P₁.eval V))| ≤
        ε*regulatorRun R.family N per (j+1)^q := by
  obtain ⟨k₀,after⟩ := eventually_atTop.mp (OriginalMarkedRunAction.calendar R simple marks money grade)
  filter_upwards [eventually_ge_atTop k₀,WilsonHeldRetainedActionRate.fee R simple d q grade order he]
    with j late fee N per hi S card Q₁ P₁ U V agrees
  let proof := after (j+1) (late.trans (Nat.le_succ j)) N per hi
  have h := oscillation R hi proof S U V agrees
  let value := OriginalMarkedLocalPurchase.fee R.alloy.B.a (j+1) S
    ((Real.sqrt 2*regulatorRun R.family N per (j+1+1))^(grade+1))
  have bound : Real.exp value-1 ≤ ε*regulatorRun R.family N per (j+1)^q := (fee N per hi S card).2
  have growth := Real.add_one_le_exp value
  have av : value ≤ ε*regulatorRun R.family N per (j+1)^q := by linarith only [bound,growth]
  exact h.trans av

end YM.Integration.WilsonHeldOldActionPrice
end
