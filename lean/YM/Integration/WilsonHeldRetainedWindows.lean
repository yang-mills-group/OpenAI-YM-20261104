import YM.Integration.WilsonHeldRefillMoment
import YM.Integration.OriginalMarkedGibbsRate

/-! The original local truncation can be used in the true conditional at any
interior reporting date. The action cost of inspecting a polynomial number of
sites is paid before all incoming ultraviolet cutoffs and periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldRetainedWindows
open Filter MeasureTheory Lattice Wilson RG OPE.Therm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open WilsonHeldRefillMoment Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "k" => (j+1)
local notation "fine" => Config G (R.family.side k per)
local notation "up" => R.family.path.rep N per k

/-- The retained action is exactly the one stamped on this original step. All
links outside the charged sites stay fixed throughout the redraw. -/
theorem physical {d : ℕ} (interior : k<N) (A : Comparison R (p:=per) interior d)
    (S : Support (R.family.side k per)) (saved : Set (Edge (Site (R.family.side k per))))
    (fixed : ∀ e : Edge (Site (R.family.side k per)), e.1 ∉ S → e ∈ saved)
    (f : fine → ℂ) (hf : Envelope f) :
    let P := approximation R (p:=per) interior d
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2 * regulatorRun R.family N per (k+1))^(d+1))
    Integrable (redraw R N per j saved P f) (scene R.family.path N per j) ∧
      (∫ V, ‖redraw R N per j saved P f V‖ ∂scene R.family.path N per j) ≤
        Real.exp a * ∫ U, ‖f U‖ ∂scene R.family.path N per k := by
  intro P a
  obtain ⟨c,hc,lo⟩ := OriginalMarkedGibbsAction.retained_floor R interior A
  let J (U : fine) := (remainder R (p:=per) interior d).additive (R.alloy.B.a.budget k) U
  have signed (X : fine) : -Real.log ((up).eval X) + Real.log (P.eval X) = J X := A.signed X
  have variation (U W : fine) (same : ∀ e ∈ saved, U e = W e) : |J U-J W| ≤ a := by
    have cost := OriginalMarkedLocalPurchase.run R interior A S U W (fun e h => same e (fixed e h))
    change |(-Real.log ((up).eval U) + Real.log (P.eval U)) - (-Real.log ((up).eval W) + Real.log (P.eval W))| ≤ a at cost
    rwa [signed U,signed W] at cost
  exact WilsonHeldRefillMoment.original R interior.le saved P
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hc lo J
    (OriginalMarkedRunCovariance.factor R interior A) variation f hf

private theorem geometric (simple : G.Simple) (interior : k<N)
    (d q : ℕ) (S : Support (R.family.side k per))
    (sites : (S.card:ℝ) ≤ R.family.path.levels.clock.hatBeta k^d)
    (small : regulatorRun R.family N per (k+1) ≤ 1) :
    (S.card:ℝ) * regulatorRun R.family N per (k+1)^(2*d+q+1) ≤ (2:ℝ)^d := by
  let x := R.family.path.levels.clock.hatBeta k
  let b := R.family.path.β N per (k+1)
  let g := regulatorRun R.family N per (k+1)
  have xp : 0 ≤ x := ((R.family.path.levels.fits.delayed k).le).trans' zero_le_one
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have rising : x ≤ R.family.path.levels.clock.hatBeta (k+1) := by
    change _ + G.slopeConstant * R.family.S.scale k ≤ _ + G.slopeConstant * R.family.S.scale (k+1)
    linarith only [mul_le_mul_of_nonneg_left ((OPE.scale_mono R.family.S).monotone (Nat.le_succ k))
      (Gauge.slopeConstant_pos simple).le]
  have dep : x/2 ≤ b := (div_le_div_of_nonneg_right rising (by norm_num)).trans (R.makes.wilson.represents N per (k+1) interior).band.1
  have xb : x ≤ 2*b := by linarith only [dep]
  have bp : 0 < b := Overlay.beta_positive R.makes.wilson interior
  have cash : g^2*b=1 := by
    change (Real.sqrt b)⁻¹^2*b=1
    rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  have two : x*g^2 ≤ 2 := (mul_le_mul_of_nonneg_right xb (sq_nonneg g)).trans_eq (by linarith only [cash])
  calc
    _ ≤ x^d * g^(2*d+q+1) := mul_le_mul_of_nonneg_right sites (pow_nonneg gp _)
    _ = (x*g^2)^d * g^(q+1) := by rw [show 2*d+q+1=2*d+(q+1) by omega,pow_add,pow_mul,mul_pow]; ring
    _ ≤ (2:ℝ)^d*1 := mul_le_mul (pow_le_pow_left₀ (mul_nonneg xp (sq_nonneg g)) two d)
      (pow_le_one₀ gp small) (pow_nonneg gp _) (by positivity)
    _ = _ := mul_one _

/-- A single grade of the real cutoff program works on every later regulator
and period. The observable need only pay its own true upper first moment. -/
theorem purchased (simple : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees : Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay) (d q : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (N per : ℕ) (interior : j+1<N)
      (S : Support (R.family.side (j+1) per)) (saved : Set (Edge (Site (R.family.side (j+1) per)))),
      (∀ e : Edge (Site (R.family.side (j+1) per)), e.1 ∉ S → e ∈ saved) →
      (S.card:ℝ) ≤ R.family.path.levels.clock.hatBeta (j+1)^d →
      ∀ (f : Config G (R.family.side (j+1) per) → ℂ), Envelope f →
        let P := approximation R (p:=per) interior (2*d+q+1)
        Integrable (redraw R N per j saved P f) (scene R.family.path N per j) ∧
          (∫ V, ‖redraw R N per j saved P f V‖ ∂scene R.family.path N per j) ≤
            Real.exp 1 * ∫ U, ‖f U‖ ∂scene R.family.path N per (j+1) := by
  let C : ℝ := 2^d
  have cp : 0 < C := by positivity
  have st := (tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees (2*d+q+1))
  have pay := (tendsto_add_atTop_nat 1).eventually (OriginalMarkedGibbsRate.charged R simple (2*d+q) C⁻¹ (inv_pos.mpr cp))
  obtain ⟨floor,hf⟩ := eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)
  filter_upwards [st,pay,eventually_ge_atTop floor] with j parts bill late N per interior S saved fixed sites f h fpt
  let g := regulatorRun R.family N per (j+1+1)
  let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a (j+1) S ((Real.sqrt 2*g)^(2*d+q+2))
  have grant := physical R interior (parts N per interior) S saved fixed f h
  have nonneg : 0≤a := OriginalMarkedLocalPurchase.fee_nonneg _ _ _ (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) _)
  have cut : g ≤ 1 := (hf _ (late.trans (by omega)) N per interior).le
  have geo := geometric R simple interior d q S sites cut
  have paid : 2*Real.exp 2*a ≤ C⁻¹*S.card*g^(2*d+q+1) := bill N per interior S
  have tiny : a ≤ 1 := by
    calc a ≤ 2*Real.exp 2*a := le_mul_of_one_le_left nonneg (by linarith [Real.add_one_le_exp (2:ℝ)])
         _ ≤ _ := paid
         _ ≤ C⁻¹*C := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left geo (inv_nonneg.mpr cp.le)
         _ = 1 := inv_mul_cancel₀ cp.ne'
  exact ⟨grant.1,grant.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr tiny) (integral_nonneg (fun _ => norm_nonneg _)))⟩

end YM.Integration.WilsonHeldRetainedWindows
