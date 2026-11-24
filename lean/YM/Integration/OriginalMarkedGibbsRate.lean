import YM.Integration.OriginalMarkedGibbsCumulant
import YM.Integration.OriginalMarkedRowRate

/-! Cofinal connected marked error for a true local update under the same
complete measured exterior law. The selected clock pays the root summation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedGibbsRate
open Filter Lattice RG Wilson Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12
open OriginalMarkedRunAction OriginalMarkedGibbsCumulant Push.GridApprox.Attach GapsLocal.Renew
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {V : Type*} [Fintype V] [DecidableEq V] {J : Census V}

/-- The selected physical trajectory pays an arbitrary vanishing prefactor
for the entire charged interaction mass through a specified marked support. -/
theorem charged (hG : G.Simple) (q : ℕ) (v : ℝ) (hv : 0<v) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, m<N → ∀ S : Support (R.family.side m p),
      let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
      2*Real.exp 2*OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ((Real.sqrt 2*g)^(q+2)) ≤
        v*S.card*g^(q+1) := by
  let c := 4*Real.exp 2*(17:ℝ)^4*(Real.sqrt 2)^(q+2)
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [OriginalMarkedRowRate.shell_clock R hG (v/c) (div_pos hv hc)] with m shell N p hm S
  let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
  let K := hitConstant (((R.alloy.B.a.budget m).B+1)*OriginalMarkedLocalPurchase.width R.alloy.B.a)
  have kg : c*(K*g)≤v := by
    rw [mul_comm]
    exact (le_div_iff₀ hc).mp (shell N p hm)
  have g₀ : 0≤g := (IterationFour.Currency.g_pos R.makes N p (m+1) hm).le
  calc
    2*Real.exp 2*OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ((Real.sqrt 2*g)^(q+2))
        = c*(K*g)*S.card*g^(q+1) := by
      dsimp only [OriginalMarkedLocalPurchase.fee,c,K]
      rw [mul_pow,show g^(q+2)=g^(q+1)*g from pow_succ g (q+1)]
      ring
    _ ≤ v*S.card*g^(q+1) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right kg (Nat.cast_nonneg _)) (pow_nonneg g₀ _)

/-- At every requested order, one previous physical Run and one true
global exterior law control every signed insertion subset and partition.
The finite price is linear in the marked block and independent of period. -/
theorem purchased (hG : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (q : ℕ) (v : ℝ) (hv : 0<v) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ) (hm : m<N) (S : Support (R.family.side m p)) (s : J.Mode)
      (F : V → Config G (R.family.side m p)→ℂ) (b : V→ℝ),
      (∀ i,Measurable (F i)) → (∀ i,0≤b i) → (∀ i U,‖F i U‖≤b i) →
      ‖WilsonTagCumulantRate.coefficient s (ActualRunCoarseReadout.expectation R N p m) F-
        WilsonTagCumulantRate.coefficient s (refill R (p:=p) (d:=q+1) hm S) F‖ ≤
        v*S.card*(Pert.Asymptotics.regulatorRun R.family N p (m+1))^(q+1)*WilsonTagCumulantRate.slope s b := by
  filter_upwards [OriginalMarkedRunAction.calendar R hG marks fee (q+1),charged R hG q v hv] with
    m bought rate N p hm S s F b meas nonnegative bound
  exact (OriginalMarkedGibbsCumulant.connected R hm (bought N p hm) S s F b meas nonnegative bound).trans
    (mul_le_mul_of_nonneg_right (rate N p hm S) (WilsonTagCumulantRate.slope_nonneg s b nonnegative))

end YM.Integration.OriginalMarkedGibbsRate

