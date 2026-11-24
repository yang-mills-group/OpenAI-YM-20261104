import YM.Integration.WilsonAddressedPublicFirstRoseBookedClock
import YM.Integration.WilsonIndependentCapturedDates
/-! The original moving financial window accepts any previously purchased
cofinal class of school dates and has two actual steps before the berth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseWindow
open Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato Analysis Table Spec Trace.Pilot
open WilsonReceivedChronologicalFixedCellFee (capture)
open WilsonAddressedPublicFirstRoseTicket (Receipt)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta

theorem cofinal (simple:G.Simple){n:ℕ}(φ:Test n)(A floor:ℕ):
    ∀ᶠr:ℝ in trail,∀first K:ℕ,capture R φ r≤K →
      σ K-σ first ≤ (A:ℝ)*(1+Real.log (H (first+1))) → floor≤first:=by
  let ceiling:=σ floor+(A:ℝ)*(1+Real.log (H (floor+1)))
  have late:=R.family.S.divergent.comp (WilsonAddressedPublicFirstRoseMovingDate.cofinal R φ)
  filter_upwards [late.eventually_gt_atTop ceiling] with r passed
  intro first K coarse clock
  have large:ceiling < σ K:=passed.trans_le ((WilsonIndependentCapturedDates.increasing R).monotone coarse)
  by_contra! early
  have paid:Real.log (H (first+1))≤Real.log (H (floor+1)):=Real.log_le_log
    (zero_lt_one.trans (R.family.path.levels.fits.delayed _))
    (WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.succ_le_succ early.le))
  dsimp [ceiling] at large
  linarith only [clock,large,(WilsonIndependentCapturedDates.increasing R).monotone early.le,
    mul_le_mul_of_nonneg_left (add_le_add_left paid 1) (Nat.cast_nonneg (α:=ℝ) A)]

theorem original (simple:G.Simple){n:ℕ}(φ:Test n){School:ℕ→Prop}(enrolled:∀ᶠm in atTop,School m)(A:ℕ):
    ∀ᶠr:ℝ in trail,∀first f K:ℕ,∀hi lo θ:ℝ,capture R φ r≤f → f<K →
      Receipt R hi lo r θ first f K (capture R φ r) A → School first ∧ first+1≤K-2 ∧ K-2+1+1=K:=by
  obtain ⟨floor,school⟩:=eventually_atTop.mp enrolled
  filter_upwards [cofinal R simple φ A floor] with r after
  intro first f K hi lo θ cf fk ticket
  have small:8*R.family.S.a f < R.family.S.a (first+1):=ticket.refined.trans_le
    ((mul_le_mul_of_nonneg_right ((min_le_left hi lo).trans (le_max_left hi lo)) ticket.positive.le).trans ticket.coarse)
  have gap:R.family.S.a f < R.family.S.a (first+1):=by linarith only [small,R.family.S.a_pos f]
  have ages:first+1<f:=by
    by_contra! reverse
    exact gap.not_ge (R.family.S.strictAnti.antitone reverse)
  exact ⟨school first (after first K (cf.trans fk.le) ticket.span),by omega,by omega⟩

end YM.Integration.WilsonAddressedPublicFirstRoseWindow
end
