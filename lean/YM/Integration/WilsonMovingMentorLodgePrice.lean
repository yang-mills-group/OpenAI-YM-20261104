import YM.Integration.WilsonMovingMentorLodge
import YM.Integration.WilsonMovingLogCurrency

/-! The original analytic reserve at the physical lower budget, with its true
additive fee and its two rotated copies at the next measured temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorLodgePrice
open Filter Lattice Wilson Pressure RG RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AnalyticBridge.VerifiedReset.Collection Push.PriceCompiler AllOrder
open scoped Classical Topology
variable {G : Gauge} (R : Run G)

def amount (N per m : ℕ) : ℝ :=
  let u := R.alloy.B.a.clock.hatBeta (m+1)
  let i := R.alloy.B.a.clock.J m
  let y := u^(Shop.seam_hat i-1)
  turnFee (R.family.path.rep N per m).p * (y+y) + y

theorem total (rate : ℕ → ℝ) (held : WilsonMovingMentorLodge.Held rate R.kit)
    {N m : ℕ} (per : ℕ) (live : m ≤ N) :
    amount R N per m ≤ (R.alloy.B.a.clock.hatBeta (m+1))^(Shop.seam_hat (R.alloy.B.a.clock.J m)) := by
  let i := R.alloy.B.a.clock.J m
  let j := R.alloy.B.a.clock.J (m+1)
  let P := (R.family.path.rep N per m).p
  have budget : P = R.family.path.levels.budget m := (R.makes.wilson.represents N per m live).vac
  have order : P.order = (R.metals.p.profile i).order := by
    rw [budget]
    change (R.alloy.B.a.params m).order = _
    rw [params_eq R.alloy.B.valid]
  have power : P.power = (R.metals.p.profile i).power := by
    rw [budget]
    change (R.alloy.B.a.params m).power = _
    rw [params_eq R.alloy.B.valid]
  have entry := held.terms j _ (R.alloy.B.valid.pays m) i (step_paid R.alloy.B.a m)
  simpa only [amount, beta_eq R.alloy.B.valid m] using entry.total P order power

theorem measured (simple : G.Simple) (rate : ℕ → ℝ) (held : WilsonMovingMentorLodge.Held rate R.kit)
    {a ε : ℝ} (ha : 0 ≤ a) (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m < N →
      amount R N per m ≤ ε * (Pert.Asymptotics.regulatorRun R.family N per (m+1))^a := by
  let X := -(a/2 + 1)
  have hx : X < -(a/2) := by dsimp [X]; linarith
  obtain ⟨b,hb⟩ := exists_nat_ge (a/2)
  have warm := (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonMovingLogCurrency.physical R simple ha hx positive,
    R.family.path.levels.fits.deep.eventually_ge_atTop b,warm.eventually_ge_atTop (1:ℝ)] with
    m loan stage hot N per live
  have hb' : (b:ℝ) ≤ R.alloy.B.a.clock.J m := by exact_mod_cast stage
  have seam : Shop.seam_hat (R.alloy.B.a.clock.J m) ≤ X := by
    dsimp [Shop.seam_hat,X]
    linarith
  have nonnegative : 0 ≤ (R.alloy.B.a.clock.hatBeta (m+1))^X :=
    Real.rpow_nonneg (by change 1 ≤ R.alloy.B.a.clock.hatBeta (m+1) at hot; linarith) _
  calc amount R N per m ≤ _ := total R rate held per live.le
       _ ≤ (R.alloy.B.a.clock.hatBeta (m+1))^X := Real.rpow_le_rpow_of_exponent_le hot seam
       _ ≤ 7*(R.alloy.B.a.clock.hatBeta (m+1))^X := by linarith
       _ ≤ _ := loan N per live

end YM.Integration.WilsonMovingMentorLodgePrice
end
