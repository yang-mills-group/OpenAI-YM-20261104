import YM.Integration.WilsonGraphCenteredFarCropExpense
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPhysicalWindowAndPhase

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredWindow

open Filter Function Real PowerSeries Continuation Growth Moving
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (Z g hg) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.J
private abbrev θ := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)

/-- The two directions of the actual field map used in the long-window estimate. -/
theorem fields (h : ℕ) (r s : ℝ) :
    let f := r * exp s
    let transfer := AppointedCenteredReverse.transfer.{u} g hg periods strict h
    Zenith (Physical.next (H.{u} g hg periods strict) h) r s = chairs g.core h (transfer f r) ∧
    Zenith (Physical.next (H.{u} g hg periods strict) h) f (-s) = chairs g.core h (transfer r f) := by
  intro f transfer
  refine ⟨rfl, ?_⟩
  change chairs g.core h ((Physical.next (H.{u} g hg periods strict) h (r * exp s) (-s)).toLinearMap) = _
  rw [AppointedPhysicalWindowAndPhase.reverseAtWindow.{u} g hg periods strict h r s]
  rfl

/-- The earned forward field and clock price at arbitrary precision, with the true reverse crop invoice. -/
theorem paid (h m : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C * (gYM g.core r)^(-B) →
      let f := r * exp s
      let t := θ.{u} g hg periods strict r
      let transfer := AppointedCenteredReverse.transfer.{u} g hg periods strict h
      let A := chairs g.core h (transfer f r)
      let L := chairs g.core h (transfer r f)
      let a := Kseries (Z g hg) (Q.{u} g hg).MS h (-s)
      let b := AppointedCenteredReverse.reverseSeries (Z g hg) (Q.{u} g hg).MS h s
      let Aq := chairs g.core h (atColumn a k t)
      let Uq := chairs g.core h (atColumn b k t)
      ‖(θ.{u} g hg periods strict f : ℂ) - bend (Z g hg) (Q.{u} g hg).MS s k (t : ℂ)‖ +
        ‖A - Aq‖ ≤ (gYM g.core r)^(m+1) ∧
      ‖L - Uq‖ ≤ 8 * (gYM g.core r)^(m+1) + 4 * (|t|^(k+1) * ∑ q ∈ pairsAbove k,
        ‖chairs g.core h (coeff q.1 a)‖ * ‖chairs g.core h (coeff q.2 b)‖) := by
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  have bank := (AppointedPhysicalWindowAndPhase.earned.{u} g hg periods strict).main (m+1) h hC hB
  have heats := paid_reading simple (θ.{u} g hg periods strict)
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
  have toZero : Tendsto (fun r => (gYM g.core r)^(m+1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero m)] using (shrink simple).pow (m+1)
  filter_upwards [bank.1] with k estimate
  filter_upwards [estimate, bank.2, heats, toZero.eventually_lt_const (by norm_num : (0:ℝ)<1/4)]
    with r hr bounds heat small
  intro s hs upper f t transfer A L a b Aq Uq
  have maps := fields.{u} g hg periods strict h r s
  have raw := hr s hs upper
  have cap := bounds s hs upper
  have folded : Aq = crank (Z g hg) (Q.{u} g hg).MS h s k (t:ℂ) :=
    column_by a k t
  change ‖(θ.{u} g hg periods strict f:ℂ) - bend (Z g hg) (Q.{u} g hg).MS s k (t:ℂ)‖ +
    ‖Zenith (Physical.next (H.{u} g hg periods strict) h) r s -
      crank (Z g hg) (Q.{u} g hg).MS h s k (t:ℂ)‖ ≤ _ at raw
  rw [maps.1, ← folded] at raw
  have forward : ‖A - Aq‖ ≤ (gYM g.core r)^(m+1) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans raw
  have back : ‖L‖ ≤ 2 := by
    change ‖chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r (r * exp s))‖ ≤ 2
    rw [← maps.2]
    exact cap.2
  have reverse := (AppointedCenteredReverse.original.{u} g hg periods strict h k r s back).2.2
    (forward.trans small.le)
  have expense := AppointedCenteredCrop.original.{u} g hg periods strict h k r s heat.2.2.1
  refine ⟨raw, reverse.trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_left forward (by norm_num))
    (mul_le_mul_of_nonneg_left expense (by norm_num))

end YM.FVA2.GradedFar.AppointedCenteredWindow

