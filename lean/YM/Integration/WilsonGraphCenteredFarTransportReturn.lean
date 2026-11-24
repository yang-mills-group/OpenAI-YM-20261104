import YM.Integration.WilsonGraphCenteredFarSeriesPrice
import YM.Integration.WilsonGraphCenteredFarWindowExpense

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredTransport

open Filter Real Growth Continuation
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev θ := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)

/-- On the elected fields, the reverse transport has an arbitrary absolute power on the
whole polynomial distance window. The cropped series is evaluated at the original near heater. -/
theorem onWindow (h m : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∀ᶠ k : ℕ in atTop, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      let f := r * exp s
      let t := θ.{u} g hg periods strict r
      let L := chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r f)
      let Uq := chairs g.core h (atColumn
        (AppointedCenteredReverse.reverseSeries (Z g hg) (Q.{u} g hg).MS h s) k t)
      ‖L-Uq‖ ≤ D * (gYM g.core r)^(m+1) := by
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨K, hK⟩ := exists_nat_gt B
  have actual : Tendsto (gYM g.core) (𝓝[>] (0:ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨shrink simple, positive_g simple⟩
  have edges := actual.eventually (G1.Wire.move C B hK hC)
  have heat := paid_reading simple (θ.{u} g hg periods strict)
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
  have toZero : Tendsto (fun r => (gYM g.core r)^(m+1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero m)] using (shrink simple).pow (m+1)
  have caps := ((AppointedPhysicalWindowAndPhase.earned.{u} g hg periods strict).main (m+1) h hC hB).2
  filter_upwards [AppointedCenteredWindow.paid.{u} g hg periods strict h m hC hB,
    eventually_ge_atTop (m+1+2+K*h)] with k forwardFee depth
  obtain ⟨D,hD,charge⟩ := AppointedCenteredSeriesPrice.defect
    (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching h k K (m+1) depth
  refine ⟨8+4*D, by positivity, ?_⟩
  filter_upwards [forwardFee, caps, edges, heat, actual.eventually charge,
    toZero.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with r raw bound inWindow heater expense small
  intro s hs upper f t L Uq
  let A := chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h f r)
  let Aq := chairs g.core h (atColumn (Kseries (Z g hg) (Q.{u} g hg).MS h (-s)) k t)
  have numerical := (raw s hs upper).1
  have close : ‖A - Aq‖ ≤ (gYM g.core r)^(m+1) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans numerical
  have filed := AppointedCenteredWindow.fields.{u} g hg periods strict h r s
  have bounded : ‖L‖ ≤ 2 := by
    change ‖chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r (r * exp s))‖ ≤ 2
    rw [← filed.2]
    exact (bound s hs upper).2
  have prod : ‖Aq * Uq - 1‖ ≤ D * (gYM g.core r)^(m+1) :=
    expense s (inWindow (exp s) (Real.one_le_exp_iff.mpr hs) upper) t heater.2.2.2
  have returned := (AppointedCenteredReverse.original.{u} g hg periods strict h k r s bounded).2.2
    (close.trans small.le)
  calc ‖L-Uq‖ ≤ 8*‖A-Aq‖+4*‖Aq*Uq-1‖ := returned
       _ ≤ 8*(gYM g.core r)^(m+1)+4*(D*(gYM g.core r)^(m+1)) :=
         add_le_add (mul_le_mul_of_nonneg_left close (by norm_num)) (mul_le_mul_of_nonneg_left prod (by norm_num))
       _ = (8+4*D)*(gYM g.core r)^(m+1) := by ring

end YM.FVA2.GradedFar.AppointedCenteredTransport

