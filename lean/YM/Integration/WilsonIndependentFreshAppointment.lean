import YM.Integration.WilsonIndependentFreshScalar
import YM.Integration.WilsonIndependentFreshCoverWard

/-! The original calibrated Wick circuit supplies the vacuum, covariance,
predictor and moment estimates used for the older scalar. A compound group word is issued on the nonbare
quiet at capture, with its original positive-rank salary fixed there. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentFreshAppointment
open Lattice RG RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open scoped ENNReal Classical
variable {G : Gauge} {W : Type} {j : W → ℕ} {n : Page j → Side}
variable (S : Circuit j n) {K : KernelChoices} (Y : Oracle.Program K)
variable (branch : ∀ patch : Patch, patch.Branches K G) {color : G.ColorIndex}
variable {L : Meter W} {base capture stop : Choice j} {budget : Marked j}
variable {p m offset e moments : ℕ} {F : Tent j} {γ : ℝ}
local notation "world" => S.dialect Y G branch (sheet F)
local notation "quiet" => S.payroll Y G branch (sheet F)

/-- One compound insertion follows all the original dated conditional
moments, including every scalar produced by a nonconstant incident field. -/
theorem original (simple : G.Simple) (grade : quantum 1 0 ≤ moments)
    (book : SatisfiesQ G Y S branch budget p moments γ)
    (notebook : Notebook S Y G branch color base F p)
    (atBase : ∀ w, budget.peak (base.choose w) = 0)
    (mesh : ∀ w, S.l (base.choose w) = 1) (age : OfAge budget L)
    :
    ∃ seed : (world).Primitive L p (quantum 1 0),
    ∀ (m offset : ℕ) (capture stop : Choice j)
      (Z : (capture.after.part (world) (quiet) seed).Report m) (portrait : W → Portrait G),
      (∀ w, BasisT m offset (portrait w) (Z.main (Page.opening capture.after.spans w))) →
    ∀ (root : W → Room) (gross : W → ℝ), (∀ w, 0 ≤ gross w) →
      (∀ i, i ≤ p → ∀ r, 0 < r → Claim L
        (fun w => (world).coverQ root 2 (capture.choose w)) (fun w => ENNReal.ofReal (gross w))
        (fun w => Z.main (Page.opening capture.after.spans w) i r)) →
      capture.age ≤ stop.age → ∀ e, e ≤ p →
      ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ w,
        ‖note (Z.main (Page.finallyW capture.after.spans w) e 0) -
          note (Z.main ((WilsonIndependentFreshScalar.remaining capture stop).choose w) e 0)‖ ≤
          C * (L.val w).toReal^k * (gross w*(S.l (capture.choose w)/S.l (stop.choose w))^γ) := by
  obtain ⟨enrolled,lamp⟩ := Atlas.reservations S G Y branch atBase age book color notebook simple mesh
  let paid := enrolled.emits (b := 1) (u := 0) (by norm_num) grade
  refine ⟨paid.creators,?_⟩
  intro m offset capture stop Z portrait genuine root gross hg wage older e he
  have ward := WilsonIndependentFreshCoverWard.original _ (quiet) paid.port capture.after paid.creators Z
    paid.bulk paid.price portrait genuine (by norm_num [quantum]) paid.rates paid.inspiration
  exact WilsonIndependentFreshScalar.original (world) (quiet) paid.creators paid.bulk (paid.leads lamp)
    (by norm_num [quantum]) Z gross hg wage ward older he
end YM.Integration.WilsonIndependentFreshAppointment
