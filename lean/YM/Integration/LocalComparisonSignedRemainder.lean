import YM.Integration.LocalComparisonBlockSupport
import YM.Integration.LocalComparisonReclosure
import YM.Integration.ActualNormalizedPush
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! The literal signed remainder of an actual conditional step.

The source below is defined before any reclosure representation is chosen.
Its multiplicative identity uses the full prescribed packet and the original
coarse vacuum, including at a zero of that vacuum. Normalization and the
connected identity are then justified on the actual positive history.

No estimate or represented regular/forced envelope is asserted here. In
particular the connected identity does not commute a logarithm with an
integral, or remove the field dependence of the conditional denominator.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
    (C : Family G) (N period level : ℕ)

/-- Remove the same formal packet multiplicatively from the actual full
push, then subtract exactly the original unmarked coarse density. -/
def actualSignedRemainder
    (F : TestSpace D → Config G (C.side (level + 1) period) → Poly R)
    (model : MarkedPackets D G (C.side level period) R)
    (x : TestSpace D) (U : Config G (C.side level period)) : Poly R :=
  Poly.pass (-(model.read x
      (Pert.Asymptotics.regulatorRun C N period (level + 1)) U)) *
      actualPush C N period level (F x) U -
    ((C.path.rep N period level).eval U : ℂ) • (1 : Poly R)

variable {C N period level}
    (F : TestSpace D → Config G (C.side (level + 1) period) → Poly R)
    (model : MarkedPackets D G (C.side level period) R)

/-- The complete physical-minus-formal numerator is the formal multiplier
times this one signed remainder. No nonvanishing assumption is used. -/
theorem actualSignedRemainder_factor (x : TestSpace D)
    (U : Config G (C.side level period)) :
    actualPush C N period level (F x) U -
        Poly.pass (model.read x
          (Pert.Asymptotics.regulatorRun C N period (level + 1)) U) *
          (((C.path.rep N period level).eval U : ℂ) • (1 : Poly R)) =
      Poly.pass (model.read x
        (Pert.Asymptotics.regulatorRun C N period (level + 1)) U) *
        actualSignedRemainder C N period level F model x U := by
  have hi := Next.Rank.Exponential.pass_neg
    (model.read x (Pert.Asymptotics.regulatorRun C N period (level + 1)) U)
    (model.quiet_read x _ U)
  rw [actualSignedRemainder, mul_sub, ← mul_assoc,
    mul_comm (Poly.pass (model.read x _ U))
      (Poly.pass (-(model.read x _ U))), hi, one_mul]

/-- A literal factorization identifies the deterministic remainder; it
does not choose a new representation or infer a smallness estimate. -/
theorem actualSignedRemainder_of_factor
    (E : TestSpace D → Config G (C.side level period) → Poly R)
    (h : ∀ x U, actualPush C N period level (F x) U =
      Poly.pass (model.read x
        (Pert.Asymptotics.regulatorRun C N period (level + 1)) U) * E x U)
    (x : TestSpace D) (U : Config G (C.side level period)) :
    actualSignedRemainder C N period level F model x U =
      E x U - ((C.path.rep N period level).eval U : ℂ) • (1 : Poly R) := by
  rw [actualSignedRemainder, h, ← mul_assoc,
    Next.Rank.Exponential.pass_neg _ (model.quiet_read x _ U), one_mul]

variable (hC : C.Makes) (hl : level < N)
include hC hl

/-- Normalize only after the actual history supplies strict positivity.
The same field-dependent denominator remains in both terms. -/
theorem actualSignedRemainder_normalized (x : TestSpace D)
    (U : Config G (C.side level period)) :
    normalized C N period level (actualSignedRemainder C N period level F model x) U =
      Poly.pass (-(model.read x
        (Pert.Asymptotics.regulatorRun C N period (level + 1)) U)) *
        normalized C N period level (actualPush C N period level (F x)) U - 1 := by
  have hρ := (Multi.AxisShift.chosen_positive hC.wilson hl.le U).ne'
  change ((C.path.rep N period level).eval U)⁻¹ •
      (Poly.pass (-(model.read x _ U)) * actualPush C N period level (F x) U -
        ((C.path.rep N period level).eval U : ℂ) • (1 : Poly R)) = _
  rw [smul_sub, ← mul_smul_comm, Complex.coe_smul, smul_smul,
    inv_mul_cancel₀ hρ, one_smul]
  rfl

theorem actualSignedRemainder_normalized_factor (x : TestSpace D)
    (U : Config G (C.side level period)) :
    normalized C N period level (actualPush C N period level (F x)) U =
      Poly.pass (model.read x
        (Pert.Asymptotics.regulatorRun C N period (level + 1)) U) *
        (1 + normalized C N period level
          (actualSignedRemainder C N period level F model x) U) := by
  rw [actualSignedRemainder_normalized F model hC hl]
  rw [← add_sub_assoc, add_sub_cancel_left, ← mul_assoc,
    mul_comm (Poly.pass (model.read x _ U)) (Poly.pass (-(model.read x _ U))),
    Next.Rank.Exponential.pass_neg _ (model.quiet_read x _ U), one_mul]

/-- Integrability of the full original input justifies extracting its quiet
coefficient through the actual push. The vacuum is then the selected
history's own exact step, rather than a separate denominator receipt. -/
theorem actualPush_quiet
    (A : Config G (C.side (level + 1) period) → Poly R)
    (hA : Integrable A (prior G _))
    (hq : ∀ W, (A W).part R.quiet =
      ((C.path.rep N period (level + 1)).eval W : ℂ))
    (U : Config G (C.side level period)) :
    (actualPush C N period level A U).part R.quiet =
      ((C.path.rep N period level).eval U : ℂ) := by
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  have hI := StepData.push_slice (C.path.levels.transition_mass level period β) U A hA
  change (Poly.get R.quiet) (∫ W, K.density β W U • A W ∂prior G _) = _
  rw [← (Poly.get R.quiet).integral_comp_comm hI]
  have he : (fun W => (Poly.get R.quiet) (K.density β W U • A W)) =
      (fun W => ((K.density β W U * (C.path.rep N period (level + 1)).eval W : ℝ) : ℂ)) := by
    funext W
    change K.density β W U • (A W).part R.quiet = _
    rw [hq, Complex.real_smul, Complex.ofReal_mul]
  rw [he]
  have hVac := ((C.path.rep N period (level + 1)).envelope
    (hC.wilson.represents N period (level + 1) hl).good).integrable (prior G _)
  have hVI := StepData.push_slice (C.path.levels.transition_mass level period β)
    U (C.path.rep N period (level + 1)).eval hVac
  have hVC := Complex.ofRealCLM.integral_comp_comm hVI
  simp only [Complex.ofRealCLM_apply, smul_eq_mul] at hVC
  rw [hVC]
  exact congrArg (fun a : ℝ => (a : ℂ))
    (congr_fun (hC.wilson.steps N period level hl).1 U).symm

theorem actualNormalizedPush_quiet
    (A : Config G (C.side (level + 1) period) → Poly R)
    (hA : Integrable A (prior G _))
    (hq : ∀ W, (A W).part R.quiet =
      ((C.path.rep N period (level + 1)).eval W : ℂ))
    (U : Config G (C.side level period)) :
    (normalized C N period level (actualPush C N period level A) U).part R.quiet = 1 := by
  have hρ := (Multi.AxisShift.chosen_positive hC.wilson hl.le U).ne'
  change ((C.path.rep N period level).eval U)⁻¹ •
    (actualPush C N period level A U).part R.quiet = 1
  rw [actualPush_quiet hC hl A hA hq, Complex.real_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hρ]
  rfl

omit hC hl in
private theorem connected_factor (M E : Poly R)
    (hM : M.part R.quiet = 0) (hE : E.part R.quiet = 1) :
    Extra.Trajectories.connected (Poly.pass M * E) =
      M + Extra.Trajectories.connected E := by
  have hF : (Poly.pass M * E).part R.quiet = 1 := by
    rw [Poly.quiet_mul, Poly.pass_part M hM, hE, one_mul]
  apply Extra.Trajectories.pass_inj (Extra.Trajectories.connected_quiet hF)
  · change M.part R.quiet + (Extra.Trajectories.connected E).part R.quiet = 0
    rw [hM, Extra.Trajectories.connected_quiet hE, zero_add]
  · rw [Extra.Trajectories.pass_connected hF,
      Extra.Trajectories.pass_add hM (Extra.Trajectories.connected_quiet hE),
      Extra.Trajectories.pass_connected hE]

/-- The connected comparison is the logarithm of one normalized signed
remainder. The complete input is integrated first; the actual denominator
stays inside the resulting field-dependent polynomial. -/
theorem actualSignedRemainder_connected
    (hF : ∀ x, Integrable (F x) (prior G _))
    (hq : ∀ x W, (F x W).part R.quiet =
      ((C.path.rep N period (level + 1)).eval W : ℂ))
    (x : TestSpace D) (U : Config G (C.side level period)) :
    Extra.Trajectories.connected
        (normalized C N period level (actualPush C N period level (F x)) U) -
      model.read x (Pert.Asymptotics.regulatorRun C N period (level + 1)) U =
      Extra.Trajectories.connected (1 + normalized C N period level
        (actualSignedRemainder C N period level F model x) U) := by
  have hA := actualNormalizedPush_quiet hC hl (F x) (hF x) (hq x) U
  have hE : (1 + normalized C N period level
      (actualSignedRemainder C N period level F model x) U).part R.quiet = 1 := by
    rw [actualSignedRemainder_normalized F model hC hl]
    rw [← add_sub_assoc, add_sub_cancel_left, Poly.quiet_mul,
      Poly.pass_part (-(model.read x _ U)) (by
        change -(model.read x _ U).part R.quiet = 0
        rw [model.quiet_read, neg_zero]), hA, one_mul]
  rw [actualSignedRemainder_normalized_factor F model hC hl,
    connected_factor _ _ (model.quiet_read x _ U) hE]
  abel

omit hC hl
section Reclosure
open Comparison.RG02

variable {Y : Bulk.Chain C.path} {datum : LocalFormal.Datum C R}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {inputCarrier : Carrier C datum.cutoff datum.period (datum.level + 1)}
    {fineRoots : V → Site (C.side (datum.level + 1) datum.period)}
    {coarseRoots : V → Site (C.side datum.level datum.period)}
    {input : Taste (TestSpace D) fineRoots inputCarrier.rep R}
    {inputPackets : MarkedPackets D G (C.side (datum.level + 1) datum.period) R}
    {inputRadii inputKernelCosts : V → ℝ} {inputForcedPrice : ℝ}
    {packets : MarkedPackets D G (C.side datum.level datum.period) R}
    {order forcedOrder : ℕ} {p : BudgetPoint} {w kernelCosts : V → ℝ}
    {delta constant geometry inherited calibration nextRegular nextForced : ℝ}
    {addresses : V → Support (C.side datum.level datum.period)}
    (H : MarkedReclosure Y datum inputColors inputCarrier fineRoots coarseRoots input
      inputPackets inputRadii inputKernelCosts inputForcedPrice packets order forcedOrder p w
      kernelCosts delta constant geometry inherited calibration nextRegular nextForced addresses)

/-- Every actual reclosure represents this already-defined signed source.
The conclusion uses its original carrier vacuum and keeps the entire
residual density, including all mixed forced products. -/
theorem MarkedReclosure.actualSignedRemainder (x : TestSpace D)
    (U : Config G (C.side datum.level datum.period)) :
    actualSignedRemainder C datum.cutoff datum.period datum.level
        (fun x => (input.leaf x).density) packets x U =
      (H.residual.leaf x).density U -
        (H.carrier.rep.eval U : ℂ) • (1 : Poly R) := by
  have he := actualSignedRemainder_of_factor
    (C := C) (N := datum.cutoff) (period := datum.period) (level := datum.level)
    (fun x => (input.leaf x).density) packets (fun x => (H.residual.leaf x).density)
    (fun x U => (congr_fun (H.exact.density x) U).trans (H.full x U)) x U
  rw [← congr_fun H.carrier.vacuum U] at he
  exact he

end Reclosure
end YM.Integration.LocalComparison
