import YM.Integration.WilsonMatrixTicketLanesReportedOneBlock

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedSettlement
open Function Filter FVA2 OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedOneBlock
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)
variable {I : Type} [Fintype I]

/-- The original one-block Haar numerator, including the common vacuum denominator,
of the actual freshly registered physical source. -/
def fresh (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (b N p : ℕ)
    (atStage : L.level r = b+1) (u : Directions G (R.family.side b p))
    (o : I → Site (R.family.side (L.level r) p)) : ℂ :=
  let m := L.level r
  let D := step R p atStage
  let g := regulatorRun R.family N p m
  (Spool.spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V => bare (g⁻¹^2) V •
    ∏ i,R.family.O m p (center R m N p (atRef L (d i) r (N,p) (w i))) (o i) V) (Parcel.Oven.slice u g)

/-- Apply the same compensated physical stencil to the filed scalar word values. -/
def priced (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (N p : ℕ)
    (v : (∀ i,(R.family.labels.level (d i)).Index) → ℂ) : ℂ :=
  ∑ j,(∏ i,WilsonMatrixTicketLanesReportedMaster.color R (d i) (L.level r) N p
    (L.shift (d i) r (w i)) (j i)) * v j

/-- Assemble the numerical original word estimates after all signs, centers and
different engineering degrees have been fixed on the same group fields. -/
theorem measured (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (b N p : ℕ)
    (atStage : L.level r = b+1) (age : ∀ i,R.family.ref (d i) ≤ L.level r)
    (future : L.level r ≤ N) (u : Directions G (R.family.side b p))
    (o : I → Site (R.family.side (L.level r) p))
    (v : (∀ i,(R.family.labels.level (d i)).Index) → ℂ) (ε : ℝ) (pos : 0 ≤ ε)
    (bought : ∀ j, ‖Spool.reads (fun i=>WilsonCoherentTerminalFrame.lamp R (d i) (j i))
      (step R p atStage) u o (regulatorRun R.family N p (L.level r)) - v j‖ ≤ ε) :
    ‖fresh R F L r d w b N p atStage u o - priced R F L r d w N p v‖ ≤
      (∏ i,(2:ℝ)^(d i)*mass R.family (d i) (L.shift (d i) r (w i))) * ε := by
  let c (j : ∀ i,(R.family.labels.level (d i)).Index) := ∏ i,
    WilsonMatrixTicketLanesReportedMaster.color R (d i) (L.level r) N p (L.shift (d i) r (w i)) (j i)
  let x (j : ∀ i,(R.family.labels.level (d i)).Index) :=
    Spool.reads (fun i=>WilsonCoherentTerminalFrame.lamp R (d i) (j i)) (step R p atStage) u o
      (regulatorRun R.family N p (L.level r))
  have physical : fresh R F L r d w b N p atStage u o = ∑ j,c j*x j :=
    WilsonMatrixTicketLanesReportedOneBlock.original R F L r d w b N p atStage age future u o
  rw [physical]
  change ‖(∑ j,c j*x j) - ∑ j,c j*v j‖ ≤ _
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  calc
    _ ≤ ∑ j,‖c j*(x j-v j)‖ := norm_sum_le _ _
    _ ≤ ∑ j,‖c j‖*ε := Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bought j) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonMatrixTicketLanesReportedPlatedBank.cost R F L r d w N p future) pos

end YM.Integration.WilsonMatrixTicketLanesReportedSettlement
