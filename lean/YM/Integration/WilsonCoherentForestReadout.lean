import YM.Integration.WilsonCoherentForestMeasure
import YM.Integration.WilsonCoherentPivotContinuity

/-! Both fields in the signed comparison are Borel on a *single* sampled
forest with the actual common compact pivots. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentForestReadout
open Function Set MeasureTheory Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentReportingForest
open WilsonCoherentForestMeasure
open scoped Classical Topology

variable {G : Gauge} {c f: Side} {S: StepData c f}
variable (T:Forest S.ratio) (B:Finset T.Free)
local notation "E" => moving T B

def state (z : Sample T B G) := restored T B z.1 (Chart.expLinks G (↥E) z.2)

theorem restored_meas {Ω : Type*} [MeasurableSpace Ω]
    (v : Ω→Outer T B→G.El) (w : Ω→↥E→G.El) (mv : Measurable v) (mw : Measurable w) :
    Measurable (fun a=>restored T B (v a) (w a)) := by
  have bg : Measurable (fun a=>background T B (v a)) := by
    apply measurable_pi_lambda
    intro i
    by_cases h:internal T i.val
    · simp [background,h]
    · simpa only [background,dif_neg h,Function.comp_def] using (measurable_pi_apply (⟨pivot T i.val,saved T B i.val h⟩:Outer T B)).comp mv
  exact T.continuous_drape.measurable.comp ((cut T E).symm.measurable.comp ((mw.mul bg).prodMk mv))

theorem measurable_state : Measurable (state (G:=G) T B) :=
  restored_meas T B _ _ measurable_fst (Chart.expLinks_meas.comp measurable_snd)

variable (R : Run G) {I:Type} [Fintype I] (d:I→ℕ)

def polynomial (θ : ℝ) (y : ∀i,R.family.label (d i)) (o : I→Site f) (p : ℕ) (z:Sample T B G) : ℂ :=
  WilsonCoherentReportingPivot.row R d θ y o (restored T B z.1 1) (drift T B z.2) p 1

theorem measurable_drift : Measurable (fun z : Sample T B G=>drift T B z.2) := by
  apply measurable_pi_lambda
  intro e
  by_cases h:e∈T.trunks
  · simp [drift,h]
  · by_cases h':(⟨e,h⟩:T.Free)∈E
    · simpa only [drift,dif_neg h,dif_pos h',Function.comp_def] using (measurable_pi_apply (⟨⟨e,h⟩,h'⟩:↥E)).comp (measurable_snd (α:=Outer T B→G.El))
    · simp [drift,h,h']

theorem measurable_polynomial (θ : ℝ) (y : ∀i,R.family.label (d i)) (o : I→Site f) (p : ℕ) :
    Measurable (polynomial T B R d θ y o p) := by
  have mb : Measurable (fun z : Sample T B G =>restored T B z.1 1) :=
    restored_meas T B _ _ measurable_fst measurable_const
  have mz := measurable_drift (G:=G) T B
  change Measurable (fun z : Sample T B G =>∑ a, WilsonCoherentReportingFrame.charge R d θ y a *
    WilsonCoherentPivotStencil.row (WilsonCoherentReportingFrame.roster R d a)
      (restored T B z.1 1 ∘ legs (WilsonCoherentReportingFrame.roster R d a) o)
      (drift T B z.2 ∘ legs (WilsonCoherentReportingFrame.roster R d a) o) p 1)
  apply Finset.measurable_sum
  intro a _
  let J:=WilsonCoherentReportingFrame.roster R d a
  let loc:=legs J o
  have h₁ : Measurable (fun z:Sample T B G=>restored T B z.1 1 ∘ loc) :=
    measurable_pi_lambda _ fun i=>(measurable_pi_apply (loc i)).comp mb
  have h₂ : Measurable (fun z:Sample T B G=>drift T B z.2 ∘ loc) :=
    measurable_pi_lambda _ fun i=>(measurable_pi_apply (loc i)).comp mz
  exact ((WilsonCoherentPivotContinuity.row J p 1).measurable.comp (h₁.prodMk h₂)).const_mul _

end YM.Integration.WilsonCoherentForestReadout
