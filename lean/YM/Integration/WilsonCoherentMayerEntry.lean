import YM.Integration.WilsonCoherentMayerOccurrences
import YM.Integration.WilsonCoherentReportingFrame

/-! Genuine thresholded Wilson sections on original dormant regular addresses.
The scalar wallet is bought on the fixed section before the lattice size and
placements. Other occupied addresses and the ambient positive density are
those of the submitted representation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerEntry
open Function Finset MeasureTheory Lattice Wilson RG Source PhysicalNext.Repeat
open Legato Lotus RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical BigOperators
variable {G:Gauge} (run:Run G) {d:ℕ} {f:Side}

def unitPrice (d:ℕ) (a:(run.family.labels.level d).Index):ℝ :=
  max 1 (isCompact_univ.exists_bound_of_continuousOn
    (WilsonCoherentTerminalFrame.lamp run d a).regular.continuousOn).choose

theorem uniform (d:ℕ) (a:(run.family.labels.level d).Index) (x:Site f) (U:Config G f) :
    ‖Light (WilsonCoherentTerminalFrame.lamp run d a) f x U‖≤unitPrice run d a :=by
  have h:=(isCompact_univ.exists_bound_of_continuousOn
    (WilsonCoherentTerminalFrame.lamp run d a).regular.continuousOn).choose_spec
  exact (h (expandAt x U) (Set.mem_univ _)).trans (le_max_right ..)

def wallet (y:run.family.label d) (θ:ℝ) (χ:ℂ →L[ℝ] ℝ) :ℝ :=
  ‖χ‖*∑a,‖(run.family.labels.level d).scaled θ⁻¹ y a‖*unitPrice run d a

def raw (y:run.family.label d) (x:Site f) (θ:ℝ) (χ:ℂ →L[ℝ] ℝ) (U:Config G f):ℝ :=
  χ (Push.Local.presented (run.family.localSection d) x θ y U)

theorem bill (y:run.family.label d) (x:Site f) (θ:ℝ) (χ:ℂ →L[ℝ] ℝ) (U:Config G f) :
    ‖raw run y x θ χ U‖≤wallet run y θ χ :=by
  apply (χ.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [WilsonCoherentReportingFrame.arm]
  refine (norm_sum_le _ (fun a=>_)).trans (Finset.sum_le_sum fun a _=>?_ )
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (uniform run d a x U) (norm_nonneg _)

variable (A:Rep G f) (key:ℕ) (x:Site f) (y:run.family.label d) (χ:ℂ →L[ℝ] ℝ)
  (reaches:(run.family.localSection d).footprint x⊆(A.activities.reg key).support)
  (vacant:A.activities.E key=0)

def entered : Leaf A where
  turn := .logKey key
  ingredient := masked A.p.threshold (A.activities.reg key).support (raw run y x A.p.threshold χ)
  scopedR := by
    intro U V same flags
    change (A.activities.reg key).support∩RG.flags A.p.threshold U=
      (A.activities.reg key).support∩RG.flags A.p.threshold V at flags
    have hh : Healthy A.p.threshold (A.activities.reg key).support U ↔
        Healthy A.p.threshold (A.activities.reg key).support V := by
      unfold Healthy;rw [Finset.disjoint_iff_inter_eq_empty,flags,Finset.disjoint_iff_inter_eq_empty]
    by_cases good:Healthy A.p.threshold (A.activities.reg key).support U
    · rw [masked_eq _ _ _ _ good,masked_eq _ _ _ _ (hh.mp good)]
      apply congrArg χ
      exact (run.family.localSection d).placed_local _ _ U V
        (fun _ hi hj=>same _ (reaches hi) (reaches hj))
    · rw [masked_ne _ _ _ _ good,masked_ne _ _ _ _ (mt hh.mpr good)]
  grant :=by
    intro U read; by_contra bad; exact read (masked_ne _ _ _ _ bad)
  blank := vacant
  weight := wallet run y A.p.threshold χ
  earn :=by
    intro U;by_cases good:Healthy A.p.threshold (A.activities.reg key).support U
    · rw [masked_eq _ _ _ _ good];exact bill run y x _ χ U
    · rw [masked_ne _ _ _ _ good,norm_zero];exact (norm_nonneg _).trans (bill run y x _ χ U)
  glows :=by
    intro g U
    have hh : Healthy A.p.threshold (A.activities.reg key).support (gauge g U) ↔
        Healthy A.p.threshold (A.activities.reg key).support U :=by unfold Healthy;rw [gauge_flags]
    by_cases good:Healthy A.p.threshold (A.activities.reg key).support U
    · rw [masked_eq _ _ _ _ (hh.mpr good),masked_eq _ _ _ _ good]
      exact congrArg χ ((run.family.localSection d).placed_invariant (run.makes.sections d) x _ g U)
    · rw [masked_ne _ _ _ _ (mt hh.mp good),masked_ne _ _ _ _ good]
  borel := masked_measurable _ _ _ (χ.continuous.comp ((run.family.localSection d).continuous_places _ x)).measurable

theorem original (U:Config G f) :
    let m:=entered run A key x y χ reaches vacant
    m.turn=.logKey key ∧ m.weight=wallet run y A.p.threshold χ ∧
    (m.turn.qualifies A U→m.ingredient U=raw run y x A.p.threshold χ U ∧
      m.ingredient U=χ (Push.Local.primary (run.family.localSection d) x A.p.threshold y U)):=by
  refine ⟨rfl,rfl,fun good=>?_⟩
  change Healthy A.p.threshold (A.activities.reg key).support U at good
  change masked _ _ _ U=_ ∧ masked _ _ _ U=_
  rw [masked_eq _ _ _ _ good]
  refine ⟨rfl,?_⟩
  unfold raw
  apply congrArg χ
  exact (Push.Local.presented_primary x (Next.Foundations.sound G d) y U (Finset.disjoint_of_subset_left reaches good)).symm

end YM.Integration.WilsonCoherentMayerEntry
