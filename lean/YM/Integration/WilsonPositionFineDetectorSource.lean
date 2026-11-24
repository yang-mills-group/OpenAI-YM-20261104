import YM.Integration.WilsonOriginalPositionFineScheme

/-! The signed scalar at the finer bare temperature can be heard on the native seven
moment faces. Coefficient extraction follows the joint product of the proper
moments on its own finite mesh, before integration against the position test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionFineDetectorSource
open RG17 Trace.Pilot PhysMS Climb
open Filter Finset PowerSeries Lattice Wilson RG Extraction Spec XSpace XSpace.Retirement
open XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register
open PhysicalNext.Repeat.Legato WilsonPositionRawMesh
open scoped Topology BigOperators Classical
variable {G:Gauge} (Z : WilsonPrescription G)

def faces (m : Mesh) (q : ℕ) (u:ℝ) : ℝ :=
  ∑ k:Fin (q+1), (Deposit m (fun x => coeff (k:ℕ)
    (Rose.b3 (Rose.batchT (Rose.cooked Z.scheme Z.store 6 x)))) (Rose.test Z.criterion)).re * u^(k:ℕ)

theorem finite (m : Mesh) (paid : Z.store.Meets Z.scheme m 6) (q:ℕ) (u:ℝ) :
    forward Z m q u = faces Z m q u / Rose.cT Z.criterion.cut G Z.criterion.image := by
  let D := Rose.Detector Z.scheme Z.criterion m
  let c := Rose.cT Z.criterion.cut G Z.criterion.image
  have empty : coeff 0 D=0 := by
    have h := congrArg (coeff 0) (Rose.prepared_odd Z.scheme Z.criterion m paid)
    rw [Rose.inversion,coeff_rescale,map_neg,pow_zero,one_mul] at h
    change coeff 0 D = -coeff 0 D at h
    linear_combination h/2
  have weighs (k:ℕ) : coeff k (Rose.chosen Z.scheme Z.criterion m) = ((c:ℂ)⁻¹)*coeff k D := by
    obtain h|h := eq_or_ne k 0
    · rw [h,empty,mul_zero,coeff_zero_eq_constantCoeff_apply,Rose.zero_choice]
    · exact Rose.puts Z.scheme Z.criterion m k h
  rw [WilsonPositionRawMesh.forward,faces,Finset.sum_div]
  apply sum_congr rfl
  intro k _
  have term := Rose.detector Z.scheme Z.criterion m (k:ℕ)
  change coeff (k:ℕ) D = Deposit m (fun x => coeff (k:ℕ)
    (Rose.b3 (Rose.batchT (Rose.cooked Z.scheme Z.store 6 x)))) (Rose.test Z.criterion) at term
  rw [← term]
  change (coeff (k:ℕ) (Rose.chosen Z.scheme Z.criterion m)).re * u^(k:ℕ) =
    (coeff (k:ℕ) D).re * u^(k:ℕ)/c
  rw [weighs,←Complex.ofReal_inv,Complex.re_ofReal_mul]
  ring

theorem scheduled {R:Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F:Final R.family f S) (J:ℝ→PhysMS.tower S)
    (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6) (hG : G.Simple)
    {B:ℕ} (hB:0<B)
    (fine index:ℝ→ℕ) (dates : WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=hG) (B:=B) Z fine index) :
    ∀ᶠ r in trail, ∀ (q:ℕ) (u:ℝ) (z:ℕ×ℕ) (bound:ℝ),
    |WilsonPositionRawCutoff.thermometer Z F J A r z-forward Z (Z.run.step (index r)) q u| ≤ bound ↔
    |(WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A r z).re-
      faces Z (Z.run.step (index r)) q u| ≤ bound*|Rose.cT Z.criterion.cut G Z.criterion.image| := by
  let m:=WilsonMeasuredWindow.stop R.family.path.levels hG B
  let Λ:=WilsonPositionAuxiliaryReporterCalendar.scale R hG (B:=B)
  have inlet := (goesFront (Expense.Stretched.runs Z.run)).eventually
    (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2
  obtain ⟨k,hk⟩:=eventually_atTop.mp inlet
  have grows : Tendsto Λ trail atTop := tendsto_atTop_add_const_left _ _
    ((WilsonAdmissionScale.logarithm_tendsto R.family.path.levels hG).comp
      (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB))
  have lr := Real.log_pos (show 1<(Z.run.ratio:ℝ) by
    exact_mod_cast (show 1<Z.run.ratio from (by decide : 1<3).trans_le Z.run.large))
  have positive : 0 < |Rose.cT Z.criterion.cut G Z.criterion.image| := abs_pos.mpr Z.criterion.fresh.ne
  filter_upwards [dates,grows.eventually_ge_atTop 1,grows.eventually_ge_atTop ((k:ℝ)*Real.log Z.run.ratio)]
    with r hm one bound
  intro q u z b
  have large : k ≤ index r := by
    have p : Λ r ≤ (Λ r)^((3:ℝ)/2) := by
      simpa using Real.rpow_le_rpow_of_exponent_le one (show (1:ℝ)≤3/2 by norm_num)
    exact_mod_cast le_of_mul_le_mul_right (bound.trans (p.trans hm.2.1)) lr
  rw [WilsonPositionRawCutoff.thermometer,finite Z (Z.run.step (index r)) (hk _ large).1 q u,←sub_div,
    abs_div,div_le_iff₀ positive]

end YM.Integration.WilsonPositionFineDetectorSource
