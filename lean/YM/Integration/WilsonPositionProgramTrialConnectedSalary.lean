import YM.Integration.WilsonPositionProgramTrialRegisteredReturn
import YM.Integration.WilsonPositionEpochCellTariff

/-! The registered signed return with its actual connected cofactors, and a
compact-test bound independent of the volume of the auxiliary inversion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialConnectedSalary
open Filter Set Finset Function PowerSeries MeasureTheory Metric Lattice Wilson XSpace XSpace.Rose
open XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerFundedSecant (faceKey)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonPositionProgramTrialSurvey (source)
open WilsonPositionProgramTrialRose (filed roster expense posts)
open scoped Classical BigOperators ENNReal Topology
variable {G : Gauge} (R : Run G) (d : Fin 3 → ℕ) (cap : ∀ k, d k < 7)
    (v : (k : Fin 3) → (R.family.labels.level (d k)).Coeff)
    (W : Initialize G) (V : Store G) (t : Sample 3)
local notation "post" => posts (source R d v W t) (filed W V t)

def stopped (q : ℕ) (E : Badge → ℕ → ℂ) : ℂ :=
  ∑ j : Fin 7, ∑ f ∈ antidiagonal q, coeff f.1 (post j) * E (faceKey j) f.2

def payroll (q : ℕ) (fee : Badge → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j : Fin 7, ∑ f ∈ antidiagonal q, ‖coeff f.1 (post j)‖ₑ * fee (faceKey j) f.2

theorem original (q : ℕ) (E : Badge → ℕ → ℂ) (fee : Badge → ℕ → ℝ≥0∞) (b : ℝ≥0∞)
    (bought : ∀ s k, k ≤ q →
      ‖coeff k (source R d v W t s) - quotient W (V:=V) t (tag G) k s - E s k‖ₑ ≤ b * fee s k) :
    ‖coeff q (roster R d cap v W V t) - stopped R d v W V t q E‖ₑ ≤
      b * payroll R d v W V t q fee := by
  have face (s : Badge) (k : ℕ) : coeff k (expense R d cap v W V t s) =
      coeff k (source R d v W t s) - quotient W (V:=V) t (tag G) k s := by
    rw [expense,map_add,coeff_mk,WilsonPositionProgramTrialSurvey.original R d cap v W V t (tag G) s k]
  rw [roster,map_sum,stopped,←sum_sub_distrib,payroll,Finset.mul_sum]
  refine (enorm_sum_le ..).trans (sum_le_sum fun j _ => ?_)
  rw [coeff_mul,←sum_sub_distrib,Finset.mul_sum]
  simp_rw [←mul_sub]
  refine (enorm_sum_le ..).trans (sum_le_sum fun f hf => ?_)
  have pair := Finset.HasAntidiagonal.mem_antidiagonal.mp hf
  rw [enorm_mul,face,mul_left_comm]
  exact mul_le_mul_right (bought (faceKey j) f.2 (by omega)) _

variable {n : ℕ} (m : Mesh) (φ : Test n) (Y : Sample n → ℂ)

theorem compact {D b w : ℝ} (small : m.spacing ≤ 1) (cost : 0 ≤ b) (available : 0 ≤ w)
    (radius : ∀ z ∈ tsupport φ, ‖z‖ ≤ D) (bound : ∀ z, ‖φ z‖ ≤ b)
    (localPrice : ∀ c ∈ m.Box, ∀ u : m.Tuple (n:=n), m.rel (m.back u) c ∈ tsupport φ →
      ‖Y ⟨m,m.back u,0⟩‖ ≤ w) :
    ‖Deposit m Y φ‖ ≤ b * w * volume.real (closedBall (0 : Points n) (D + 4*n)) := by
  let aisle := closedBall (0 : Points n) (D + 4*n)
  suffices h : ‖Deposit m Y φ - 0‖ ≤ b * w * volume.real aisle by simpa only [sub_zero] using h
  apply homeward_price
  intro c hc
  let Q := m.levels c (board m φ Y c)
  have spatial (z : Points n) : ‖Q z‖ ≤ b*w ∧ (z ∉ aisle → Q z = 0) := by
    by_cases atCell : ∃ u : m.Tuple (n:=n), z ∈ m.cell c (m.back u)
    · obtain ⟨u,hu⟩ := atCell
      have field : Q z = φ (m.rel (m.back u) c) * Y ⟨m,m.back u,0⟩ := m.stair_at c z hu
      rw [field]
      by_cases used : m.rel (m.back u) c ∈ tsupport φ
      · have close := m.upper_corner c hu
        have inside : z ∈ aisle := by
          rw [show aisle = closedBall (0 : Points n) (D+4*n) from rfl,mem_closedBall,dist_zero_right]
          exact Mesh.norm_near small (radius _ used) ((dist_comm z _).trans_le close)
        constructor
        · rw [norm_mul]
          exact mul_le_mul (bound _) (localPrice c hc u used) (norm_nonneg _) cost
        · exact fun miss => (miss inside).elim
      · rw [image_eq_zero_of_notMem_tsupport used,zero_mul,norm_zero]
        exact ⟨mul_nonneg cost available,fun _ => rfl⟩
    · have field : Q z = 0 := m.stair_off c z (fun u hu => atCell ⟨u,hu⟩)
      rw [field,norm_zero]
      exact ⟨mul_nonneg cost available,fun _ => rfl⟩
  change ‖(∫ z,Q z) - 0‖ ≤ _
  rw [sub_zero,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=aisle) (fun z => (spatial z).2)]
  exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..|>.measure_lt_top)
    (fun z _ => (spatial z).1)

end YM.Integration.WilsonPositionProgramTrialConnectedSalary
end
