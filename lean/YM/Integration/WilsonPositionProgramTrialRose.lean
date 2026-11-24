import YM.Integration.WilsonPositionProgramTrialSurvey
import YM.Integration.WilsonMaxwellThermometerFundedSecant
import YM.Integration.WilsonMaxwellThermometerKineticPanel

/-! The measured trial, with one frozen fitted vector per slot on every face,
and the seven public readings in the prescribed centered compact test. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonPositionProgramTrialRose
open Function Finset PowerSeries Lattice Wilson XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open XSpace.Structure1 XSpace.Retirement FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open WilsonPositionProgramTrialSurvey (source cylinder difference)
open WilsonMaxwellThermometerSurveyThreeRoster (hear)
open WilsonMaxwellThermometerFundedSecant (faceKey)
open scoped Classical BigOperators

def posts (a b : Badge → PS) : Fin 7 → PS :=
  ![1, -b {2}, -b {1}, -b {0}, -a {1,2} + 2*a {1}*a {2},
    -a {0,2} + 2*b {0}*a {2}, -a {0,1} + 2*b {0}*b {1}]

theorem connected (a b : Badge → PS) :
    b3 a - b3 b = ∑ j : Fin 7, posts a b j * (a (faceKey j) - b (faceKey j)) := by
  simp only [b3, two_smul, posts, faceKey, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, add_zero]
  ring

variable {G : Gauge} (R : Run G) (d : Fin 3 → ℕ) (cap : ∀ i, d i < 7)
  (v : (i : Fin 3) → (R.family.labels.level (d i)).Coeff)
  (W : Initialize G) (V : Store G) (t : Sample 3)

def expense (S : Badge) : PS :=
  cylinder R d v W t S + PowerSeries.mk (fun q =>
    coeff q (hear R W t (difference R d cap v W V t (tag G) S q)))

def filed (S : Badge) : PS := batchT (cooked W V 6 t) S

theorem face (S : Badge) :
    source R d v W t S - filed W V t S = expense R d cap v W V t S := by
  apply PowerSeries.ext
  intro q
  rw [expense, map_add, coeff_mk, map_sub, filed, batchT, coeff_mk]
  rw [Rose.detail W V t (tag G) q S]
  exact WilsonPositionProgramTrialSurvey.original R d cap v W V t (tag G) S q

def roster : PS :=
  ∑ j : Fin 7, posts (source R d v W t) (filed W V t) j *
    expense R d cap v W V t (faceKey j)

theorem normalized :
    b3 (source R d v W t) - together W V t = roster R d cap v W V t := by
  change _ - b3 (filed W V t) = _
  rw [connected, roster]
  apply sum_congr rfl
  intro j _
  rw [face R d cap v W V t]

theorem first :
    coeff 1 (b3 (source R d v W t)) - coeff 1 (together W V t) =
      ∑ j : Fin 7,
        (coeff 0 (posts (source R d v W t) (filed W V t) j) *
            coeff 1 (expense R d cap v W V t (faceKey j)) +
         coeff 1 (posts (source R d v W t) (filed W V t) j) *
            coeff 0 (expense R d cap v W V t (faceKey j))) := by
  rw [← map_sub, normalized R d cap v W V t, roster, map_sum]
  apply sum_congr rfl
  intro j _
  rw [coeff_one_mul]
  simp only [coeff_zero_eq_constantCoeff]
  ring

variable (Z : WilsonPrescription G) (m : Mesh)

/-- The public quantity at the right-hand side is the actual finite detector
coefficient on the chosen mesh, with its native smear and center rule. -/
theorem original (q : ℕ) :
    Deposit m (fun t => coeff q (b3 (source R d v Z.scheme t))) (test Z.criterion) -
      coeff q (Detector Z.scheme Z.criterion m) =
    Deposit m (fun t => coeff q (roster R d cap v Z.scheme Z.store t)) (test Z.criterion) := by
  rw [Rose.detector]
  unfold Deposit
  rw [← mul_sub, ← sum_sub_distrib]
  apply congrArg (_ * ·)
  apply sum_congr rfl
  intro x _
  rw [← mul_sub, ← map_sub, normalized R d cap v Z.scheme Z.store]

end YM.Integration.WilsonPositionProgramTrialRose
end
