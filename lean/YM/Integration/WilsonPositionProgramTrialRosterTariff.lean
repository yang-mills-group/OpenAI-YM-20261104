import YM.Integration.WilsonPositionProgramTrialAppointment
import YM.Integration.WilsonOriginalPublicFigureCatalogue
import YM.Integration.WilsonOriginalPublicFigureCharges
import YM.Integration.WilsonMaxwellThermometerSurveyThreeAllowance

/-! Apply the finite published rates to the actual R and W coefficient lists
after both have been issued, retaining their complete common quiet field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialRosterTariff
open Function Finset PowerSeries Lattice Wilson XSpace XSpace.Rose XSpace.Normalize XSpace.Cirrus
open XSpace.Structure1 PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonPositionProgramInversionMaterial (Axes ceiling)
open WilsonMaxwellThermometerSurveyThreeRoster (Pin read hear)
open WilsonMaxwellThermometerSurveyThreeLedger (invoice)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonPositionProgramTrialSurvey (source)
open scoped Classical BigOperators ENNReal
variable {G : Gauge} (R : Run G) (q : ℕ) (D : Pin R →₀ PowerSeries ℂ)

def proposed (A : Pin R → ℕ → ℂ) : ℂ :=
  ∑ a ∈ D.support, ∑ f ∈ antidiagonal q, coeff f.1 (D a) * A a f.2

def charge : ℝ≥0∞ :=
  ∑ a ∈ D.support, ∑ f ∈ antidiagonal q, ‖coeff f.1 (D a)‖ₑ

theorem tariff (W : Initialize G) (t : Sample 3) (A : Pin R → ℕ → ℂ)
    (b : ℝ≥0∞) (rate : ∀ a k, k ≤ q → ‖coeff k (read R W t a) - A a k‖ₑ ≤ b) :
    ‖coeff q (hear R W t D) - proposed R q D A‖ₑ ≤ b * charge R q D := by
  simp only [hear, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, smul_eq_mul,
    coeff_mul, proposed, charge]
  rw [← sum_sub_distrib, Finset.mul_sum]
  refine (enorm_sum_le ..).trans (sum_le_sum fun a _ => ?_)
  rw [← sum_sub_distrib, Finset.mul_sum]
  simp_rw [← mul_sub]
  refine (enorm_sum_le ..).trans (sum_le_sum fun f hf => ?_)
  rw [enorm_mul, mul_comm b]
  have pair := Finset.HasAntidiagonal.mem_antidiagonal.mp hf
  exact mul_le_mul_right (rate a f.2 (by omega)) _

theorem surveyed (W : Initialize G) (V : Store G) (t : Sample 3)
    (p : Tags G 6 3) (s : Badge) (A : Pin R → ℕ → ℂ)
    (b : ℝ≥0∞) (rate : ∀ a k, k ≤ q → ‖coeff k (read R W t a) - A a k‖ₑ ≤ b) :
    let D := invoice R W V t p q s
    ‖quotient W (V:=V) t p q s - proposed R q D A‖ₑ ≤ b * charge R q D := by
  intro D
  rw [← WilsonMaxwellThermometerSurveyThreeLedger.printed R W V t p q s]
  exact tariff R q D W t A b rate

variable (d : Fin 3 → ℕ) (s : Badge) (v : (i : Fin 3) → (R.family.labels.level (d i)).Coeff)
local notation "dₛ" => (d ∘ Subtype.val : s → ℕ)
local notation "vₛ" => (fun i:s => v (Subtype.val i))
local notation "ζ" => WilsonOriginalPublicFigureCatalogue.filed R dₛ vₛ

def originalBill : ℝ≥0∞ := WilsonOriginalPublicFigureCharges.charge R dₛ q ζ

def originalSum (A : Axes R dₛ → ℕ → ℂ) : ℂ :=
  ∑ u : WilsonPositionProgramSeriesRead.Terms R dₛ q,
    WilsonPositionProgramSeriesRead.weight R dₛ q ζ u * A u.1 u.2.val.2

theorem balance (W : Initialize G) (V : Store G) (t : Sample 3) (p : Tags G 6 3)
    (A : Axes R dₛ → ℕ → ℂ) (B : Pin R → ℕ → ℂ) (b : ℝ≥0∞)
    (billA : ‖coeff q (source R d v W t s) - originalSum R q d s v A‖ₑ ≤
      b * originalBill R q d s v)
    (billB : ∀ a k, k ≤ q → ‖coeff k (read R W t a) - B a k‖ₑ ≤ b) :
    let D := invoice R W V t p q s
    ‖coeff q (source R d v W t s) - quotient W (V:=V) t p q s -
      (originalSum R q d s v A - proposed R q D B)‖ₑ ≤
      b * (originalBill R q d s v + charge R q D) := by
  intro D
  have second := surveyed R q W V t p s B b billB
  rw [show ∀ a b c d : ℂ, a-b-(c-d)=(a-c)+(d-b) from fun _ _ _ _ => by ring,mul_add]
  refine (enorm_add_le ..).trans (add_le_add billA ?_)
  rwa [enorm_sub_rev]

end YM.Integration.WilsonPositionProgramTrialRosterTariff
end
