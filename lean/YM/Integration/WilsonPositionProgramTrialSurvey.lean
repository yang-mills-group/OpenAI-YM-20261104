import YM.Integration.WilsonPositionProgramTrialThermalGrades
import YM.Integration.WilsonMaxwellThermometerSurveyThreeLedger

/-! The fitted original trial and the positioned public column on the same tree.
The change of original group cylinders and the change in their measured weights
are separate signed sums. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialSurvey
open Function Finset PowerSeries Lattice Wilson XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open XSpace.Structure1 PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonMaxwellThermometerSurveyThreeRoster (Pin read printedPin hear)
open private printed from YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
open WilsonThermometerPositionTunedSlope (Columns finite paid price)
open WilsonThermometerPositionTunedCorrection (surveyed residual)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonMaxwellThermometerSurveyThreeLedger (invoice)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (d : Fin 3 → ℕ) (cap : ∀ i, d i < 7)
  (v : (i : Fin 3) → (R.family.labels.level (d i)).Coeff)
  (W : Initialize G) (V : Store G) (t : Sample 3) (p : Tags G 6 3)
  (S : Badge)
local notation "dₛ" => (d ∘ Subtype.val : S → ℕ)
local notation "vₛ" => (fun i : S => v (Subtype.val i))
local notation "zₛ" => (t.layout ∘ Subtype.val : S → Cover)
local notation "T" => W.tree t.F.p

def source : PowerSeries ℂ :=
  paid R dₛ (frozen R dₛ vₛ) (finite R dₛ t.F.p zₛ T)

def cylinder : PowerSeries ℂ :=
  paid R dₛ (frozen R dₛ vₛ) (residual R W dₛ t.F.p zₛ T)

def ballot : Pin R →₀ PowerSeries ℂ :=
  ∑ a : Columns R dₛ, Finsupp.single
    (printedPin R S (fun i => ⟨⟨d i, cap i⟩, a i⟩))
    (price R dₛ (frozen R dₛ vₛ) a)

theorem surveyed_ballot :
    hear R W t (ballot R d cap v S) =
      paid R dₛ (frozen R dₛ vₛ) (surveyed R W dₛ t.F.p zₛ T) := by
  rw [ballot, map_sum, paid]
  apply sum_congr rfl
  intro a _
  rw [hear, Finsupp.linearCombination_single, smul_eq_mul,
    printed R W t S (fun i => ⟨⟨d i, cap i⟩, a i⟩)]
  rfl

def difference (q : ℕ) : Pin R →₀ PowerSeries ℂ :=
  ballot R d cap v S - invoice R W V t p q S

/-- The public payment includes the own-horizon Wick term, the complete layout
at this order and the unit on each absent leg. -/
theorem original (q : ℕ) :
    coeff q (source R d v W t S) - quotient W (V := V) t p q S =
      coeff q (cylinder R d v W t S) +
        coeff q (hear R W t (difference R d cap v W V t p S q)) := by
  have same := WilsonThermometerPositionTunedCorrection.earned R W dₛ t.F.p zₛ T (frozen R dₛ vₛ)
  have h := congrArg (coeff q) same
  rw [map_sub] at h
  rw [difference, map_sub, map_sub, surveyed_ballot,
    WilsonMaxwellThermometerSurveyThreeLedger.printed R W V t p q S]
  change _ - _ = _ + (_ - _)
  unfold source cylinder
  rw [← h]
  ring

/-- At one loop the independently solved field slope multiplies the full
zeroth-order normalized read of the same occupied word. -/
theorem first :
    let δ := difference R d cap v W V t p S 1
    coeff 1 (source R d v W t S) - quotient W (V := V) t p 1 S =
      coeff 1 (cylinder R d v W t S) + ∑ u ∈ δ.support,
        (coeff 0 (δ u) * coeff 1 (read R W t u) + coeff 1 (δ u) * coeff 0 (read R W t u)) := by
  intro δ
  rw [original R d cap v W V t p S]
  congr 1
  change coeff 1 (hear R W t δ) = _
  simp only [hear, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, smul_eq_mul,
    coeff_one_mul, coeff_zero_eq_constantCoeff]
  apply sum_congr rfl
  intro u _
  ring

theorem ground :
    let δ := difference R d cap v W V t p S 0
    coeff 0 (source R d v W t S) - quotient W (V := V) t p 0 S =
      coeff 0 (cylinder R d v W t S) + ∑ u ∈ δ.support,
        coeff 0 (δ u) * coeff 0 (read R W t u) := by
  intro δ
  rw [original R d cap v W V t p S]
  congr 1
  change coeff 0 (hear R W t δ) = _
  simp only [hear, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, smul_eq_mul,
    coeff_zero_eq_constantCoeff, map_mul]

end YM.Integration.WilsonPositionProgramTrialSurvey
end
