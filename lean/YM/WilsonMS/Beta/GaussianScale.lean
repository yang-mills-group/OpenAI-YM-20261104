import YM.WilsonMS.Beta.Pearled
/-!
# Loop integrals of the numerical coefficient

Shift each momentum integral at the corresponding heat scale. With rigorous
kernel convergence available can use the ordinary formulas on these finite
Gaussian expressions. Result is under a single compact-interval integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue.HeatPapers
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native Horn
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open Papers
open scoped Topology ContDiff BigOperators ENNReal
variable {α : ℝ} (h : 0 < α)

abbrev ν (r : ℝ) : ℝ :=
  1 + r ^ 2

lemma ν_pos (r : ℝ) : 0 < ν r := by
  unfold ν
  positivity

def displacement (x r : ℝ) : ℝ :=
  r ^ 2 * x / ν r
variable (p : QP) (x t d u : ℝ)
local notation "a" => ν t
local notation "P" => Kproj x
local notation "Ψ" => displacement x t
local notation "Π" => Kproj (displacement x t)

lemma density_move : Pill t P (p - Π) = t ^ 3 * Real.exp (-(x * Ψ)) * Real.exp (-(a * p.sq)) := by
  unfold Pill City.brush
  rw [one_pow, one_pow, one_mul, one_mul, mul_left_comm, mul_assoc]
  rw [← exp_add, ← exp_add]
  congr 2
  unfold Momentum.sq
  unfold displacement ν Kproj Punit
  norm_num [Fin.sum_univ_four, Detect.spike, Pi.single_apply]
  simp +decide
  field_simp
  ring

def capital (F : ℝ → ℝ → ℝ → ℝ) (x t : ℝ) :=
  t ^ 3 * Real.exp (-(x * displacement x t)) * (Real.pi ^ 2 / ν t ^ 2 / (2 * Real.pi) ^ 4) *
    F (ν t) (displacement x t) x

lemma capitalized (F : QP → ℝ) (v : HeatPapers.Poly) (hF : ∀ p : QP, F (p - Π) = v.val p)
    (C : ℝ → ℝ → ℝ → ℝ) (hv : Papers.opening mplane (Beam a (ν_pos t)) v = C a Ψ x) :
    tune P F t = capital C x t := by
  unfold tune capital
  rw [← integral_sub_right_eq_self _ Π, ← hv, mul_assoc (t ^ 3 * _), ← net_order (ν_pos t)]
  simp_rw [density_move, hF, mul_assoc, MeasureTheory.integral_const_mul]
  ring_nf
  refine congr_arg (fun x : ℝ => _ * x) (integral_congr_ae ?_)
  exact Eventually.of_forall (fun x : QP => mul_comm ..)

lemma momenta_A : tune P (SpurA x) t = capital ValueA x t := by
  apply capitalized x t _ (paneA Ψ x) _ _ (paneA_value ..)
  intro v
  rw [riser_A]
  change _ = meterR v (paneA Ψ x)
  rw [paneA_ray]
  simp only [Pi.sub_apply, along_one, ↓reduceIte]
  simp +decide

lemma momenta_S : tune P (SpurK x) t = capital ValueS x t := by
  apply capitalized x t _ (paneS Ψ x) _ _ (paneS_value ..)
  intro v
  rw [riser_S]
  change _ = meterR v (paneS Ψ x)
  rw [paneS_ray]
  simp only [Pi.sub_apply, along_one, ↓reduceIte]
  simp +decide
end YM.WilsonMS.BetaValue.HeatPapers
