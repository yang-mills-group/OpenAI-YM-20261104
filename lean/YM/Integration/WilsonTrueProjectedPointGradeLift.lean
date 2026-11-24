import YM.Integration.WilsonTrueProjectedPointSalary

/-! Restore the physical coupling of each coefficient on the stored inverse
prefix. Positive grades retain their powers even when neighbouring blocks
use different temperatures. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointGradeLift
open Function Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open WilsonTrueProjectedPointInverse WilsonTrueProjectedPointSalary
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "A" => WilsonNeutralPointCourse.transfer R wood a depth digit

def change (ρ : ℝ) (report : ι → PowerSeries ℂ) : ι → PowerSeries ℂ :=
  fun b => rescale (ρ:ℂ) (report b)

theorem placed (N j : ℕ) (ρ g : ℝ) (u b : ι) :
    up R wood a depth digit N j (ρ*g) u b =
      rescale (ρ:ℂ) (up R wood a depth digit N j g u b) := by
  apply PowerSeries.ext
  intro k
  simp only [coeff_rescale,up_at,WilsonTrueProjectedPointSalary.entry,mul_pow,Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]

theorem restored (N first n : ℕ) (ρ : ℝ) (g : ℕ → ℝ) (report : ι → PowerSeries ℂ) :
    lift R wood a depth digit N first (fun j => ρ*g j) (change R ρ report) n =
      change R ρ (lift R wood a depth digit N first g report n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    change (∑ b, up R wood a depth digit N (first+n) (ρ*g (first+n)) u b*
      lift R wood a depth digit N first (fun j => ρ*g j) (change R ρ report) n b) =
      rescale (ρ:ℂ) (∑ b, up R wood a depth digit N (first+n) (g (first+n)) u b*
        lift R wood a depth digit N first g report n b)
    rw [map_sum,ih]
    exact sum_congr rfl fun b _ => by rw [map_mul,placed];rfl

theorem original (N first n q : ℕ) (g : ℕ → ℝ) (report : ι → PowerSeries ℂ)
    (simple : G.Simple) (o : Stationary.Loc G 1) (front : d≤R.family.path.levels.clock.J (first+1))
    (live : first+n≤N) {ρ B C M : ℝ} (hρ : 0<ρ) (fund : 0≤B) (hc : 0≤C) (hM : 1≤M)
    (start : ∀ z, ‖readout R q report z‖≤B)
    (temperature : ∀ i, i<n → |g (first+i)/ρ| ≤ M)
    (fee : ∀ i, i<n → ∀ k, k≤q → ∀ u b, |coeff k ((A N (first+i))⁻¹ u b)| ≤ C)
    (z : Panel R (d:=d) q) :
    ‖readout R q (lift R wood a depth digit N first g (change R ρ report) n) z‖ ≤
      ρ^z.1.val*B*(1+(Fintype.card (Panel R (d:=d) q):ℝ)*(M^q*C)*n)^(level R q z) := by
  let h := fun j => g j/ρ
  have hM0 := zero_le_one.trans hM
  have fare (i : ℕ) (active : i<n) (k : ℕ) (cap : k≤q) (u b : ι) :
      |WilsonTrueProjectedPointSalary.entry R wood a depth digit N (first+i) (h (first+i)) k u b| ≤ M^q*C := by
    rw [WilsonTrueProjectedPointSalary.entry,abs_mul,abs_pow]
    exact mul_le_mul ((pow_le_pow_left₀ (abs_nonneg _) (temperature i active) k).trans
      (pow_le_pow_right₀ hM cap)) (fee i active k cap u b) (abs_nonneg _) (pow_nonneg hM0 _)
  have bound := WilsonTrueProjectedPointSalary.original R wood a depth digit N first n q h report
    simple o front live (mul_nonneg (pow_nonneg hM0 _) hc) fund start fare z
  have equal : (fun j => ρ*h j) = g := by
    funext j
    dsimp only [h]
    field_simp
  have liftEq := restored R wood a depth digit N first n ρ h report
  rw [equal] at liftEq
  rw [liftEq]
  unfold readout change
  rw [coeff_rescale,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
  exact (mul_le_mul_of_nonneg_left bound (pow_nonneg hρ.le _)).trans_eq (by ring)

theorem constant (ρ : ℝ) (report : ι → ℂ) :
    change R ρ (fun b=>PowerSeries.C (report b)) = fun b=>PowerSeries.C (report b) := by
  funext b
  apply PowerSeries.ext
  intro n
  cases n <;> simp [change,coeff_rescale,coeff_C]

end YM.Integration.WilsonTrueProjectedPointGradeLift
