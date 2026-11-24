import YM.Integration.WilsonTrueProjectedPointGradeLift
import YM.Integration.WilsonPinnedWidthCalendar

/-! The measured clock pays the comparison of all temperatures in one
independent inverse prefix. The upper cutoff enters only through the given
dated inverse matrices on that same finite course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointClock
open Function Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open QuadraticLocal RemainderComparison ConnectedActivityE6 Push
open WilsonTrueProjectedPointInverse WilsonTrueProjectedPointSalary WilsonPinnedWidthTransport
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G)
local notation "C" => R.family
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "S" => R.family.S

theorem spread (i j : ℕ) : H j-H i=G.slopeConstant*elapsed S i j := by
  change _+G.slopeConstant*(S).scale j-(_+G.slopeConstant*(S).scale i)=_
  unfold elapsed
  ring

theorem elapsed_nonnegative {i j : ℕ} (hi : i ≤ j) : 0 ≤ elapsed S i j := by
  have b := blocks S i (j-i)
  rw [show i+(j-i)=j by omega] at b
  exact (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))).trans b

theorem monotone (simple : G.Simple) {i j : ℕ} (hi : i ≤ j) : H i ≤ H j := by
  apply sub_nonneg.mp
  rw [spread R]
  exact mul_nonneg (G.slopeConstant_pos simple).le (elapsed_nonnegative R hi)

theorem log_rise (simple : G.Simple) {first j : ℕ} (live : first ≤ j) :
    1 ≤ Λ first ∧ Λ j ≤ Λ first+G.slopeConstant*elapsed S first j := by
  have base : 1 ≤ H first := ((C).path.levels.fits.delayed first).le
  have order := monotone R simple live
  have hpos := zero_lt_one.trans_le base
  have higher := hpos.trans_le order
  have estimate := Real.log_le_sub_one_of_pos (div_pos higher hpos)
  rw [Real.log_div higher.ne' hpos.ne'] at estimate
  have limit : H j/H first-1 ≤ H j-H first := by
    rw [show H j/H first-1=(H j-H first)/H first by field_simp]
    exact div_le_self (sub_nonneg.mpr order) base
  change 1 ≤ 2+Real.log (H first) ∧ 2+Real.log (H j) ≤ 2+Real.log (H first)+_
  rw [←spread R first j]
  exact ⟨by linarith [Real.log_nonneg base],by linarith only [estimate,limit]⟩

theorem thermal (simple : G.Simple) {N per first i j : ℕ}
    (early : first ≤ i) (along : i ≤ j) (live : j ≤ N) :
    let g := fun k => Coat.gStep (((C).path.rep N per k).beta)
    0<g j ∧ |g i/g j| ≤ 2*(1+G.slopeConstant*elapsed S first j) := by
  let t := elapsed S first j
  let σ := G.slopeConstant
  have t0 : 0 ≤ t := elapsed_nonnegative R (early.trans along)
  have hσ : 0 ≤ σ := (G.slopeConstant_pos simple).le
  have n : 0 ≤ σ*t := mul_nonneg hσ t0
  have P : 0<1+σ*t := by linarith
  have bp : 1 ≤ H first := ((C).path.levels.fits.delayed _).le
  have order := monotone R simple early
  have sp := spread R first j
  have r : H j ≤ H i*(1+σ*t) := by
    have tmp : H j ≤ H first*(1+σ*t) := by
      change H j-H first=σ*t at sp
      nlinarith only [sp,mul_nonneg (sub_nonneg.mpr bp) n]
    exact tmp.trans (mul_le_mul_of_nonneg_right order P.le)
  let I := ((C).path.rep N per i).beta
  let J := ((C).path.rep N per j).beta
  have lo : H i/2 ≤ I := (R.makes.wilson.represents N per i (along.trans live)).band.1
  have hi : J ≤ 2*H j := (R.makes.wilson.represents N per j live).band.2
  have ip : 0<I := (half_pos (zero_lt_one.trans_le (bp.trans order))).trans_le lo
  have jp : 0<J := (half_pos (zero_lt_one.trans ((C).path.levels.fits.delayed _))).trans_le
    (R.makes.wilson.represents N per j live).band.1
  have linear : J ≤ 4*(1+σ*t)*I := by
    have hmul := mul_le_mul_of_nonneg_right (show H i ≤ 2*I by linarith) P.le
    linarith only [hi,r,hmul]
  have squared : J ≤ (2*(1+σ*t))^2*I := by
    apply linear.trans
    apply mul_le_mul_of_nonneg_right _ ip.le
    nlinarith only [n,sq_nonneg (σ*t)]
  have rr:=Real.sqrt_le_sqrt squared
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by linarith : 0 ≤ 2*(1+σ*t))] at rr
  change 0<(Real.sqrt J)⁻¹ ∧ |(Real.sqrt I)⁻¹/(Real.sqrt J)⁻¹| ≤ 2*(1+σ*t)
  rw [inv_div_inv,abs_of_pos (div_pos (Real.sqrt_pos.mpr jp) (Real.sqrt_pos.mpr ip))]
  exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr jp),(div_le_iff₀ (Real.sqrt_pos.mpr ip)).mpr rr⟩

end YM.Integration.WilsonTrueProjectedPointClock

namespace YM.Integration.WilsonTrueProjectedPointClock
open Function Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open WilsonTrueProjectedPointInverse WilsonTrueProjectedPointSalary WilsonPinnedWidthTransport
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G)
variable {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "A" => WilsonNeutralPointCourse.transfer R wood a depth digit

theorem original (N per first n q v : ℕ) (report : ι → PowerSeries ℂ)
    (simple : G.Simple) (o : Stationary.Loc G 1) (front : d ≤ R.family.path.levels.clock.J (first+1))
    (live : first+n+1 ≤ N) {B M : ℝ} (fund : 0 ≤ B) (paid : 0 ≤ M)
    (start : ∀ z, ‖readout R q report z‖ ≤ B)
    (fare : ∀ i, i ≤ n → ∀ k, k ≤ q → ∀ u b,
       |coeff k ((A N (first+i))⁻¹ u b)| ≤ M*(RG16.Lambda R.family.path.levels (first+i))^v)
    (z : Panel R (d:=d) q) :
    let j := first+n
    let t := elapsed R.family.S first j
    let g := fun k => ConnectedActivityE6.Coat.gStep ((R.family.path.rep N per k).beta)
    let ρ := g j
    let bill := (2*(1+G.slopeConstant*t))^q * (M*(RG16.Lambda R.family.path.levels first+G.slopeConstant*t)^v)
    ‖readout R q (lift R wood a depth digit N first g (WilsonTrueProjectedPointGradeLift.change R ρ report) (n+1)) z‖ ≤
      ρ^z.1.val*B*(1+(Fintype.card (Panel R (d:=d) q):ℝ)*bill*(n+1:ℕ))^(level R q z) := by
  intro j t g ρ bill
  have t0 : 0 ≤ t := elapsed_nonnegative R (by dsimp [j];omega)
  have span := mul_nonneg (G.slopeConstant_pos simple).le t0
  have late : first ≤ j := by dsimp [j]; omega
  have within : j ≤ N := by dsimp [j];omega
  have loom := log_rise R simple late
  have Mpos : 0 ≤ M*(RG16.Lambda R.family.path.levels first+G.slopeConstant*t)^v := mul_nonneg paid
    (pow_nonneg (by linarith only [loom.1,span]) _)
  have pos : 0<ρ := (thermal R simple late le_rfl within (per:=per)).1
  apply WilsonTrueProjectedPointGradeLift.original R wood a depth digit N first (n+1) q g report
    simple o front (by omega) pos fund Mpos (by linarith only [span]) start
  · intro i hi
    exact (thermal R simple (Nat.le_add_right first i) (show first+i ≤ j by dsimp [j];omega)
      within (per:=per)).2
  · intro i hi k cap u b
    have age := log_rise R simple (Nat.le_add_right first i)
    have remain := elapsed_nonnegative R (show first+i ≤ j by dsimp [j];omega)
    have le : elapsed R.family.S first (first+i) ≤ t := by
      dsimp only [t,elapsed] at *
      linarith only [remain]
    exact (fare i (by omega) k cap u b).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (log_rise R simple (first:=first+i) (j:=first+i) le_rfl).1)
        (age.2.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left le (G.slopeConstant_pos simple).le))) _) paid)

end YM.Integration.WilsonTrueProjectedPointClock
