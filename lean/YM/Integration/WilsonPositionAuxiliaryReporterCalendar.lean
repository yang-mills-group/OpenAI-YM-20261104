import YM.Integration.WilsonPositionBareScalarDiagonal
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! The common inversion regulator expressed in the original reporting mesh's measured
logarithmic scale, with every accuracy fixed before both physical cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionAuxiliaryReporterCalendar
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Trace.Pilot Pert.Asymptotics
open XSpace FVA2 FVA2.Register FVA2.Scale MS MS.Land
open scoped Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit)
    (t : ℝ→ℝ) (physical : Coupling G t) (Z : WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B

def scale (r : ℝ) : ℝ := 2 + WilsonAdmissionScale.logarithm R.family.path.levels (m r)

local notation "Λ" => scale R hG (B:=B)

private theorem scale_pos (r : ℝ) : 0<Λ r :=
  add_pos (by norm_num) (WilsonAdmissionScale.logarithm_pos _ _)

include hB in
private theorem growing : Tendsto Λ trail atTop :=
  tendsto_atTop_add_const_left _ _ ((WilsonAdmissionScale.logarithm_tendsto R.family.path.levels hG).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB))

include hB pace physical in
theorem measured : Tendsto (fun r=>Λ r + 2*Real.log (t r)) trail (𝓝 2) := by
  have fee := WilsonPhysicalCutoffCurrency.temperature R hG pace hB t physical
  have lim := (Real.continuousAt_log one_ne_zero).tendsto.comp fee
  rw [Real.log_one] at lim
  have sum := lim.const_add 2
  rw [add_zero] at sum
  refine sum.congr' ?_
  filter_upwards [physical.positive] with r hr
  have hb := zero_lt_one.trans (R.family.path.levels.fits.delayed (m r))
  change 2 + Real.log (R.family.path.levels.clock.hatBeta (m r)*t r^2) = _
  rw [Real.log_mul hb.ne' (pow_pos hr _).ne',Real.log_pow]
  change _ = (2+Real.log (R.family.path.levels.clock.hatBeta (m r)))+2*Real.log (t r)
  ring

include hB pace physical H in
theorem paid (q d : ℕ) (C : ℝ) (hc : 0≤C) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail,∀ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ) ≤ C*(Λ r)^d → (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|t r| ≤ δ := by
  have cmp := (measured R hG hB pace t physical).eventually_lt_const (show (2:ℝ)<3 by norm_num)
  have many := (growing R hG hB).eventually_ge_atTop 9
  have power := WilsonPositionBareScalarDiagonal.paid Z H q d (C*4^d) trail
    physical.positive (physical.conforms hG) hd
  filter_upwards [cmp,many,power] with r a b bill i hi bound
  apply bill i hi
  calc
    (i:ℝ) ≤ C*(Λ r)^d := bound
    _ ≤ C*(4*(-Real.log (t r)))^d := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (scale_pos R hG r).le (by linarith) d) hc
    _ = _ := by rw [mul_pow]; ring

/-- A native auxiliary inversion date whose logarithmic inverse spacing equals the original
reporter's Lambda to the three-halves power, up to one fixed-block rounding. -/
def inversion (r : ℝ) : ℕ := ⌈(Λ r)^((3:ℝ)/2)/Real.log Z.run.ratio⌉₊

include hB pace physical H in
theorem original (q : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail,let i:=inversion R hG (B:=B) Z r
      WilsonPositionAuxiliaryMesh.floor Z.run q (t r) ≤ i ∧
      (Z.run.step i).spacing^Tide.mildG ≤ (t r)^(q+1) ∧
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q *|t r| ≤ δ := by
  have base : 1<(Z.run.ratio:ℝ) := by exact_mod_cast (show 1<Z.run.ratio from (by decide : 1<3).trans_le Z.run.large)
  have lr := Real.log_pos base
  obtain ⟨A,ha,lower⟩ := WilsonPositionBareScalarDiagonal.feasible Z q trail physical.positive (physical.conforms hG)
  have root := (tendsto_rpow_atTop (show 0<(1:ℝ)/2 by norm_num)).comp (growing R hG hB)
  have view := (measured R hG hB pace t physical).eventually_const_lt (show (0:ℝ)<2 by norm_num)
  have bill := paid R hG hB pace t physical Z H q 2 ((Real.log Z.run.ratio)⁻¹+1) (by positivity) hd
  filter_upwards [lower,view,(growing R hG hB).eventually_ge_atTop 1,
    root.eventually_ge_atTop (A*Real.log Z.run.ratio),bill,physical.positive] with r low v scaleLarge slope charge hr
  let x:=Λ r
  let i:=inversion R hG (B:=B) Z r
  have x1 : 1≤x := scaleLarge
  have xp : 0<x := zero_lt_one.trans_le x1
  have lead : x*x^((1:ℝ)/2)=x^((3:ℝ)/2) := by
    nth_rw 1 [←Real.rpow_one x]
    rw [←Real.rpow_add xp];norm_num
  have ceilA : x^((3:ℝ)/2)/Real.log Z.run.ratio ≤ (i:ℝ) := Nat.le_ceil _
  have first : WilsonPositionAuxiliaryMesh.floor Z.run q (t r) ≤ i := by
    apply (Nat.cast_le (α:=ℝ)).mp
    refine low.trans ((le_div_iff₀ lr).mpr ?_ |>.trans ceilA)
    calc
      A*(-Real.log (t r))*Real.log Z.run.ratio ≤ x*(A*Real.log Z.run.ratio) := by
        have hx : -Real.log (t r) ≤ x := by
          change 0<x+2*Real.log (t r) at v
          linarith
        calc
          _ ≤ A*x*Real.log Z.run.ratio := by gcongr
          _ = _ := by ring
      _ ≤ x*x^((1:ℝ)/2) := mul_le_mul_of_nonneg_left slope xp.le
      _ = _ := lead
  have large : (i:ℝ) ≤ ((Real.log Z.run.ratio)⁻¹+1)*x^2 := by
    have n := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg xp.le ((3:ℝ)/2)) lr.le)
    change (i:ℝ)<x^((3:ℝ)/2)/Real.log Z.run.ratio+1 at n
    have q2 : x^((3:ℝ)/2) ≤ x^2 := by
      rw [←Real.rpow_natCast];exact Real.rpow_le_rpow_of_exponent_le x1 (by norm_num)
    have div := div_le_div_of_nonneg_right q2 lr.le
    simp only [div_eq_mul_inv] at div n
    nlinarith [show 1≤x^2 from one_le_pow₀ x1]
  exact ⟨first,WilsonPositionAuxiliaryMesh.cost Z.run q hr first,charge i first large⟩

end YM.Integration.WilsonPositionAuxiliaryReporterCalendar
