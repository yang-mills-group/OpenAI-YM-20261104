import YM.Integration.FVA1Physical.Wilson.MovingExpansion
import YM.FVA2.FkMoment

/-! Exact Wick coefficients for the inherited physical ray. The chart
Jacobian and the tag prior stay inside the calculation. The extra scalar
appearing in numerator and vacuum is strictly positive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FVA2 FVA2.CityHistory FVA2.RayScatter
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (Z : ChartRatio G) (t : d.Tags) (u : Pins G c)

def rayFactor (h : d.Room G) : ℝ :=
  basePower (jointV d t) (gives d t h) u (city G d) 1 *
    ((Fintype.card d.Tags : ℝ)⁻¹ * Stack.overhead Z d.Links)

theorem rayFactor_pos (hZ : LocalRatio Z) (h : d.Room G) : 0 < rayFactor d Z t u h :=
  mul_pos (base_power_pos ..) (mul_pos
    (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (tagNonempty d))))
    (Stack.official hZ))

private theorem ray_kernel {W : SpaceF G d → ℝ} (hw : ContDiffAt ℝ ω W 0)
    (hZ : LocalRatio Z) (h : d.OK G) (a : ℕ → ℝ) :
    rise (chartAmplitude d Z a t W) * Stack.exponential (Stack.advancing (consume d t 1)) =
    roll ((Fintype.card d.Tags : ℝ)⁻¹ * overhead Z d.Links) *
      (supplyZ d Z t (Delay.stones a) * rise W) := by
  let j := jacobian Z (U:=d.Links) ∘ (Legacy.framesF d G)
  let e := Real.exp ∘ (-(consume d t a (G:=G)))
  let b := (Fintype.card d.Tags : ℝ)⁻¹
  have hj : ContDiffAt ℝ ω j 0 := Fork.Hhold Z hZ
  have he : ContDiffAt ℝ ω e 0 := (thermal d t h a).neg.exp
  have eqn : chartAmplitude d Z a t W = b • (j * e * W) := by
    funext x
    change jacobian Z x.1 * b * Real.exp (-consume d t a x) * W x =
      b * ((jacobian Z x.1 * Real.exp (-consume d t a x)) * W x)
    ring
  have hH := Fork.smear_abs (F:=Pins G c) (ι:=d.Links) (p:=consume d t (G:=G) 1) Z hZ
  change roll (overhead Z d.Links) *
    (Legacy.birth Z d * Stack.exponential (Stack.advancing (consume d t (G:=G) 1))) =
    rise j * Stack.exponential (Stack.advancing (consume d t (G:=G) 1)) at hH
  rw [eqn,ExactTower.rise_natural (f:=j*e*W) b
    (((hj.mul he).mul hw).of_le le_top),rise_mul (f:=j*e) (g:=W) ((hj.mul he).of_le le_top) (hw.of_le le_top),
    rise_mul (f:=j) (g:=e) (hj.of_le le_top) (he.of_le le_top),Delay.suitcase Z t a h hZ,Legacy.noStats Z hZ h t,
    OpenSlots.chip,Delay.exp_vac0 (thermal_stat d t h)]
  change roll b * (rise j * rise e * rise W) * Stack.exponential (Stack.advancing (consume d t 1)) =
    roll (b*overhead Z d.Links) * ((Legacy.birth Z d * _ * rise e)*rise W)
  rw [show roll (E:=SpaceF G d) (b*overhead Z d.Links) = roll b * roll (overhead Z d.Links)
      by simp [roll,map_mul]]
  linear_combination (norm := ring_nf) -(roll b * rise e * rise W) * hH

/-- All coarse fields and the actual inverse-coupling offsets enter the
independent formal transfer, for arbitrary joint analytic history marks. -/
theorem ray_ticket {W : SpaceF G d → ℝ} (hw : ContDiffAt ℝ ω W 0)
    (hZ : LocalRatio Z) (h : d.Room G) (a : ℕ → ℝ) :
    PowerSeries.mk (rayCoefficient d Z a t u W) =
      C (rayFactor d Z t u h) *
        Stack.read u (μLedger d Z t h (Delay.stones a) * premiere d Z t h (Delay.stones a) (rise W)) := by
  have quadratic (v : SpaceF G d) :
      (jointV d t).flourish v = 2 * jet (consume d t 1) 2 v := by linarith only [progress d t v]
  unfold rayCoefficient rayPhase
  rw [FVA2.RayScatter.absolute 1 (thermal d t (room_ok d h) 1) (jointV d t) quadratic
    (gives d t h) u (city G d) _ (chartAmplitude_analytic d hZ (room_ok d h) a t hw),
    ray_kernel d Z t hw hZ (room_ok d h) a, Fork.roll_μ, map_mul (Stack.read u), rollThrough,
    share_part d t (Delay.stones a) h (rise W) Z hZ,rayFactor]
  simp only [map_mul,mul_assoc]

end YM.Integration.FVA1Physical.Wilson
