import YM.Integration.WilsonRunKineticPeriodIncome
import YM.Integration.WilsonConditionalTaylorKineticWrap

/-! A moving complete finite conditional may be used in the kinetic
readout. Its two-link strip, rather than its name or a particular bare
recursion, is the input to the full Hessian comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonKineticResponseLimit
open Function Finset Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open PhysicalNext.Repeat.Legato MSbar MSbar.Midpoint MSbar.Heath MSbar.Wave
open Qlocal.Schedule WilsonConditionalTaylorSceneCalibration
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators

variable {G : Gauge} (a : G.ColorIndex) (U : (n : Side) → Pap (wire G n)) (e : ℕ) (T : Slopes G)

def finite (n : Side) :=
  caliper n (Lis.sun G a) (coeff e (place (WilsonMovingGaussianCoordinates.link G n).symm (U n)))

theorem raw (civic : ∀ᶠ n in atTop,Civic (U n)) {η : ℝ} (pos : 0<η)
    (actual : Kith η T (fun n=>rancho (U n) e 2)) :
    Tendsto (finite a U e) atTop (𝓝 (2*Cork.value a T)) := by
  obtain ⟨k,A,paid⟩ := (Cork.Pad.ch (0:Axis)).mul (Cork.Pad.ch (0:Axis))
  have localSum := WilsonCoverKineticMoment.anchored k _ A paid (coord (1:Axis),a) (coord (1:Axis),a)
    T (fun n=>rancho (U n) e 2) pos actual
  have cost := (tendsto_const_nhds (x:=(2:ℝ))).mul localSum
  apply cost.congr'
  filter_upwards [civic] with n atSide
  exact (WilsonRunKineticPeriodIncome.measured (U n) e a atSide).symm

variable (R : Run G) (simple : G.Simple) (V : Voice G)
    (invoice : vacuumInvoice a V R.metals R.rolls R.alloy R.kit)
include simple invoice in
theorem physical (N j : ℕ) (hi : j≤N) (civic : ∀ᶠ n in atTop,Civic (U n))
    {η : ℝ} (pos : 0<η) (actual : Kith η T (fun n=>rancho (U n) e 2)) :
    Tendsto (fun per : ℕ=> -(finite a U e (R.family.side j per)) /
      caliper (R.family.side j per) (Lis.sun G a) (inkAt R N per j)) atTop (𝓝 (Cork.value a T)) := by
  have growth : Tendsto (fun per:ℕ=>(R.family.side j per).val) atTop atTop :=
    (show StrictMono (fun per:ℕ=>(R.family.side j per).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  have held : Tendsto (R.family.side j) atTop atTop := tendsto_atTop.2 fun n=>growth.eventually_ge_atTop n.val
  have fetched := (raw a U e T civic pos actual).comp held
  have denom := WilsonConditionalTaylorKineticWrap.limit R simple a V invoice N j hi
  have cover := fetched.neg.div denom (show (-2:ℝ)≠0 by norm_num)
  convert cover using 1 <;> first | rfl | ring

end YM.Integration.WilsonKineticResponseLimit
end
