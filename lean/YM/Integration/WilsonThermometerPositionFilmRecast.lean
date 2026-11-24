import YM.Integration.WilsonThermometerOriginalFilmRows
import YM.Integration.WilsonPhysicalMarkedDefectBasisTransport
import YM.Integration.WilsonThermometerOriginalClockSlope

/-! At the measured inverse clock the actual finite recast stores every upper connected face through first order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmRecast
open Function Finset Lattice Wilson RG Exterior Precision Tree Marker Multi
open FVA1Physical.Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Rebirth AllOrder AllOrder.Floe
open Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Symmetry Comparison.RG02.Order
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {R:Census V} {c f:Side}
    {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G} (K:Bulk.Kernel S p P O)
    (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f) (grades:V→ℕ) (r:ℕ) (live:0<r)
    (q:Pace.Coin) (a:ℝ) (earned:Pace.Earn q a) (depth:ℕ) (base:Bulk.Colors R G c)
local notation "clock" => (Rebirth.caliber q earned.1).back depth
local notation "bank" => FVA1Physical.Wilson.recastColors K F tag C grades r clock base
local notation "A" => Stationary.arm G c 1

include live in
theorem original (valid:∀t:Hot R,C.power t=Launch.index R grades t.val+1)
    (s:Hot R) (x:fieldDir G c 1) :
    let W:=logMarked (Bulk.Fk K F tag C x r)
    (Air.discharge bank 0 x).part s.val=(First.buc W).part s.val ∧
      (Air.discharge bank 1 x).part s.val=(First.ind W).part s.val := by
  let U:=fun l (y:Stationary.Link G c)=>Orbit.words K F tag C r s.val l ((A) y)
  have smooth (l:ℕ) (_:l≤r):Differentiable ℝ (U l):=
    ((FVA1Physical.Wilson.mixed_engineering_degree K F tag C grades valid s r l).smooth.differentiable (by simp)).comp (A).differentiable
  have z:=WilsonThermometerOriginalClockSlope.zeroth U clock r ((A).symm x)
  have o:=WilsonThermometerOriginalClockSlope.first U clock (WilsonThermometerOriginalClockSlope.rating q a earned depth)
     r live smooth ((A).symm x)
  have root (l:ℕ) (hl:l≤r): (Air.discharge bank l x).part s.val=born U clock 0 r l ((A).symm x) := by
    rw [FVA1Physical.Wilson.recast_read K F tag C grades r clock base valid hl,Multi.part_lit]
    rfl
  constructor
  · rw [root 0 (Nat.zero_le _),z]
    unfold U
    rw [(A).apply_symm_apply]
    rfl
  · rw [root 1 live,o]
    unfold U
    rw [(A).apply_symm_apply]
    rfl

end YM.Integration.WilsonThermometerPositionFilmRecast
