import YM.Integration.SelectedPlanClearedNumerator

/-! The complete finite submitted plan, at its own measured group field
and beta. The signed cubic and quartic term survives the kinetic subtraction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice Wilson RG Precision Exterior IterationFour IterationFour.Vacuum PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {N per r : ℕ}

def interaction (K : PathData G) (U : Config G n) : ℝ :=
  Patch.average fun h : Signed=>uncut K.cubic (pull h 0 U)+uncut K.quartic (pull h 0 U)

theorem curvature_pair (B : Clip) (K : PathData G) (U : Config G n) :
    mainTerm B K U-secondTerm B K U=interaction K U := by
  unfold mainTerm secondTerm interaction Patch.average
  simp only [Finset.sum_add_distrib]
  ring

theorem earlier_grades (R : Run G) (P : Plan R.family N per r) {m : ℕ}
    (alpha : P.coefficient m 0=P.alpha m) (g : ℝ) :
    P.poly m g-P.alpha m=
      ∑ e∈(Finset.range (r-2+1)).erase 0,P.coefficient m e*g^e := by
  have h0 : 0∈Finset.range (r-2+1) := Finset.mem_range.mpr (by omega)
  have all:=Finset.sum_erase_add (Finset.range (r-2+1)) (fun e=>P.coefficient m e*g^e) h0
  rw [pow_zero,mul_one,alpha] at all
  unfold Plan.poly
  linarith only [all]

theorem spring_numerator (R : Run G) (P : Plan R.family N per r) (m : ℕ)
    (g : ℝ) (y : fieldDir G (R.family.side m per) 1) :
    let K:=(R.family.path.rep N per m).path
    let B:=(R.family.path.levels.params m).clip
    let U:=represent y
    let α:=P.alpha m
    let p:=ActualAnalyticPlanVacuum.radicand R P m g
    let c:=ActualAnalyticPlanVacuum.coupling R P m g
    (SelectedPlanClearedNumerator.numerator R P m (g,y)).re -
        (mainTerm B K U+g^2*(Precision.loop K U+α*secondTerm B K U)) =
      (g^2*(P.poly m g-α))*mainTerm B K U+
      g^2*α*interaction K U+
      p*ActualGradedVacuum.restored (P.layers m) c U := by
  dsimp only
  rw [←curvature_pair (R.family.path.levels.params m).clip]
  simp only [SelectedPlanClearedNumerator.numerator,ActualAnalyticPlanVacuum.vacuum,
    ActualAnalyticPlanVacuum.kinetic,Complex.ofReal_re]
  ring

end YM.Integration.OriginalMarkedRunAction
