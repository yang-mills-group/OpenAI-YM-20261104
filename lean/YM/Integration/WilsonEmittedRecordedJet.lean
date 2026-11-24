import YM.Integration.WilsonEmittedWordFootprint
import YM.Integration.FVA1Physical.TwoReset.ReadCopies
import YM.Integration.WilsonVacuumPreResetJointRootReading

/-! The original one-page receiver reads the complete funded group word at a
genuine nonflat link direction with its single native Laurent shift. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedRecordedJet
open Function Finset Lattice Wilson RG Precision Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison.RG02 FVA1Physical FVA1Physical.TwoReset AllOrder.Ker
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Laurent PertExtension.Series AnalyticBridge.SectorAffine.Offset
open WilsonEmittedRootCensus WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (x : X) (w : V → ℕ) {σ : ℝ} {p : ℕ}
variable (staff : Air.Staff M (fun i=>(M i).paint x) w σ p)
variable (L : Layout G) (tape : Finset Age) (s : Multi.Hot Γ)
local notation "q" => (fun i : ι=>(M i).paint x)
local notation "Z" => Air.craft M q w L tape
local notation "C" => field M q (picked M s.val)
local notation "d" => Launch.index Γ w s.val+1
def chart (G : Gauge) (n : Side) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap
    ((Stationary.arm G n 1).toContinuousLinearMap.comp (WilsonCubicOriginalTorus.coordinates G n))

private theorem linked : C=Bulk.projected ((Z).mark s) ∘ chart G n := by
  funext z
  have eqn:=WilsonVacuumPreResetJointRootReading.logarithm (G:=G) (f:=n) z.2
  change Air.sums M q (picked M s.val) z.1 (increment 1 z.2) =
    Air.sums M q (fun i=>(ScatterR.actor M i).val=s.val) z.1
      (Stationary.input G n (WilsonCubicOriginalTorus.coordinates G n z.2))
  rw [eqn]
  congr 1
  funext i
  apply propext
  exact eq_comm

include staff in
theorem original (j : ℕ) (A : Directions G n) :
    Assembly.jet C (d+j) (1,A)=
      (Air.discharge Z j (Stationary.arm G n 1 (WilsonCubicOriginalTorus.coordinates G n A))).part s.val := by
  rw [Air.discharge,Multi.part_lit,linked M x w L tape s]
  exact Assembly.jet_continuous_right (chart G n) ((Air.grade M q w staff L tape s).smooth.of_le le_top) (f:=Bulk.projected ((Z).mark s)) (1,A)

include staff L tape in
theorem below (j : ℕ) (hj : j<d) (A : Directions G n) :
    Assembly.jet C j (1,A)=0 := by
  rw [linked M x w L tape s,Assembly.jet_continuous_right (chart G n)
    ((Air.grade M q w staff L tape s).smooth.of_le le_top)]
  unfold Assembly.jet
  rw [(Air.grade M q w staff L tape s).vanish j hj]
  simp

include staff L tape in
theorem analytic : ContDiffAt ℝ ω C 0 := by
  rw [linked M x w L tape s]
  have hs : ContDiffAt ℝ ω (Bulk.projected ((Z).mark s)) (chart G n 0) := by
    simpa only [map_zero] using (Air.grade M q w staff L tape s).smooth
  exact hs.comp 0 (chart G n).contDiff.contDiffAt

end YM.Integration.WilsonEmittedRecordedJet
end
