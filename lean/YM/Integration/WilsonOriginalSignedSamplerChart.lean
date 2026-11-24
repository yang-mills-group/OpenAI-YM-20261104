import YM.Integration.WilsonOriginalSignedFullMatrix
import YM.Integration.OriginalMarkedHeatCovariance
import YM.WilsonCoeffUV.Step.Source

/-! The shared finite chart of the original all-path affine Gaussian and
the vacuum and marked Wick prescriptions on its actual forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedSamplerChart
open Function Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix Bloch
open Pressure Pressure.Testing PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent
open FreeResolvent.Affine WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G) (N m per : ℕ) (hm : m < N)
local notation "a" => R.family.path.levels
set_option quotPrecheck false in
local notation "Δ" => (a).clock.op m per
local notation "T" => ships R.alloy.B N m per
local notation "A" => R.alloy.B.M.H N (m+1)
local notation "Y" => RunFormalChain.fromRun R
set_option quotPrecheck false in
local notation "W₀" => installed (Δ).ratio (R.alloy.B.M.towers N m).A0
set_option quotPrecheck false in
local notation "W₁" => installed (Δ).ratio (predictionA (a) N m)
variable (F : Forest (R.family.path.levels.clock.op m per).ratio)
  (tag : (R.family.path.levels.clock.op m per).Choices)

theorem covariance : ((Y).step N m per hm).covariance F tag =
    (primary (Δ) F tag (T).high (T).up all 0)⁻¹ := by
  have born : primary (Δ) F tag (T).high (T).up all 0 = treeMatrix G (Δ) F (A).metric :=
    WilsonOriginalSignedFullMatrix.original R N m per hm F tag
  rw [born]
  unfold Bulk.Kernel.covariance
  have home := (CommonConstruction.runAlong R).home (N:=N) (m:=m) (p:=per) F hm
  have hp : Bid.Prismatic (S:=(Δ)) (G:=G) F ((a).params (m+1)).clip (R.family.path.rep N per (m+1)).path :=
    fun i => (home.2.1.2.2 i).1
  rw [(Y).clips N per (m+1) hm]
  exact congrArg Inv.inv (FreeResolvent.Tests.checked_loop (S:=(Δ)) (G:=G) F (A) tag _ _ hp home.2.2.1)

include hm in
theorem ambient : FreeResolvent.covariance G (Δ) F (A).metric =
    FreeResolvent.covariance G (Δ) F (freeForms (a) N (m+1)) := by
  have h : Precision.K ((A).metric.acts ((a).clock.schedule.side (m+1) per)) =
      Precision.K ((freeForms (a) N (m+1)).acts ((a).clock.schedule.side (m+1) per)) :=
    UVExt.horizon_exact (N:=N) (m:=m+1) (p:=per) R.alloy.B.M R.alloy.B.plan hm
  unfold FreeResolvent.covariance treeInverse treeMatrix fullMatrix baseMatrix
  rw [h]

include hm tag in
/-- All named rows and columns in either finite source may be submitted
without reselecting the prior or its fluctuation law. -/
theorem original (Φ : ChartRatio G) (P w : PChart G ((a).S.side (m+1) per)) :
    (camSlice G (Δ) F (extractV G (Δ) F (W₀)) = camSlice G (Δ) F (extractV G (Δ) F (W₁))) ∧
    inside (Δ) F (A).metric (W₀) Φ P =
      inside (Δ) F (freeForms (a) N (m+1)) (W₁) Φ P ∧
    insideMark (Δ) F (A).metric (W₀) Φ P w =
      insideMark (Δ) F (freeForms (a) N (m+1)) (W₁) Φ P w ∧
    winter (Δ) F (A).metric (freeForms (a) N m) (W₀) Φ P =
      winter (Δ) F (freeForms (a) N (m+1)) (freeForms (a) N m) (W₁) Φ P := by
  have pic : extractV G (Δ) F (W₀) = extractV G (Δ) F (W₁) :=
    OriginalMarkedHeatCovariance.affineMatrix R N m per hm F tag
  have actual := covariance R N m per hm F tag
  have born : primary (Δ) F tag (T).high (T).up all 0 = treeMatrix G (Δ) F (A).metric :=
    WilsonOriginalSignedFullMatrix.original R N m per hm F tag
  rw [born] at actual
  have inv : treeInverse G (Δ) F (A).metric 0 = treeInverse G (Δ) F (freeForms (a) N (m+1)) 0 := by
    rw [← OriginalMarkedHeatCovariance.activeCovariance R N m per hm F tag,actual]
    simp [treeInverse,FreeResolvent.resolve]
  refine ⟨congrArg (camSlice G (Δ) F) pic, ?_, ?_, ?_⟩
  · rw [inside,inside,shot,shot,inv,pic]
  · rw [insideMark,insideMark,shot,shot,inv,pic]
  · have eat : summer (Δ) F (A).metric (W₀) Φ P = summer (Δ) F (freeForms (a) N (m+1)) (W₁) Φ P := by
      funext i
      simp only [summer,xray,ambient R N m per hm F,pic]
    rw [winter,winter,eat]

end YM.Integration.WilsonOriginalSignedSamplerChart
