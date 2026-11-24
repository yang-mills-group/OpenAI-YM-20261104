import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNamedBasis
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestJet WilsonPointChildTestCoordinates WilsonCoeffUV.Wheel.Mark
variable {ι:Type}

def scroll (Y:Garden D):Scroll D:=⟨Y.val ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm,
  (show ContDiff ℝ (↑D) Y.val from Y.property).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm.contDiff⟩

theorem physical_scroll (Y:Garden D):physical (scroll Y)=portrait D Y:=by
  apply congrArg (portrait D)
  apply Subtype.ext
  funext x
  exact congrArg Y.val ((PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm_apply_apply x)

def basisScroll (D:ℕ)(t:Spring D):Scroll D:=scroll (Dawn.tint D t.val)
theorem basis_field (D:ℕ)(t:Spring D):physical (basisScroll D t)=cone D t.val:=physical_scroll _

def atom (h:ι → ℕ)(s:ι)(t:Spring (h s)):ℝ →L[ℝ] Pen h {s}:=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (petal h s (claim (h s) (finger (paper_fits t)) zeroC))

theorem tested (h:ι → ℕ)(s:ι)(t:Spring (h s))(V:Case h)(c:ℝ):
    touch V {s} (atom h s t c)=c*(claim (h s) (finger (paper_fits t)) zeroC (V s)):=by
  change (touch V {s}) (c • petal h s (claim (h s) (finger (paper_fits t)) zeroC))=_
  rw [map_smul,petal_hit,smul_eq_mul]
  
def issue (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(N j:ℕ)
    (v:Letter (R.family.labels.level k)):Era G (Pen h {s}):=
  ∑t:Spring (h s),tuftV (atom h s t) (WilsonPointChildPairedHistory.ledger R u depth N (N-j) j v (basisScroll _ t))

theorem authorized (R:Run G)(simple:G.Simple)(o:Loc G 1)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)
    (N j:ℕ)(live:j≤N)(v:Letter (R.family.labels.level k)):Auth k (issue R u k h s depth N j v):=by
  apply Auth.sum
  intro t _
  exact (WilsonPointChildPairedHistory.honest R u depth simple o N (N-j) j (by omega) v (basisScroll _ t)).tuft _
end YM.Integration.WilsonPointChildNamedBasis
