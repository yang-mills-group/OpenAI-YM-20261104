import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Realized
/-! # QScale trial, identity at these profiles and precision with genuine Guard applied.
- Trial based at r through exactly H there. ψ evaluated in the original conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh O.Read Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ}
    (N : WilsonPrescription G) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "X" => Scale.Measure.start N.scheme N.criterion
local notation "FX" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => Scale.Measure.adjust N.scheme N.criterion
local notation "Zf" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "ψ" => GroupS.ψ N.criterion M ν
variable (s:ℝ) {x:Points n} (hx:x∈conf n)

-- L is exactly the additional conversion put on these H inputs to the trial
-- estimate at x in s radius. Identity theorem uses `s` as η=−log T here.
-- No input that the engineering-home itself is calibrated at ψ.
def guardTrial (d:ℕ) := conversion Zf s d * stepV (ψ s) (mirror (W d))
include H
lemma base_adjust : Base (W d) := (Integration.WilsonPositionHomogeneousCoefficients.purchased N H).scheme d|>.scale
lemma structure_trial : Base (Zf s d * stepV (ψ s) (mirror (W d))) := ((H.dilation ν).check.paid s d).mul
    ((base_adjust N M H).rewind.switch ((H.dilation ν).check.led s).real)
lemma trial_advance : coeff 0 (guardTrial N ν M s d)=Level.Dial d s := by
  rw [guardTrial,conversion, mul_assoc, coeff_C_mul,(structure_trial N ν M H s).zero,mul_one]
lemma poseEq (d:ℕ) : actMark (stepV (ψ s) (mirror (W d))) (actMark (Zf s d) (scaling s (FX d)))= couple (ψ s) (X d) := by
  let F:= (H.dilation ν).check
  rw [F.reads,Facets.team (q:=ψ s) _ _ (F.led s).start,Scale.Measure.outlook,acts,(base_adjust N M H).turn',acts_h]
include hx
lemma scale_identity (u:Tags G d n) :
    Reg.Point.story (status (guardTrial N ν M s d) (fxt (FX d) (Real.exp (-s) • x))) u = (Reg.Point.story (fxt (X d) x) u).subst (ψ s) := by
  rw [ ← moves _ _ ((H.dilation ν).check.led s).start, ←fxt_c,←poseEq N ν M H s d,acts]
  have hy := Work.A05.smul_conf (Real.exp_pos (-s)) hx
  have he : status (guardTrial N ν M s d) (fxt (FX d) (Real.exp (-s) • x)) =
      fxt (actMark (Zf s d * stepV (ψ s) (mirror (W d))) (scaling s (FX d))) x := by
    funext j; ext1 v; simp only [fxt,dif_pos hy,dif_pos hx,actMark,seen,scale_at]
    apply Finset.sum_congr rfl; intro i _; apply congr_arg
    funext j; rw [pulseU,guardTrial,conversion,mul_assoc, coeff_C_mul]; rfl
  rw [he]

end YM.FVA2.GradedFar259.Quotes
