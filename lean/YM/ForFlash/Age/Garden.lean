import YM.ForFlash.F9.Pads
import YM.SignedWilsonExpansion.Camera.Pad
import YM.ForFlash.Age.Distances
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.SignedWilsonExpansion.Camera
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice Schedules HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Dancer.Shell Dancer.Fort XSpace.Cirrus
open Kane.Tilted Belle Belfry Belfry.ScaleFits StageG
open scoped Topology ContDiff Classical BigOperators
namespace FlightForFlash
open Fire Fire.RoadForFlash
variable {G:Gauge}{d b e:ℝ}{n:ℕ}
abbrev rack := (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm.toContinuousLinearMap
def dimensionBill:ℝ:= max 1 ‖rack‖
lemma paidDim : 0<dimensionBill:= zero_lt_one.trans_le (le_max_left ..)
lemma cubeH (z:EuclideanSpace ℝ Axis): ‖WithLp.ofLp z‖≤ ‖z‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun k=> PiLp.norm_apply_le z k)
lemma cubeP (z:EuclideanSpace ℝ Axis): ‖z‖≤ dimensionBill*‖WithLp.ofLp z‖:=
   (rack.le_opNorm (WithLp.ofLp z)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
-- Declare bound in absolute units (meters-cubed not being reissued).
def PaidSize (S:Schedule)(f:ℕ)(x:Shake (n:=n))(length gap:ℝ):Prop:=
   (∀ i, ‖S.gridPoint f (x i)‖ ≤ length) ∧ Pairwise fun i j=>gap ≤ ‖S.gridPoint f (x i)-S.gridPoint f (x j)‖
variable {L' r A:ℝ}{C:Family G}{S:Schedule}{f:ℕ}{x: Shake (n:=n)}
lemma paidNorm (hr:0<r) (hi:InWidth d b (Extraction.tag (S.a f/r) x)) : PaidSize S f x (dimensionBill*(r*b)) (d*r):=by
   let Y:= Extraction.tag (S.a f/r) x
   have eq(i): S.gridPoint f (x i)=r • Y i:=by
      apply PiLp.ext; intro a; change S.a f*(x i a:ℝ)= r*(( S.a f/r )*( x i a:ℝ )); field_simp
   constructor
   · intro i; rw [eq,norm_smul,Real.norm_of_nonneg hr.le,mul_left_comm]; exact mul_le_mul_of_nonneg_left ( (cubeP ( Y i )).trans (mul_le_mul_of_nonneg_left ( hi.far i ) paidDim.le) ) hr.le
   intro i j h; rw [eq,eq, ←smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm d]; refine mul_le_mul_of_nonneg_left (( hi.gap i j h ).trans ?_) hr.le; unfold cubedist; rw [dist_eq_norm]; exact cubeH (Y i-Y j)
lemma PaidSize.more (h:PaidSize S f x b d)(h1:b≤L')(h2:A≤d): PaidSize S f x L' A:= ⟨fun i=>(h.1 i).trans h1, fun _ _ h'=>h2.trans ( h.2 h' )⟩
variable {ι:Type} {L:Filter ι}{w:ℝ} {r₁ r₂:ι→ℝ} {f':ι→ℕ}{x':ι→Shake (n:=n)}
include w
lemma marked {a:ℝ}(h:G.Simple)(hr:Tendsto r₁ L trail)(hd:0<d)(hw:0<w)
   (hx: InBWidth d a (cck G∘r₁) (plot r₁ f' x' S) L)(hp:(r₁*payD (cck G∘r₁) a) ≤ᶠ[L] r₂):
   ∀ᶠ i in L,PaidSize S (f' i) (x' i) (dimensionBill*r₂ i) (spare G w r₁ i):=by
   filter_upwards [hr.eventually self_mem_nhdsWithin,hx,hp,shrink₁ h hr hw hd] with i hr hi hp hd; exact ( paidNorm hr hi ).more (mul_le_mul_of_nonneg_left hp paidDim.le) hd
end FlightForFlash
end YM.SignedWilsonExpansion.Camera
end
