import YM.RemainderComparison.Denom.Input
import YM.RemainderComparison.Fallow.Arrow
import YM.MergeProof.Wicket
import YM.RemainderComparison.Conditional
import YM.Next.RANK.Exponential
/-!
# Release of same-measure ratio to cumulant consumers

Budget reader can remain within connected terms and forced output; full derivative
statements on all seam fields are on the *entire* exact field. Do not take derivatives
inside its real polar organization at flagged or moving boundaries. No volume
normalization assumption. Even when using a chart to crop, ratio is on full cycle.
Actual window/conditional kernels in same Haar push; resources here consume full identity
and same p => characteristic loops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Denom
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby Passion
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat Passion.SeatD Fallow
open Next.Rank.Exponential MergeProof.Accent SectorNext.Vacuum
open GridRenewal.Rain PhysicalNext.Repeat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}{f:Side}{α:Type*}
variable (p:BudgetPoint) (T:Rep G n) (F:StepData n f) (R:ι→Support n)(Z:Set ι)
variable (H:Yard ι α G n)(a b:α)(β:ℝ)
variable [Fintype θ][DecidableEq θ]{J:Census θ}{q:θ→ℝ}{σ v:ℝ}{k:ℕ}
variable (z:ι→ Poly J)
local notation "d"=> H.gala T.p Z z a
local notation "P'"=> T.p
variable (W:Config G f→ Poly J)(V:Config G n) (E:Config G n→ Poly J)
local notation "U"=> F.push β W
local notation "x'"=> T.activities
structure Current (V : Config G n) : Prop where
    sumK : Summable (Yard.gala H T.p Z z a V)
    out : F.push β W V= Complex.ofReal (Real.exp (T.exponent V)) • (GridRenewal.Rain.cyclone (E V) * (∑' i, Yard.gala H T.p Z z a V i))
    still : (E V).part J.quiet=0
variable (hx: Passion.Oriented D J Z z)(hK:T.activities.K=Ethereal.dusk H Z b)(hζ:T.activities.forced=H.more)(h : Jolt.Orbit H Z)
variable (hC:Current T F Z H a β z W E V) -- autoImplicit order inspect
include hC h hζ hK hx
lemma currency : (F.push β W V).part J.quiet= (T.eval V:ℂ):=by
   rw [hC.out,Poly.part_smul, GridRenewal.Rain.passes (E V) hC.still, Poly.quiet_mul,Poly.pass_part _ hC.still, one_mul,Poly.share hC.sumK]; unfold Rep.eval; rw [Complex.ofReal_mul]; unfold Activities.gas; rw [Complex.ofReal_tsum]; simp_rw [Fallow.serene T.p Z J H a b V z hx T hζ hK h rfl]
omit hC h hζ hK hx
omit [Fintype θ] in
lemma onlyOne (hx:flags T.p.threshold V=∅): ∑' i,Yard.gala H T.p Z z a V i=1:=by
   rw [tsum_eq_single ∅]
   · have hh : (H.manifest a).admissible T.p V ∅ :=by simp [Activities.admissible,hx]
     simp [Yard.gala, Merge.Photo.fronts,hh]
   intro s hs; unfold Yard.gala Merge.Photo.fronts; rw [if_neg]
   intro he; obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr hs; obtain ⟨x,hx'⟩:= (H.more j).inventory_ne
   have hh : x∈ flags T.p.threshold V:= by rw [←he.2]; exact Finset.mem_biUnion.mpr ⟨j,hj,hx'⟩
   simp [hx] at hh

include hC
-- connected uniquely on all good mask. On FULL use Corona sectors & force. DO NOT DENOM BOUND AS VAC NONCONTRACTIVE.
local notation "Pn" => ((T.eval V:ℂ)⁻¹ • (F.push β W V))
lemma concurs (hv:flags T.p.threshold V=∅) : Expands (E V) ((T.eval V:ℂ)⁻¹ • F.push β W V):=by
   rw [hC.out, onlyOne T Z H a z V hv,mul_one, smul_smul]; unfold Rep.eval; rw [Activities.gas_one _ _ hv,mul_one]; let q:ℂ:= Complex.ofReal (Real.exp (T.exponent V))
   rw [inv_mul_cancel₀ (show q≠0 from Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),one_smul]; exact ⟨hC.still,(GridRenewal.Rain.passes _ hC.still).symm⟩

omit hC
variable {ψ: Config G f→ℝ} (hψ : ∀ i,(W i).part J.quiet= Complex.ofReal (ψ i))
include hψ
-- denominator extraction does NOT include Jacobian-choice fees.B.First.Eri. Probes against same input.Refine not requiring any precision distortion.RG02 bills.
omit [Fintype θ] in
lemma from_base (hh:Integrable W (prior G _))(h:F.IsKernel β G) : Poly.part (F.push β W V) J.quiet=(↑(F.push β ψ V):ℂ):=by
   rw [show (U V).part J.quiet= _ from congr_fun (MergeProof.Accent.push_get h hh J.quiet) V]; simp_rw [hψ]; unfold RG.StepData.push; apply Eq.trans (integral_congr_ae ?_) (integral_ofReal (μ:=Wilson.prior G f) (f:=fun i=> F.density β i V • ψ i) (𝕜:=ℂ))
   exact ae_of_all _ fun i=> (Complex.ofRealCLM.map_smul (F.density β i V) (ψ i)).symm
end YM.RemainderComparison.Denom
