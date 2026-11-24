import YM.FormalOPE.RG10.OpenSlots.Field
/-!
 # Coordinates on all inversion link orbits, compared to the currently integrated slice.
 The truss pins only the interior forest at a stage (except at the terminal step).
 Use these coordinates for representing output polynomials on OFF-truss values as needed.
 No IR claims.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
 def firstBill : Flats G n→ ℝ:= Fabric.wilson ∘ expLinks G _
 lemma firstGranted : ContDiffAt ℝ ω (firstBill (n:=n) (G:=G)) 0:= by
    let a:= Orb.liftLinks ∘ expLinks G (Orb.OEdge n); have ha:MatDiffAt a 0:= BlockGauge.along neighborhood_exp
    have ht (u:Site n) (p): ContDiffAt ℝ ω (fun x:Flats G n=> G.mat (travel (a x) u p)) 0:= by
      induction p generalizing u with
      | nil=> exact contDiffAt_const
      | cons w v ih=>
         apply (show ContDiffAt ℝ ω (fun x=> G.mat (w.read (a x) u)) 0 from ?_).mul (ih _)
         unfold Step.read; split; exact mat_inv_diff (ha _); exact ha _
    change ContDiffAt ℝ ω (fun x:Flats G n=> Wilson.energy (a x)/2) 0; refine .div_const ?_ _; unfold Wilson.energy; exact ContDiffAt.sum (fun p _=> Push.Loops.price_diff (V:=fun x=> faceValue (a x) p) (ht ..))
 lemma first_held : Stationary (firstBill (n:=n) (G:=G)):= Inherit.stable firstGranted (by unfold firstBill; rw [Function.comp_apply,identity_zero, Fabric.prior_zero _ rfl]) (fun x=>div_nonneg (Wilson.energy_nonneg _) zero_le_two)

variable {L: Fabric G c} {S:StepData c f}(P:Inside S.ratio)(t:S.Choices)
local notation "F"=> Cross (G:=G) S P
 def substep : F × Flats G c→ℝ:= fun x=> BlockGauge.penalty S t (expLinks G _ (extend P x.1)) (expLinks G _ x.2)
variable (H:S.patch.Branches S.kernel G)
include H
lemma subReady : ContDiffAt ℝ ω (substep (G:=G) P t) 0:= by
 let a:= blankRight (G:=G) (S:=S) P; have hb (i: Orb.OEdge f): ContDiffAt ℝ ω ((fun v:Flats G f =>G.mat (expLinks G _ v i)) ∘ a) 0:= by
   exact (show ContDiffAt ℝ ω (fun v:Flats G f=>G.mat (expLinks G _ v i)) (a 0) from by rw [map_zero]; exact neighborhood_exp i).comp _ ((LinearMap.toContinuousLinearMap a).contDiff.contDiffAt)
 exact smooth_penalty S H t (show MatDiffAt (expLinks G _ ∘ a) 0 from hb) (show MatDiffAt (expLinks G _ ∘ (Prod.snd : F × Flats G c → Flats G c)) 0 from fun k=> (show ContDiffAt ℝ ω (fun v:Flats G c=> G.mat (expLinks G _ v k)) ((0:F × Flats G c).2) from neighborhood_exp k).comp (0:F × Flats G c) (show ContDiffAt ℝ ω (Prod.snd : F × Flats G c→Flats G c) 0 from contDiffAt_snd) ) (by change (expLinks G _ ∘ a) 0=1; simp only [comp_apply,map_zero,identity_zero])
lemma subStill : Stationary (substep (G:=G) P t):= Inherit.stable (subReady P t H) (by
     unfold substep BlockGauge.penalty BlockGauge.distance; change S.kernel.penalty*(∑ _, _) = 0; simp only [Prod.fst_zero, map_zero, Prod.snd_zero, identity_zero,unit_step S H t]; simp)
    (fun x=> mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun _ _=> (G.price_range _).1))
omit H
end YM.FormalOPE.RG10.OpenSlots
