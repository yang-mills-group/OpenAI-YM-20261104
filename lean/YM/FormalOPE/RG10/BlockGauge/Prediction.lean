import YM.Work.F04.Choices
import YM.Push.LOOP_COEFFICIENT.Joint
import YM.Branch.Covariant
import YM.FormalOPE.RG10.Ward.Forces
/-!
 # The *formal-law* predictor on the finite orbifold regulator, genuine StepData germ

 Extend it AWAY from trivial orbit by a measurable gauge-covariant prescription (StepData with
 chosen tag fixed, restrict outputs to chosen representative of each unoriented coarse edge orbit
 before using this as an auxiliary Laplace system). This arbitrary choice is NOT part of the germs
 near the trivial orbit: there any tag gives the same predictor, and prediction genuinely respects
 inversion. Real RG articles use different period or generator and step away from identity--this
 is only for diagram evaluation. Never identify this regulator with C physical step. This auxiliary
 description pins the noise kernel normalizations per independent coarse link, not per full torus
 links. Tags kept available when used in fine integrals. No arbitrary minimizer used except with
 the given Branches assurance.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Function Finset PowerSeries Topology Metric Lattice Gauge RG Wilson MeasureTheory
open PertExtension PertExtension.Orb InversionWard Push.Loops
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge} {c f n:Side}
variable (S : StepData c f)
variable (H:S.patch.Branches S.kernel G)
variable (t:S.Choices)

abbrev LinkFrame (G:Gauge)(n: Side):= OEdge n → G.El
def atStep (U: LinkFrame G f) : LinkFrame G c := fun e=> S.prediction (Orb.liftLinks U) t e.val

lemma lifted_pred {U: Config G c} (h:retained U) : Orb.liftLinks (fun e : OEdge c=> U e.val)=U:= by
 funext i; unfold Orb.liftLinks; split
 · rename_i hi; change U (eR i)= _; rw [hi]
 rename_i hh
 have he: i= reflect (index i).val := by rw [show (index i).val=eR i from rfl, (eR_spec i).resolve_left hh, reflect_reflect]
 change (U (index i).val)⁻¹=U i; have ha: Orb.reflect i=(index i).val:= by conv_lhs=> rw [he]; exact reflect_reflect _
 exact (congrArg (fun v=> (U v)⁻¹) ha).symm.trans ((InversionWard.all_reversed i U).symm.trans (congr_fun h i))

include H
@[fun_prop] lemma atStep_meas : Measurable (atStep S t (G:=G)):= by apply measurable_pi_lambda; intro e; exact ((measurable_pi_apply _).comp (S.prediction_meas H t)).comp (Orb.lift_cont G).measurable
omit H in
private lemma lift_home : Orb.liftLinks (1:LinkFrame G n)=1 := by funext i; unfold Orb.liftLinks; split<;>simp -- omit H in
lemma unit_step : atStep (G:=G) S t 1 =1:= by funext i; unfold atStep; rw [lift_home]; exact Push.settled S H _ t
-- true step densities at flat use SAME tag in all factors. Uniform all common Choices here!
lemma all_t (u:Config G f) (hu:u=1) : ∀ᶠ U in 𝓝 u, ∀ t' : S.Choices, S.prediction U t'=S.prediction U t:= hu ▸ (Filter.eventually_all.mpr (fun t'=> Work.F04.prediction_germ H t' t))
lemma same_choice : ∀ᶠ U:LinkFrame G f in 𝓝 1, ∀ t':S.Choices, S.prediction (liftLinks U) t'= S.prediction (liftLinks U) t:= by
 have he: Tendsto (Orb.liftLinks (K:=G.El) (n:=f)) (𝓝 1) (𝓝 1):= lift_home ▸ (Orb.lift_cont G).continuousAt.tendsto -- inspect
 exact he.eventually (all_t S H t 1 rfl)
lemma respect_inv (he:_root_.Even f.val): ∀ᶠ U:LinkFrame G f in 𝓝 1, Orb.liftLinks (atStep S t U) = S.prediction (Orb.liftLinks U) t:= by
 filter_upwards [same_choice S H t] with U hu
 apply lifted_pred _ -- check arg
 have hn:= S.prediction_channel H inversion 0 (Orb.liftLinks U) t
 have hA : pull inversion 0 (liftLinks U) = liftLinks U:= mirrors he U
 rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero,hA,hu (S.withinChoice inversion 0 t)] at hn; exact hn.symm

-- projected body.Step gauge covariance on ENTIRE auxiliary integral, not full inversion
-- invariance away from saddle: don't use there.
 def even_spin (t:Site f→ G.El)(U:LinkFrame G f): LinkFrame G f:= fun e=> Lattice.gauge t (Orb.liftLinks U) e.val
lemma step_gauge (p:Site f→ G.El)(h: evenAt p)(U:LinkFrame G f) : atStep S t (even_spin p U)=even_spin (p∘ S.ratio.embed) (atStep S t U):= by
 funext e; unfold atStep even_spin; rw [show Orb.liftLinks _= Lattice.gauge p (Orb.liftLinks U) from funext (fun e=> (Orb.path_law p U h e).symm)]; unfold StepData.prediction;
 rw [S.updateGauged H, (S.patch.bond_gauge (h:=H) ..).2]; unfold Lattice.gauge; rw [lift_at]; rfl
end YM.FormalOPE.RG10.BlockGauge
