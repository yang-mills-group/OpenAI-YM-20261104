import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogLink
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.Extra.MULTISOURCE_TRAJECTORIES.Smooth
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Meristem
/-!
 # An all-field model summand for orienting the actual primitive
 Fixed patch ANY radius; not using analyticity of representation chosen
 on orbit. Construct gauge-invariant smooth function that reduces locally
 to the specified formula using genuine Lie links. Do not average model by
 conditional law; AFTER solving formal coefficient query, demand real
 completion averaging over ONE residual compact group (prob mass 1). Marker
 unaffected. Exact support in AUX torus; use Trio.ornament for big torus.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Gauze
open Filter Function Metric Lattice Wilson RG Push Push.AbsoluteSums
open Pressure Precision Exterior ConnectedActivityE6 Channel SliceRows
open PhysicalNext PhysicalNext.Repeat Boulevard Blaze Brush
open Uniform MeasureTheory Matrix Extra.Trajectories Next.Fluctuations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c f: Side} {B : BudgetPoint}
local notation "X"=>Positions (Uniform.Primary c G)
-- Here 'wide': extension ONLY used to book an estimator, never change kernels.
structure Snip (G : Gauge) where
   size : ℝ
   pos : 0<size
   out : G.Mat → G.Color
   smooth : ContDiff ℝ ∞ out
   stays w : ‖w-1‖ ≤ size → out w=G.plog w

attribute [local instance] Gauge.frobInner in
lemma whittle (G : Gauge) : Nonempty (Snip G):= by
   obtain ⟨v,hv,h⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 (G.plog_diff.eventually (by simp)); let d: ContDiffBump (1:G.Mat):=⟨v/2,v,half_pos hv,by linarith⟩
   refine ⟨⟨d.rIn,d.rIn_pos,fun w=> d w • G.plog w,contDiff_iff_contDiffAt.mpr fun i=> ?_,fun w hw=> ?_⟩⟩
   · by_cases he:i ∈ closedBall (1:G.Mat) d.rOut
     · exact d.contDiffAt.smul ((h he).of_le (show (∞:ℕ∞ω)≤ω from le_top))
     refine (contDiffAt_const (c:=(0:G.Color))).congr_of_eventuallyEq ?_
     filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp (d.tsupport_eq.symm ▸ he))] with u hu
     rw [show d u=0 from hu,zero_smul]
   rw [d.one_of_mem_closedBall (mem_closedBall_iff_norm.mpr hw),one_smul]
section field
def prong (W:Extra.Trajectories.Field G c) (x : Site c) (e:Lattice.Step) := if e.neg then star (W (e.used x)) else W (e.used x)
@[simp] lemma prong_mat (W:Config G c)(i:Site c)(j): prong (matrixField W) i j= G.mat (j.read W i):= by unfold prong Lattice.Step.read; split_ifs <;> rfl

def rode (W : Extra.Trajectories.Field G c) (x:Site c) : Walk→ G.Mat
   | []=>1
   | h::t=> prong W x h * rode W (x+h.vec) t
lemma rode_mat (U:Config G c)(x:Site c)(W:Walk): rode (matrixField U) x W= G.mat (travel U x W):= by
   induction W generalizing x <;> simp_all only [rode, travel, G.mat_one,G.mat_mul,prong_mat]
@[fun_prop] lemma rode_cd (W: Walk)(x:Site c) : ContDiff ℝ ∞ (fun P:Extra.Trajectories.Field G c=> rode P x W):= by
   induction W generalizing x with
   | nil=> exact contDiff_const
   | cons h t ih=>
      apply ContDiff.mul _ (ih _); unfold prong; split
      · exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (contDiff_apply ..))
      exact contDiff_apply ..
-- auxiliary map; repeated coordinate tree. 
def epoxy (T:Snip G) (U:Extra.Trajectories.Field G c) (a:G.Mat) : Positions (Uniform.Primary c G) := (Uniform.tint G _).symm (SliceRows.toLog (fun i:Bond c=> T.out (a*((rode U 0 (carriage 0 i.1))*U i*star (rode U 0 (carriage 0 (i.1+Lattice.step i.2))))*star a)))

def castle (U: Config G c) (a:G.El):Config G c := gauge (fun _=> a) (gauge (SliceRows.carrier 0 U) U)
local notation "D₀" => Gauge.frobInner
lemma castle_eq (U : Config G c)(a:G.El)(o:Site c→ G.El): castle (gauge o U) a=castle U (a*o 0):= by
   funext i; simp only [castle,Lattice.gauge,SliceRows.carrier]; -- CAR issue unfolds too much
   have ht (j : Site c): travel (Lattice.gauge o U) (0:Site c) (carriage 0 j)=o 0*travel U 0 (carriage 0 j)*(o j)⁻¹:= by
     rw [travel_gauge, SliceRows.deposits]
   rw [ht,ht]; group
@[fun_prop] theorem epoxy_ready (T:Snip G): ContDiff ℝ ∞ (fun p : Extra.Trajectories.Field G c × G.Mat=> epoxy T p.1 p.2):= by
  let F (x:G.Mat):=star x; have he:ContDiff ℝ ∞ F:= (starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff
  unfold epoxy; refine ((tint G (Body 1 c)).symm.contDiff (n:=∞)).comp (contDiff_pi.mpr (fun i=> T.smooth.comp ?_))
  exact ((contDiff_snd.mul (((rode_cd ..).comp contDiff_fst|>.mul ((contDiff_apply ..).comp contDiff_fst)).mul (he.comp ((rode_cd ..).comp contDiff_fst)))).mul (he.comp contDiff_snd))

def putty (T: Snip G) (U: Config G c) (a:G.El) : X:= epoxy T (matrixField U) (G.mat a)
lemma putty_eq (T: Snip G) (U: Config G c) (a:G.El): putty T U a=(tint G _).symm (toLog fun i:Bond c=> T.out (G.mat (castle U a i))):= by simp only [putty,epoxy, castle,Lattice.gauge, carrier,rode_mat,G.mat_mul,G.mat_inv]; rfl

abbrev resin (T:Snip G) (f:X→ℝ)(U:Config G c):= ∫ a:G.El, f (putty T U a) ∂G.probHaar
lemma resin_gauge (T:Snip G)(f:X→ℝ): GaugeInvariant (resin T (c:=c) f):= by
   intro t U; unfold resin; simp_rw [putty_eq, castle_eq]; exact (measurePreserving_mul_right G.probHaar (t 0)).integral_comp (Homeomorph.mulRight (t 0)).measurableEmbedding (fun x=> f ((Uniform.tint G _).symm (toLog fun i=> T.out (G.mat (castle U x i)))))
lemma integrable_resin (T:Snip G){f:X→ℝ}(hf: Continuous f)(U:Config G c): Integrable (fun a=> f (putty T U a)) G.probHaar:= by
   have he: Continuous (fun (a:G.El)=> putty T U a):= (epoxy_ready T).continuous.comp (f:=fun a=>(matrixField U,G.mat a)) (continuous_const.prodMk G.continuous_mat); exact (hf.comp he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma resin_ready (T:Snip G) (f:X→ℝ) (h:ContDiff ℝ ∞ f) : B.Regular Finset.univ (resin T f (c:=c)):= by
   haveI : TopologicalSpace.PseudoMetrizableSpace G.Mat:= inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin G.repDim → Fin G.repDim → ℂ)); let X' (U:Extra.Trajectories.Field G c):=∫ a:G.El,f (epoxy T U (G.mat a)) ∂G.probHaar
   have hX:ContDiff ℝ ∞ X':= Extra.Trajectories.integral_smooth (p:=G.mat) G.continuous_mat.aestronglyMeasurable (isCompact_range G.continuous_mat) (fun i=>Set.mem_range_self _) (h.comp (epoxy_ready T))
   have hh (U:Config G c) : ContDiffAt ℝ B.order (fun i=> X' (matrixField (increment U i))) 0:= (contDiff_infty.mp (hX.comp (Extra.Trajectories.shift_smooth.comp (contDiff_const.prodMk contDiff_id))) B.order).contDiffAt
   exact ⟨fun U W h=> congr_arg _ (funext fun i=>h i (Finset.mem_univ _) (Finset.mem_univ _)),(hX.continuous.comp matrixField_cont).measurable,resin_gauge T f,fun U _=>hh U,fun U _ x _ he=> Next.Foundations.left_has x he (hh U)⟩
end field
end YM.Juniper.Gauze
