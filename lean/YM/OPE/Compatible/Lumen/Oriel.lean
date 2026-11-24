import YM.OPE.Compatible.Lumen.Pass
/-!
# Adding analytic boost quotient
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive Matrix
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (H: Even n.val) (A:Alps B Q i l)
local notation "TK" => Keys G (Limb H)
def hippie (x:TK):ℝ:= rainbow (rinse H x) (rinse H x)/2
@[simp] lemma hZero : hippie H (0:TK)=0:=by simp [hippie, rainbow]
lemma hSm : ContDiff ℝ ω (hippie H (G:=G)):=by
      unfold hippie rainbow; apply ContDiff.div_const; apply ContDiff.sum; intro i _; let f:=fun x:TK=> rinse H x i; have hf:ContDiff ℝ ω f:= (contDiff_apply ..).comp ((LinearMap.toContinuousLinearMap (rinse H (G:=G))).contDiff); exact hf.inner ℝ hf
-- pure quadratic
lemma h_degree (x: TK)(t:ℝ): hippie H (t • x)=t^2*hippie H x:=by unfold hippie rainbow; simp [norm_smul,mul_pow,←Finset.mul_sum];ring
lemma h_station: Radial.Stationary (hippie H (G:=G)):=by
      refine ⟨(hSm H).contDiffAt.of_le le_top,hZero H,fun x=>?_⟩; rw [Radial.homogeneous_derivative _ _ _ ((hSm H).contDiffAt.of_le le_top)]; simp_rw [h_degree]; simp only [iteratedDeriv_one]; rw [deriv_fun_mul,deriv_const,deriv_fun_pow]; all_goals first | fun_prop | norm_num
lemma h_second (x:TK): Radial.jet (hippie H) 2 x= hippie H x:=by
      have hp: Reads (fun t:ℝ=> hippie H (t • x)/t^2) _:= (Pawn.trio (h_station H)).stale x; have hh:Tendsto (fun t:ℝ=> hippie H (t • x)/t^2) Tested.germ (𝓝 (hippie H x)):= by apply tendsto_const_nhds.congr'; filter_upwards [Tested.eventually_pos] with t ht; rw [h_degree]; field_simp
      exact tendsto_nhds_unique hp.limit hh
-- ambient curvature
lemma mural_bank (x:TK)(h:i ≥4): (Radial.jet (mural H A) 2 x) =
      (∑ j:G.ColorIndex, parts G 1 (cloak H x) j ⬝ᵥ (A.root.acts n *ᵥ parts G 1 (cloak H x) j))/8:=by
     let f:= frameD A (n:=n); let L:= cloak (G:=G) H; let P:=f ∘ L
     have hh : ContDiffAt ℝ ω P 0:= ((show ContDiffAt ℝ ω f (L 0) from L.map_zero.symm ▸ (A.fullK 1).plot n).comp _ L.contDiff.contDiffAt); unfold Radial.jet
     rw [show mural H A=(4:ℝ)⁻¹ • P from funext fun i=>by rw [Pi.smul_apply,smul_eq_mul,mul_comm]; exact div_eq_mul_inv ..,iteratedFDeriv_const_smul_apply (hh.of_le le_top)]
     rw [show P=f ∘ L from rfl, Next.Foundations.jets_linear L (((A.fullK 1).plot n).of_le le_top)]
     change _* ((4:ℝ)⁻¹ * iteratedFDeriv ℝ 2 _ _ (fun _=> L x))= _; rw [show (fun _:Fin 2=> L x)=![L x,L x] from funext fun i=>by fin_cases i<;>rfl,A.inkTot h n,component_dot]; simp_rw [component_mul]; let D:= (∑ j:G.ColorIndex, parts G 1 (cloak H x) j ⬝ᵥ (A.root.acts n *ᵥ parts G 1 (cloak H x) j)); change _*(_*D)=D/_; norm_num;ring
lemma mural_in (x:TK)(h:i≥4): Radial.jet (mural H A) 2 x+hippie H x=(boost H A.gear h B.K).P x x/2:=by
      rw [mural_bank H A x h, boost_price]; unfold flag; simp only; rw [major]; let M:= MSbar.Tree.Resolvent.grad n; let y(p:G.ColorIndex):= parts G 1 (cloak H x) p; let U(p):= Mᵀ *ᵥ y p
      simp_rw [Matrix.add_mulVec,dotProduct_add,Finset.sum_add_distrib]; rw [show (∑ i:G.ColorIndex, y i ⬝ᵥ ((M*Mᵀ) *ᵥ y i))=∑ i:G.ColorIndex, U i ⬝ᵥ U i from Finset.sum_congr rfl (fun i _=>by rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]; rw [show y i ᵥ* M=Mᵀ*ᵥ y i from (mulVec_transpose ..).symm])]
      unfold hippie rainbow; rw [rainbook]; change _ = ((∑ j:G.ColorIndex,y j ⬝ᵥ _)+ _)/_/_; ring
end YM.OPE.Cascade.Glass
