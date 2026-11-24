import YM.MSbar.Chord.Luna
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.Planned.ATOM_REGULAR_ESTIMATE.Norm
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Finset AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
variable {G:Gauge}{n:Side}{X:Support n}{p:BudgetPoint} {a:ℝ} {g:Config G n → ℝ}
local notation "S₀"=> Site n
local notation "E₀"=> Directions G n
local notation "T"=> Positions (Primary n G)
local notation "q₀"=> p.threshold
local notation "M"=> n.val
variable {o:Site n}{U:Config G n}(h:p.Regular X g)(he:Healthy p.threshold X U)(hv:p.supBounds o X g a)
open Next.Foundations Tensor
include h he hv
lemma all_chart {m:ℕ}(hx:m ≤ p.order): ‖iteratedFDeriv ℝ m (g∘increment U) 0‖ ≤ polarCost m*(a/p.threshold^m) := by
    let f:= g ∘ increment U; let A:=iteratedFDeriv ℝ m f 0; have hc:ContDiffAt ℝ m f 0:= (h.smooth U he).of_le (Nat.cast_le.mpr hx); have hp:=p.threshold_pos; refine op_polar (Analysis.sym_Jet hc) (div_nonneg hv.1 (pow_pos hp m|>.le)) ?_
    intro x hh; have hb : p.dirBound o (p.threshold • x):=by
        intro i; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hp.le]; exact mul_le_mul_of_nonneg_left (((norm_le_pi_norm x i).trans hh).trans (one_le_pow₀ (by simp))) hp.le
    have hz : ‖leftDerivs g (List.replicate m (p.threshold • x)) U‖ ≤ a:= hv.2 U he _ (by simpa using hx) (fun A ha=> ((List.mem_replicate.mp ha).2).symm ▸ hb)
    have ht : ‖Tensor.diagonal A (p.threshold • x)‖ ≤ a:=by
        rw [← show iteratedDeriv m (fun t:ℝ => g (increment U (t • (p.threshold • x)))) 0= diagonal A (p.threshold • x) from iteratedDeriv_on_line hc _]; have hh:=leftDerivs_diag (U:=U) (p.threshold •x) g m 0; rw [zero_smul,Work.G07.at_zero_increment] at hh; rwa [← hh]
    rw [Tensor.homogeneous,norm_smul, Real.norm_of_nonneg (pow_nonneg hp.le m)] at ht; rw [le_div_iff₀ (pow_pos hp m),mul_comm];exact ht
omit he h hv
-- any log.Bound independent periods. Original support useful after local.Mask flag Lipsch. constants
noncomputable def bendLog (G:Gauge)(u:G.El)(x:G.Color):=G.plog (G.mat (G.lieExp x*u⁻¹))
lemma paintsP (k:ℕ) (C:ℝ) (G: Gauge) :∃ V:ℝ, 0≤ V ∧ ∀ x: G.Color, ‖x‖ ≤ C→ Allows k (bendLog G (G.lieExp x)) x V:=by
    let Y:= Metric.closedBall (0:G.Color) C; obtain ⟨B,hB,hg⟩:= exists_allows (s:=Y) (isCompact_closedBall ..) (fun i _=>G.exp_jet.contDiffAt (x:=i)) k
    obtain ⟨D,hD,hd⟩:= exists_allows (s:={(1:G.Mat)}) isCompact_singleton (fun i hv=> ((Set.mem_singleton_iff.mp hv).symm ▸ G.plog_diff)) k
    obtain ⟨K,hK⟩:= isCompact_univ.exists_bound_of_continuousOn (f:=G.mat) G.continuous_mat.continuousOn; have hh(i) :‖G.mat i‖ ≤ 1+|K|:= (hK i (Set.mem_univ _)).trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))
    let F:= composeCost k D (2^k*B*(1+|K|)); refine ⟨F,by unfold F composeCost; positivity,fun x hx=>?_⟩
    let u:=G.lieExp x; let g(t:G.Color):=G.lieExp t*u⁻¹; have he:G.mat (g x)=1:= congr_arg G.mat (mul_inv_cancel u)|>.trans G.mat_one
    have hz := (hg x (Metric.mem_closedBall.mpr (show dist x 0≤ _ from by rw [dist_zero_right]; exact hx)))
    exact (show Allows k G.plog (G.mat (g x)) D from he.symm ▸ hd _ (Set.mem_singleton _)).comp (f:=fun y=>G.mat (g y)) (show Allows k (fun y=>G.mat (g y)) x _ from hz.times (f:=fun v:G.Color=>G.lieExp v) (g:=fun _=>u⁻¹) (allows_const x (hh u⁻¹)))
noncomputable def chartW(x y:T) : Directions G n:= fun e=> bendLog G (G.lieExp (panel G n x e)) (panel G n y e)
lemma pain(x:T) (F:Edge (Site n)): ‖panel G n x F‖ ≤ shade G * ‖x‖:= (norm_le_pi_norm (tint G (Exterior.Body 1 n) x) _).trans (tint_le _)
lemma birthday(x:T):chartW x x=0 :=by funext i; unfold chartW bendLog; rw [mul_inv_cancel,G.mat_one,G.plog_one];rfl
lemma account (k:ℕ)(G: Gauge) : ∃ A:ℝ, 0≤A ∧ ∀ (n:Side)(x:Positions (Primary n G)),‖x‖≤1→ Through k (chartW x) x A:=by
    let K:= shade G; have hk := shade_pos G; obtain ⟨V,hV,hG⟩:= paintsP k K G; let V':=composeCost k V K; have ht:0 ≤ V':=by unfold V' composeCost K; positivity
    refine ⟨V',ht,fun n x hx=>?_⟩; have h(i:Edge (Site n)): Allows k (fun z=> chartW x z i) x V':=by
        have hp:(‖panel G n x i‖) ≤ K := (pain x i).trans (mul_le_of_le_one_right hk.le hx)
        let A : Positions (Primary n G)→L[ℝ] G.Color := (ContinuousLinearMap.proj (R:=ℝ) i).comp (panel G n).toContinuousLinearMap
        exact (hG _ hp).comp (f:=fun y=> A y) (allows_linear (L:=A) (ContinuousLinearMap.opNorm_le_bound _ hk.le (fun z=>pain z i)) hp)
    exact Through.control (allows_pi ht h) -- edit
lemma bendUses (x:T) : (increment (increment 1 (panel G n x))) ∘ chartW x=ᶠ[𝓝 x] (fun v=>increment 1 (panel G n v)):=by
    let S(y:T)(p):=G.lieExp (panel G n y p) * (G.lieExp (panel G n x p))⁻¹; have hk(p):Tendsto (fun i=>S i p) (𝓝 x) (𝓝 1):=by rw [← show S x p=1 from mul_inv_cancel _]; exact ((G.lieExp_cont.comp ((continuous_apply p).comp (panel G n).continuous)).mul continuous_const).continuousAt -- prod order
    filter_upwards [eventually_all.mpr (fun i=> (hk i).eventually G.plog_right)] with i he; funext p; change G.lieExp (G.plog (G.mat (S i p))) * _ = _; rw [he p]; unfold S increment; simp
end YM.MSbar.Midpoint
