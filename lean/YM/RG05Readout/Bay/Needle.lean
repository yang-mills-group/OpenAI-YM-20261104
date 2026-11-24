import YM.RG05Readout.Bay.Sachet
import YM.Contact.Detectors
import YM.Shift.Cut
/-! Local tensor bank. Spectral completeness is pinned on *actual* Wilson
 label field tables. Need a detection bank with actual positivity price on
 ONE fixed chamber of every root. Construct by zoom on the common final.
Smooth approximations suffice in that kernel; passage at detector-level
 then uses ordered TESTS not dynamics, projection ties harmless. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}(h:C.Makes)
set_option quotPrecheck false
open Extraction
local notation "α!"=> C.S.a
local notation "V"=> Fin n
local notation "E"=> Points n
open Metric
abbrev sand (x: E)(r:ℝ):Set (Points n):= {z |∀ i, dist (z i) (x i)≤r}

noncomputable def valve (x:E4)(C:Family G)(i:ℕ): ContDiffBump x:=⟨C.S.a i/32,C.S.a i/16,(by have h:=C.S.a_pos i; positivity),by have h:=C.S.a_pos i; linarith⟩
noncomputable def valves (x:E)(C:Family G)(i:ℕ)(z:E):= ∏ j:V,valve (x j) C i (z j)
noncomputable def fuel (x:E)(C:Family G)(i:ℕ):ℝ:=∫ z:E, valves x C i z
lemma smooth_t (x:E) : ContDiff ℝ ∞ (valves x C i):=by
   apply contDiff_prod (f:=fun j (z:Points n)=>valve (x j) C i (z j)); intro j _
   let S:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
   exact (valve (x j) C i).contDiff.comp (f:=fun z:E=> z j) ((contDiff_apply _ _ _).comp S.contDiff) -- arguments
lemma supports_valves (x:E) : tsupport (valves x C i)⊆ sand x (α! i/16):=by
    have he(t:ℝ):IsClosed (sand x t):=by
       rw [show sand x t=⋂ j: Fin n, {z : Points n | dist (z j) (x j)≤ t} from by ext; simp [sand]]; exact isClosed_iInter fun j=> isClosed_le (by fun_prop) continuous_const
    apply closure_minimal _ (he _); intro p hp j
    have hx: valve (x j) C i (p j)≠0:=by
       by_contra hz; exact hp (prod_eq_zero (Finset.mem_univ j) hz)
    have hv:= ContDiffBump.tsupport_eq (valve (x j) C i); exact mem_closedBall.mp (hv ▸ (show p j ∈ tsupport (valve (x j) C i) from subset_closure hx))
noncomputable def phiL (n:ℕ): (Points n)≃L[ℝ] (Fin n→E4):=PiLp.continuousLinearEquiv 2 ℝ _
noncomputable def cost (n:ℕ):= ‖(phiL n).symm.toContinuousLinearMap‖
lemma distance {x:E}{r:ℝ}(hr:0≤r) {z:E} (h:z∈ sand x r) : dist z x≤ cost n*r:=by
   let T:=phiL n; have ht: dist (T z) (T x)≤ r:=by
       rw [dist_eq_norm]; exact (pi_norm_le_iff_of_nonneg hr).2 fun i=> le_trans (le_of_eq (dist_eq_norm (z i) (x i)).symm) (h i)
   conv_lhs=> rw [← T.symm_apply_apply z, ← T.symm_apply_apply x]
   rw [dist_eq_norm,← map_sub]; rw [dist_eq_norm] at ht
   exact ((T.symm.toContinuousLinearMap).le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
lemma supports_t (x:E): HasCompactSupport (valves x C i):= (isCompact_closedBall x (cost n*(C.S.a i/16))).of_isClosed_subset (isClosed_tsupport _) fun _ hx=>mem_closedBall.mpr (distance (div_pos (C.S.a_pos _) (by norm_num)).le (supports_valves x hx))
lemma positive (x:E): 0 < fuel x C i:=by
   have ht (z:E): 0 ≤ valves x C i z:= prod_nonneg fun i _=>ContDiffBump.nonneg _
   have hv:= (smooth_t (i:=i) (C:=C) x).continuous; refine integral_pos_of_integrable_nonneg_nonzero hv (hv.integrable_of_hasCompactSupport (supports_t _)) ht (x:=x) ?_
   have hx: valves x C i x=1:= Finset.prod_eq_one fun j _=> ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall_self (div_pos (C.S.a_pos _) (by norm_num)).le)
   exact hx.symm ▸ one_ne_zero -- test

def Packet (x:E)(i:ℕ)(he:sand x (C.S.a i/16)⊆conf n): YM.Test n:=⟨fun z=> ↑((fuel x C i)⁻¹ * valves x C i z),Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (smooth_t x)),((supports_t (i:=i) (C:=C) x).comp_left (g:=fun z:ℝ=>(fuel x C i)⁻¹*z) (by simp)).comp_left (show ((↑(0:ℝ)):ℂ)=0 by norm_num),by
     have ht: Function.support (fun z=> ((↑((fuel x C i)⁻¹ * valves x C i z)):ℂ))⊆ Function.support (valves x C i):=fun p hp hz=> hp (by dsimp only; rw [show valves x C i p=0 from hz]; simp); exact (closure_mono ht).trans ((supports_valves x).trans he)⟩
-- general kernel continuity cost at fitting points. compact P.
lemma converging (x:E)(hm:x∈conf n) (y:ℕ→E) (hY:Tendsto y atTop (𝓝 x)) (K:Points n→ℂ)(hK:ContinuousOn K (conf n)) (ε:ℝ)(he:0<ε) : ∀ᶠ i:ℕ in atTop, ∃ h:sand (y i) (C.S.a i/16)⊆conf n, ‖(Packet (y i) i h).applyTo K-K x‖≤ε:=by
    have hA':{z : Points n | dist (K z) (K x) < ε}∈𝓝 x:=((hK x hm).tendsto.mono_left (by rw [nhdsWithin_eq_nhds.mpr ((conf_open _).mem_nhds hm)])).eventually (ball_mem_nhds _ he)
    obtain ⟨δ,hδ,h⟩:=Metric.mem_nhds_iff.mp (inter_mem ((conf_open _).mem_nhds hm) hA'); let a:= cost n; have ht:Tendsto (fun i=> a*(C.S.a i/16)) atTop (𝓝 0):=by simpa only [zero_div,mul_zero] using ((C.S.shrinks.div_const (16:ℝ)).const_mul a)
    filter_upwards [hY.eventually (ball_mem_nhds _ (half_pos hδ)),ht.eventually (gt_mem_nhds (half_pos hδ))] with i hi hp; let S:=y i; let X:= valves S C i; let c:= fuel S C i; let q:= C.S.a i/16; have hq:0≤q:= (div_pos (C.S.a_pos _) (by norm_num)).le
    have hx : sand S q ⊆ ball x δ:= fun z hz=> mem_ball.mpr (by have hP: dist z x≤ a*q + dist S x:= (dist_triangle z S x).trans (add_le_add_left (distance hq hz) _); linarith only [show dist S x<δ/2 from mem_ball.mp hi,hP,show a*q<δ/2 from hp])
    have hw:= hx.trans (h.trans inter_subset_left); refine ⟨hw,?_⟩; let F:(Points n)→ ℝ:= c⁻¹ • X; have hc:0<c:= positive S; have hX: Integrable X:= (smooth_t (i:=i) (C:=C) S).continuous.integrable_of_hasCompactSupport (supports_t S)
    have hF:Integrable F:= hX.const_mul _; have hb(z):0≤ F z:= mul_nonneg (inv_pos_of_pos hc).le (prod_nonneg (fun i _=> ContDiffBump.nonneg _))
    have hzT : ∫ z:(Points n), F z=1:=by
       change (∫ z:(Points n), c⁻¹* X z)=_; rw [integral_const_mul, show ∫ z:(Points n), X z=c from rfl, inv_mul_cancel₀ hc.ne']
    let W:= Packet (y i) i hw; have hP':Integrable (fun z=> W z*(K z-K x)):=by
       refine Test.smearing W (K:=fun z=> K z-K x) ?_; exact hK.sub continuousOn_const
    have heq : W.applyTo K-K x = ∫ z:E, W z*(K z-K x):=by
       simp_rw [mul_sub]; rw [integral_sub (Test.smearing W hK) (show Integrable (fun z=> W z*K x) from (hF.ofReal).mul_const _)]; rw [integral_mul_const, show ∫ z:E,W z= (1:ℂ) from ?_,one_mul]; rfl
       change (∫ z:E, (F z:ℂ))= _; rw [integral_complex_ofReal,hzT]; rfl
    rw [heq]; refine (norm_integral_le_integral_norm _).trans ((integral_mono (hP'.norm) (hF.mul_const ε) (fun z=>?_)).trans_eq ?_)
    · by_cases hT: X z=0
      · rw [show W z=0 from by change (↑(c⁻¹*X z):ℂ)=0; rw [hT];simp,zero_mul,norm_zero]; exact mul_nonneg (hb _) he.le
      rw [norm_mul,show W z=(F z:ℂ) from rfl, Complex.norm_real, Real.norm_of_nonneg (hb z)]; apply mul_le_mul_of_nonneg_left _ (hb _); rw [← dist_eq_norm]; exact (show dist (K z) (K x)< ε from (h (hx (supports_valves S (subset_closure hT)))).2).le
    rw [integral_mul_const,hzT,one_mul]
end YM.RG05Readout.Bay
