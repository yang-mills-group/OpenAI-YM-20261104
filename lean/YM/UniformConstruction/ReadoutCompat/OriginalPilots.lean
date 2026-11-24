import YM.RG17.GateFlow
import YM.RG17.Launches
/-
# Sparse radiation at Pegs via finite separation stencil
Use fderiv approximations on EXACT F for moving shapes. All costs via B.
Leading point detection acquired at generic x (not literal separated 1,
needs nonprojection ties). Prepare the slightest countable regulator readout
again no local errors claimed. `scud` not assuming uniformly smooth
all families off stands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace MeasureTheory Next.UVStress Climb Cells
open PhysicalNext.Repeat.Legato Metric Lattice
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 1200000
variable {G:Gauge}{C:Family G}{S:Table C.book}{f: Extraction.Order}{F:Final C f S}{u:Filter (ℕ×ℕ)}{B:Lenses.Mantle F u}{L:Layout F} (E:Services C f S) {s:Extraction.Sequence}
set_option quotPrecheck false
local notation "M"=> Maxwell.freeTable C.labels
local notation "P"=> portal L
local notation "θ"=> role C
local notation "W"=> interval B s
variable {n:ℕ}{d:Fin n→ℕ} {K:Set (Points n)}
abbrev bright (C:Family G) := Points.gradient 0 timeAxis (Ward.disc (scalarCompar (C:=C)))
lemma starGate (C:Family G) (hG:G.Simple):∃ x∈generic 2, bright C x≠0:=by
    let z:=separated 1; have hz:= offsetConf zero_lt_one
    have ht:bright C z≠0:=by change Points.gradient .. ≠ _; rw [Trace.free_rate]; exact_mod_cast (show (8:ℝ)*theoryDensity G≠0 by positivity [theoryDensity_pos hG])
    have hh:ContinuousAt (bright C) z:= by
        have hv:= ((smoothDisc (T:=Maxwell.freeTable C.labels) (Maxwell.table_smooth _) (scalarCompar (C:=C))) z hz).contDiffAt ((conf_open _).mem_nhds hz)
        apply ((hv.fderiv_right (m:=∞) (by simp)).continuousAt).clm_apply continuousAt_const
    obtain ⟨x,hx,h⟩:= mem_closure_iff_nhds.mp ((Measure.dense_of_ae (almostGeneric 2)) z) _ (hh.tendsto.eventually_ne ht)
    exact ⟨x,h,hx⟩

abbrev sail (L:Layout F) (v:Labels M d)(r:ℝ)(x:Points n):ℂ := S.useAt S (r • x) (tags (d:=d) (fun i=> L.frame (d i) r (v i)))
lemma winds (v:Labels M d) {r:ℝ}(hr:0<r) : ContDiffOn ℝ ∞ (sail L v r) (conf _) := (S.class_smooth S F.room.kernel.smooth _).comp (show ContDiff ℝ ∞ (fun x:Points n=> r•x) by fun_prop).contDiffOn (fun _ h=> Work.A05.smul_conf hr h)

variable (h:Stands L B s)(v:Labels (Maxwell.freeTable C.labels) d)
include h E
open Ward
lemma scud (j:ℕ)(hs:IsCompact K)(hu:K⊆conf _){t:ℝ}(ht:0<t): ∀ᶠ r in interval B s,∀ x∈K, ‖iteratedFDeriv ℝ j (sail L v r) x-iteratedFDeriv ℝ j (disc (hang d v)) x‖ ≤ t := by
    let V k i:=(B.lens k (d i)).symm (Load.tent B k (d i) (v i)); have ht:= s.cofinal.eventually (B.uniformJets (p:=d) V v (fun i=> Load.seats B E (d:=d i) tendsto_const_nhds) j K hs hu t ht)
    rw [eventually_map]; filter_upwards [ht] with i hi x hx
    let r:= offsetPath B s i
    have he: sail L v r=Next.UVStress.tested (B.radius (s i)) (Lenses.testLens (B.lens (s i))) (hang d (V (s i))):=by
        funext y; unfold sail Next.UVStress.tested
        have h0 : tags (d:=d) (fun i=> L.frame (d i) r (v i))=panels (Lenses.testLens (B.lens (s i))) ∘ hang d (V (s i)):=by
           simp only [r,poised_here h]; exact funext fun j=>congr_arg (Sigma.mk (β:=S.Field) (d j)) (((B.lens (s i) (d j)).apply_symm_apply _).symm)
        rw [h0]; rfl
    rw [show sail _ _ _= _ from he]; exact hi x hx

local notation "Z!" => Ward.disc (hang d v)
lemma tightRope (hu:K⊆conf _)(hs:IsCompact K) (j:ℕ) : ∃ A:ℝ,0≤A ∧ ∀ᶠ r in W, ∀ x∈K,‖iteratedFDeriv ℝ j (sail L v r) x‖ ≤ A:=by
    have hp: ContinuousOn (iteratedFDeriv ℝ j Z!) (conf _):= fun x hx=> ((((smoothDisc (T:=Maxwell.freeTable C.labels) (Maxwell.table_smooth _) (hang d v)) x hx).contDiffAt ((conf_open _).mem_nhds hx)).continuousAt_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
    obtain ⟨c,hc⟩:= hs.exists_bound_of_continuousOn (hp.mono hu)
    refine ⟨1+max 0 c,by positivity,?_⟩
    filter_upwards [scud E h v j hs hu one_pos] with r hr x hx
    exact le_trans (norm_le_norm_sub_add ..) (add_le_add (hr x hx) ((hc x hx).trans (le_max_right ..)))

omit h E
private lemma bendOnce {y z:Points n}{k:ℝ}{i:Points n→ℂ} (h:∀ x∈K,ContDiffAt ℝ ∞ i x)(hm:∀ x∈K, ‖iteratedFDeriv ℝ 2 i x‖ ≤ k)(hp:0≤k)(hx:Convex ℝ K)(hy:y∈K)(hz:z∈K): ‖i z-i y-fderiv ℝ i y (z-y)‖ ≤ k*‖z-y‖^2:=by
    let g:= fderiv ℝ i; let H:=g y; let G(x:Points n) := i x - H x; let t:=‖z-y‖
    haveI : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
    let W' := K ∩ closedBall y t; have hY : y∈W':= ⟨hy,mem_closedBall_self (norm_nonneg _)⟩; have hZ : z∈W':= ⟨hz,by rw [mem_closedBall,dist_eq_norm]⟩
    have hv x (hh:x∈K): HasFDerivAt G (g x-H) x:= ((h x hh).differentiableAt (by simp)).hasFDerivAt.sub H.hasFDerivAt
    have he x (hh:x∈W'): ‖fderiv ℝ G x‖ ≤ k*t:=by
        refine ((hv x hh.1).fderiv ▸ (?_ : ‖g x-H‖ ≤ k*t)); refine le_trans (hx.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=g) ?_ ?_ hy hh.1) (mul_le_mul_of_nonneg_left ?_ hp)
        · intro i hi; exact ((h i hi).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
        · intro x h; unfold g; rw [← norm_iteratedFDeriv_one _,norm_iteratedFDeriv_fderiv]; exact hm x h
        exact (dist_eq_norm x y).symm.trans_le hh.2
    rw [show i z-_ -_=G z-G y from ?_ ]; swap
    · unfold G H g; rw [map_sub]; abel
    exact ((hx.inter (convex_closedBall y t)).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=G) (fun i hi=> (hv i hi.1).differentiableAt) he hY hZ).trans_eq (by unfold t; ring)

variable (Z:Ledger L)(fx:Flick C.path.levels){x:Points n}
abbrev ay (C:Family G)(x:Points n)(r:ℝ):= tag (role C r) (baseRail C x r)
abbrev bee (C:Family G)(x:Points n)(i:Fin n)(j:Axis)(r:ℝ):= tag (role C r) (nextRail C x i j r)
abbrev sightDiff (C:Family G)(x:Points n)(i:Fin n)(j:Axis) (g:ℝ→Points n→ℂ)(r:ℝ):ℂ:= (role C r)⁻¹ • (g r (bee C x i j r)-g r (ay C x r))
include Z fx E h v
lemma flashed (hx:x∈conf _)(i:Fin n)(j:Axis) : Tendsto (fun r=> (sightDiff C x i j (sail L v) r - Points.gradient i j (sail L v r) (ay C x r))/(Z.g r:ℂ)^2) W (𝓝 0):=by
   have ht : W ≤ home:= (homes B).comp s.cofinal
   obtain ⟨t,hy,H⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open _).mem_nhds hx); let V:= closedBall x t
   obtain ⟨a,ha,hA⟩:= tightRope E h v H (isCompact_closedBall x t) 2
   let m:=Points.direction i j
   refine squeeze_zero_norm' (a:=fun r=> (a * ‖m‖^2)*(role C r / Z.g r^2)) ?_ (by simpa only [mul_zero] using (closesSmaller Z fx|>.mono_left ht).const_mul (a*‖m‖^2))
   filter_upwards [hA,positiveLength.filter_mono ht, ((reachesBase Z fx x).mono_left ht).eventually (closedBall_mem_nhds _ hy), ((reachesNext Z fx x i j).mono_left ht).eventually (closedBall_mem_nhds _ hy)] with r hr he hu hq
   let y:=ay C x r; let z:=bee C x i j r
   let R:=sail L v r; let δ:= role C r; let g:= Z.g r
   have hg:0<g:=Z.positive r; have hd : 0 < δ:= div_pos (C.S.a_pos _) he
   have hh:= bendOnce (K:=V) (y:=y) (z:=z) (i:=R) (fun x hx=> (winds v he x (H hx)|>.contDiffAt ((conf_open _).mem_nhds (H hx)))) hr ha (convex_closedBall _ _) hu hq
   have hv:z-y=δ • m := by unfold z bee; rw [leapsOnce he]; exact add_sub_cancel_left ..
   change ‖(δ⁻¹ • (R z-R y)-fderiv ℝ R y m)/(g:ℂ)^2‖ ≤ (a*‖m‖^2)*(δ / g^2)
   rw [hv,map_smul,norm_smul,Real.norm_of_nonneg hd.le] at hh
   rw [norm_div, show (_:ℂ)-_=δ⁻¹ • (R z-R y-δ • fderiv ℝ R y m) from ?_,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hd).le, norm_pow, Complex.norm_real, Real.norm_of_nonneg hg.le]; swap
   · simp only [smul_sub, inv_smul_smul₀ hd.ne']
   exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hd).le) (sq_nonneg _)).trans_eq (by field_simp)

lemma rides (hx:x∈conf _)(i:Fin n)(j:Axis) : Tendsto (fun r=> Points.gradient i j (sail L v r) (ay C x r)) W (𝓝 (Points.gradient i j Z! x)):=by
   have ht : W ≤ home:= (homes B).comp s.cofinal
   obtain ⟨t,hy,H⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open _).mem_nhds hx)
   let A:= ay C x
   have hA:Tendsto A W (𝓝 x):=(reachesBase Z fx x).mono_left ht
   have hz (x:Points n)(hx:x∈conf _): ContDiffAt ℝ ∞ Z! x:= ((smoothDisc (T:=Maxwell.freeTable C.labels) (Maxwell.table_smooth _) (hang d v)) x hx).contDiffAt ((conf_open _).mem_nhds hx)
   have hp:Tendsto (fun r=> fderiv ℝ (sail L v r) (A r)-fderiv ℝ Z! (A r)) W (𝓝 0):=by
      rw [Metric.tendsto_nhds]; intro ε he
      filter_upwards [positiveLength.filter_mono ht,hA.eventually (closedBall_mem_nhds _ hy), scud E h v 1 (isCompact_closedBall x t) H (half_pos he)] with r hr hf hQ
      let a:= A r; have hh:= hz a (H hf); have hy: ContDiffAt ℝ ∞ (sail L v r) a:= (winds v hr a (H hf)|>.contDiffAt ((conf_open _).mem_nhds (H hf)))
      specialize hQ a hf; rw [dist_zero_right,← fderiv_sub (hy.differentiableAt (by simp)) (hh.differentiableAt (by simp)),← norm_iteratedFDeriv_one _,iteratedFDeriv_sub_apply (hy.of_le (by simp)) (hh.of_le (by simp))]; exact hQ.trans_lt (half_lt_self he)
   have h' := hp.add (((hz _ hx).fderiv_right (m:=∞) (by simp)).continuousAt.tendsto.comp hA)
   rw [zero_add] at h'; simp only [Function.comp_apply,sub_add_cancel] at h'
   exact (ContinuousLinearMap.apply ℝ ℂ (Points.direction i j)).continuous.continuousAt.tendsto.comp h'
end YM.RG17
