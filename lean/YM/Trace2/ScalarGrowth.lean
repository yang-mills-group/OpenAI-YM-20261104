import YM.Trace2.QuotedLimit
set_option autoImplicit false
set_option maxHeartbeats 330000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4500
noncomputable section
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
local notation "fb" => Bel C.book
local notation "scalarF" => scalarLabel C.labels
variable (A : PertExtension.Actual C φ S)
local notation "𝒜" => A.F.room.kernel
structure Fixedτ (w:S.Field 4): Prop where
   centered : expectation S 4 w=0
   mirrors (s): S.mirror A.F.room.kernel.spin 4 s w=w
   realVal : S.conj A.F.room.kernel.spin 4 w=w

namespace Fixedτ
variable {A}
lemma fixed_center {w : S.Field 4}(hw:∀ s,S.mirror A.F.room.kernel.spin 4 s w=w)(hStar:S.conj A.F.room.kernel.spin 4 w=w): Fixedτ A (centering S 4 w):=
    ⟨centers_field A.F.room.kernel.laws _,fun s=>(mirror_center (A.F.room.kernel) w s).trans (congr_arg _ (hw s)),(conj_center (A.F.room.kernel) w).trans (congr_arg _ hStar)⟩
lemma compares (hg:G.Simple){w:S.Field 4} (hw:Fixedτ A w) {k:ℕ} (hk:(A.curve.U k 4) ((fb).unit 4)= S.unit 4) (he:Spin.realH A.F.room.kernel.spin A.M.hT.spin (A.curve.U k 4)) : ∃ a:ℝ,w = a • (centering S 4 ((A.curve.U k 4) scalarF)):=by
   let U:=(A.curve.U k 4).symm;let V:= centering (fb) 4 (U w); let j: (fb).Stress:= fun i l=>if i=l then V else 0
   have hM s: (fb).mirror A.M.hT.spin 4 s (U w)=U w:=(A.curve.U k 4).injective (by rw [he.1,show A.curve.U k 4 (U w)=w from (A.curve.U k 4).apply_symm_apply _,hw.mirrors])
   have hR: (fb).conj A.M.hT.spin 4 (U w)=U w:=(A.curve.U k 4).injective (by rw [he.2,show A.curve.U k 4 (U w)=w from (A.curve.U k 4).apply_symm_apply _,hw.realVal])
   have ht:j∈ SymSpace A.M.hT.spin:= sym_mem.mpr ⟨fun i l=>(if_ctx_congr eq_comm (fun _=>rfl) (fun _=>rfl)),fun i l=>by obtain rfl|hn:=eq_or_ne i l; exact (show _ by unfold j; rw [if_pos rfl]; exact (conj_center A.M.hT _).trans (congr_arg _ hR));exact (congr_arg _ (if_neg hn)).trans ((map_zero _).trans (if_neg hn).symm), column_tensor C.labels A.M.hT.spin j (fun s i l=> ?_)⟩
   case refine_1=> obtain rfl|hn:=eq_or_ne i l
                   · unfold j; rw [if_pos rfl,if_pos rfl,eps_self]; norm_num; unfold V; rw [mirror_center A.M.hT,hM]
                   have hu := s.perm.injective.ne hn; simp only [j,if_neg hn,map_zero,if_neg hu,smul_zero]
   have hj : j∈KernelSpace A.M.hT.spin :=kernel_mem.mpr ⟨ht,fun i l=>by obtain rfl|hn:=eq_or_ne i l; exact (show _ by unfold j; rw [if_pos rfl]; exact centers_field A.M.hT.laws _); exact (congr_arg (expectation _ _) (if_neg hn)).trans (map_zero _) ⟩
   obtain ⟨a,b,c,hK⟩:=exhaust C.labels A.M.hT.spin hg (⟨j,hj⟩:KernelSpace _)
   have hv:(4:ℝ) • V= (4:ℝ) • (a+2*b) • scalarF:=by
      apply (show (4:ℝ) • V=∑ i:Axis,j i i by simp [j]; module).trans; rw [show j=_ from hK, YM.Trace.paint_sum_any, scalar_actual]; module
   refine ⟨a+2*b,?_⟩
   have hw': centering S 4 ((A.curve.U k 4) V) = w:=by
      unfold V; rw [show centering (Bel C.book) 4 (U w)= _ from value_center _,map_sub,map_smul,map_sub,map_smul,A.curve.U k 4|>.apply_symm_apply _,hk,const_out A.F.room.kernel.laws,smul_zero,sub_zero,value_center,hw.centered,zero_smul,sub_zero]
   rw [← hw',smul_right_injective ((fb).Field 4) (show (4:ℝ)≠0 by norm_num) hv]
   simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
lemma fixedΘ : Fixedτ A (centering S 4 (theta A.F 0)):=
   fixed_center (fun s=> by rw [←A.F.phase.transport.spots.signed,theta_fixed]) (theta_real ..)
lemma against_trace (hg:G.Simple){w:S.Field 4}(hw:Fixedτ A w)(H:centering S 4 (theta A.F 0)≠0):∃ a:ℝ,w=a • (centering S 4 (theta A.F 0)):=by
    obtain ⟨k, hk,ht⟩:=((A.aligned.units 4).and (A.aligned.hsym 4)).exists
    obtain ⟨a,ha⟩:=compares hg hw hk (by convert ht)
    obtain ⟨b,hb⟩:=compares hg (fixedΘ (A:=A)) hk (by convert ht)
    obtain ⟨hb',he'⟩:=smul_ne_zero_iff.mp (hb ▸ H)
    rw [hb,ha]; refine ⟨a/b,?_⟩; rw [smul_smul, div_mul_cancel₀ _ hb']
end Fixedτ
end YM.Trace
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
local notation "fb" => Bel C.book
local notation "scalarF" => scalarLabel C.labels
variable (A : PertExtension.Actual C φ S) (Y:A.F.α.space.X)
variable (W:ℕ→Wheel C 4)(k:ℕ→Filter Cutoffs)(x:ℕ→C.label 4)(R:ℝ)(hR:0<R)(h:Granular W φ A.M.hT.spin 2 R)
set_option quotPrecheck false
local notation "t" i:max => (W i).r
local notation "billLabel" i:max => S.project 4 (x i)
def targetRaw {L:Register G}{B:Table L} (m:ℕ) (b:B.Field 4):Points m→ℂ := Ward.disc fun _=>⟨4,b⟩
include h A hR
lemma cheap_compare  (hk:∀ᶠ i in atTop, (k i).NeBot ∧ k i≤φ.fuse∧Tendsto (fun j=>(W i).atCut j (show Fin (4+1) from ⟨4,Nat.lt_succ_self 4⟩) scalarF) (k i) (𝓝 (x i))) (u:Services C φ S){m:ℕ}(hm:m≤2)(T:Test m)(hT:tsupport T⊆Scaling.window R m) :
   Tendsto (fun i=> T.applyTo (fun n=> targetRaw m (S.project 4 (x i)) ((t i) • n))) atTop (𝓝 (T.applyTo (targetRaw m (B:=fb) scalarF))) := by
   rw [Metric.tendsto_nhds]; intro ε hε
   let L:=Station.charge (C:=C) (hang (fun _:Fin m=>4) (fun _=>scalarF))
   have hL : 0 ≤ L:= by unfold L Station.charge; positivity
   have hv:HasCompactSupport T := T.hasCompactSupport
   obtain ⟨c,hc⟩ := hv.exists_bound_of_continuousOn T.contDiff.continuous.continuousOn
   let M : ℝ:= |c|+1
   have hc(q:Points m): ‖T q‖ ≤ M:= by
      dsimp only [M]; by_cases q' : T q = 0; rw [q',norm_zero];positivity
      exact (hc q (subset_closure (Function.mem_support.mpr q'))).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
   let g:=ε/(2*(1+M*L)); have hg : 0<1+M*L:= add_pos_of_pos_of_nonneg one_pos (by dsimp only [M]; positivity)
   have hG : 0<g:=by dsimp only [g];positivity
   obtain ⟨Z,Q,E,V,hY⟩:= u.along
   have hC:=pay_word W h A.F.room.ordered A.F.room.kernel.smooth A.F.room.cutoff A.F.room.generic A.M.hT.smooth hR g hG (fun _:Fin m =>4) hm (fun i=> (le_rfl:4≤4)) -- hb placeholder S.Smooth
   filter_upwards [hC,hk] with i h' ⟨hK,hW,hx⟩
   specialize h' (fun _=>scalarF) T hT M (by dsimp [M];positivity) hc
   let U:=T.applyTo (targetRaw (B:=fb) m scalarF); let w: Ribbon fb (fun _: Fin m=>4):= fun _=>scalarF
   have he : Tendsto (fun j:Cutoffs=>(W i).toStation.paid (hang _ w) (h:=fun _=>le_rfl) T j.1 j.2) (k i) (𝓝 (T.applyTo (fun n=>targetRaw m (billLabel i) ((t i) • n)))) := by
      have hI:=calibrated_smear A.F.room.ordered (k i) hW (dilate (W i).rad T) (he:=fun (d:Fin m)=>hx)
      unfold Table.integralOn at hI; rw [zoom_integral] at hI
      convert hI using 2
      · rfl
      apply Test.apply_eq; intro n hn
      exact S.at_project S A.F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (Work.A05.smul_conf (W i).rad hn) (fun _:Fin m=> ⟨4,x i⟩) -- adjust
   rw [dist_eq_norm]; change _ < ε
   refine (le_of_tendsto ((he.sub tendsto_const_nhds).norm) (hW ((φ.fused _).mpr (h' (ε/4) (by positivity))))).trans_lt ?_
   change g*L*M + ε/4 < ε
   unfold g; rw [div_mul_eq_mul_div,div_mul_eq_mul_div]; apply add_lt_of_lt_sub_right (show _ < ε-ε/4 from ?_); apply (div_lt_iff₀ (mul_pos zero_lt_two hg)).mpr; nlinarith [(mul_nonneg (by dsimp [M];positivity : 0≤M) hL)]
end YM.Trace
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
local notation "fb" => Bel C.book
local notation "scalarF" => scalarLabel C.labels
variable (F:Spec.Final C φ S) (A : PertExtension.Actual C φ S)
lemma testRoom {n:ℕ}(p:Test n): ∀ᶠ r:ℝ in atTop,tsupport p⊆Scaling.window r n:=by
   let K:=tsupport p
   have hK:=p.hasCompactSupport; have hc:=p.tsupport_subset; change IsCompact K at hK
   obtain ⟨B,hB⟩:= hK.exists_bound_of_continuousOn (f:=id) continuousOn_id
   have hv (x:Points n)(i j:Fin n)(hx:x∈K)(hh:i≠j) : cubedist (x i) (x j) > 0:= dist_pos.mpr (WithLp.ofLp_injective _ |>.ne (show x i ≠ x j from (hc hx).ne hh))
   obtain hn|hne:=K.eq_empty_or_nonempty; change tsupport ⇑p=∅ at hn; rw [hn]; exact Eventually.of_forall fun r=>empty_subset _
   choose! a ha ha' using fun i j (h:i≠j)=> hK.exists_isMinOn hne ((continuous_cubedist.comp (f:=fun x:Points n=>(x i,x j)) (by fun_prop)).continuousOn)
   filter_upwards [ eventually_ge_atTop B,eventually_all.mpr fun (i:Fin n)=> eventually_all.mpr fun (j:Fin n)=>eventually_ge_atTop (if h:i≠j then (cubedist (a i j i) (a i j j))⁻¹ else 1)] with r hr hs x hx
   refine ⟨fun i j hij=> ?_,(hB x hx).trans hr⟩
   apply le_trans (b:=cubedist (a i j i) (a i j j)); exact inv_le_of_inv_le₀ (hv _ _ _ (ha i j hij) hij) (by simpa only [dif_pos hij] using! hs i j)
   exact ha' i j hij hx
include A in
lemma finds_probes (hG:G.Simple):∃ R:ℝ, 0<R ∧ ∃ T1:Test 1, ∃ T2:Test 2, tsupport T1 ⊆ Scaling.window R 1 ∧ tsupport T2 ⊆ Scaling.window R 2 ∧ T1.applyTo 1 ≠ 0 ∧ T2.applyTo (targetRaw 2 (B:=fb) scalarF)≠0:=by
   let G1 (x:Points 2):= targetRaw 2 (B:=fb) scalarF x
   have hg : ContinuousOn G1 (conf 2):= (smoothDisc A.M.hT.smooth scalarCompar).continuousOn
   obtain ⟨T1,ht⟩:=(show ∃ T1:Test 1, T1.applyTo 1≠0 by
     apply Classical.not_forall.mp
     intro h'
     have he:=Test.weak_null (K:=(fun _ : Points 1=> (1:ℂ))) continuousOn_const|>.1 h' (show (0:Points 1)∈conf 1 from valid_one _)
     exact one_ne_zero he)
   obtain ⟨T2,hT⟩:=(show ∃ T2:Test 2, T2.applyTo G1 ≠0 by
     apply Classical.not_forall.mp; intro h'
     have hh:= room_conf (x:=separated 1) (o:=0) 1 1 1 (room_separated 1 zero_le_one) one_pos one_pos
     have he:=Test.weak_null hg|>.1 h' hh; change targetRaw 2 _ _=0 at he; change Ward.disc (scalarCompar (C:=C)) _ = _ at he; rw [free_expression _ hh] at he
     exact (Complex.ofReal_ne_zero.mpr (div_ne_zero (theoryDensity_pos hG).ne' ((pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hh.ne (show _≠_ by decide)))))))) he)
   obtain ⟨R,hp,hq,hr⟩:= ((testRoom T1).and ((testRoom T2).and (eventually_gt_atTop 0))).exists
   exact ⟨R,hr,T1,T2,hp,hq,ht,hT⟩
lemma oneRaw_fixed {L:Register G}{S:Table L}(H:S.Hierarchy)(a:S.Field 4): ∀ x:Points 1,targetRaw 1 a x=expectation S 4 a:=by
   intro x
   have hx:x∈ conf 1:= valid_one _
   have hv(n:Points 1)(hn:n∈conf 1): targetRaw 1 (B:=S) a n = S.read n (fun _=>⟨4,S.representative 4 a⟩):=by
      apply Eq.trans ?_ (S.at_project S H.laws.toSymmetric (fun _=> le_rfl) hn _)
      change S.useAt S n _= S.useAt _ _ _; apply congr_arg; funext i; change (Sigma.mk 4 a)=⟨4,S.project 4 (S.representative 4 a)⟩;rw [S.rep]
   rw [hv x hx]
   rw [show x=Points.across (x 0) (0:Points 1) from PiLp.ext (by intro i; fin_cases i; simp)]
   rw [H.translations 1 (0:Points 1) (valid_one _) (x 0) _]; exact (hv 0 (valid_one _)).symm.trans (by unfold targetRaw expectation; rw [front_eval];exact congr_arg (S.useAt S 0) (by funext i;fin_cases i;rfl))
lemma cheap_center_pair (u:Services C φ S)(T1:Test 1)(T2:Test 2)(R:ℝ)(hR:0<R)(ht:tsupport T1⊆Scaling.window R 1)(hT:tsupport T2⊆Scaling.window R 2)(hp:T1.applyTo 1≠0)(W:ℕ→Wheel C 4)(k:ℕ→Filter Cutoffs)(x:ℕ→C.label 4) (H:Granular W φ A.M.hT.spin 2 R) (hk:∀ᶠ i in atTop,(k i : Filter Cutoffs).NeBot ∧ k i ≤ φ.fuse ∧ Tendsto (fun j:Cutoffs=>(W i : Wheel C 4).atCut j (show Fin (4+1) from ⟨4,Nat.lt_succ_self _⟩) scalarF) (k i) (𝓝 (x i : C.label 4))) :
      Tendsto (fun i=> T2.applyTo (fun n=> custom (S:=S) ((W i).r • n) (focus 4 (S.project 4 (x i))) (focus 4 (S.project 4 (x i))))) atTop (𝓝 (T2.applyTo (targetRaw 2 (B:=fb) scalarF))):=by
    let f(i):=S.project 4 (x i)
    have hi:=cheap_compare A W k x R hR H hk u (show 1≤2 by decide) T1 ht
    let Z := T1.applyTo (fun _=>(1:ℂ)); have hZ : Z≠0:= hp
    have hf {M:Register G}{N:Table M}(h:N.Hierarchy) (a:N.Field 4)(x:ℝ):(T1.applyTo fun n=> targetRaw 1 a (x•n))= Z*(expectation N 4 a) :=by
       unfold Z Test.applyTo; rw [← integral_mul_const]; apply MeasureTheory.integral_congr_ae (ae_of_all _ fun i=>by dsimp only; rw [oneRaw_fixed h,mul_one])
    have hW : Tendsto (fun i=> expectation S 4 (f i)) atTop (𝓝 (expectation _ 4 scalarF)):= by
       convert! ((hi.mul_const Z⁻¹).congr (fun i=>?_)) using 2; swap
       · change T1.applyTo _ * Z⁻¹ = _; rw [hf A.F.room.kernel]; field_simp; rfl
       change (expectation _ _ _) = T1.applyTo (targetRaw _ _) * _;rw [(show T1.applyTo (targetRaw 1 scalarF)= _ from by simpa only [one_smul] using! (hf A.M.hT scalarF 1))];field_simp
    have hc:=cheap_compare A W k x R hR H hk u (show 2≤2 by decide) T2 hT
    convert ((hc.sub ((hW.pow (2:ℕ)).const_mul (T2.applyTo (fun _=>1)))).congr (fun i=>?_)) using 2
    · rw [show (expectation _ 4 scalarF)=first_value 4 scalarF from ?zero,mean_scalar_free,zero_pow (by decide : 2≠0),mul_zero,sub_zero]
      case zero=> unfold first_value expectation; rw [front_eval]; apply congr_arg;funext i;fin_cases i;rfl
    rw [show expectation S 4 (f i)= first_value 4 (f i) from by change expectation S 4 (f i)=first_value 4 (f i); unfold expectation first_value; rw [front_eval]; apply congr_arg; funext j;fin_cases j;rfl,← show T2.applyTo (fun (_:Points 2)=> (first_value 4 (f i))^2) = T2.applyTo (fun _=>1) * (first_value 4 (f i))^2 from by unfold Test.applyTo; simp_rw [mul_one]; rw [integral_mul_const]] -- one_remainder? replace
    change T2.applyTo (fun x=> targetRaw _ (f i) _) - T2.applyTo _= _
    let Z (n : Points 2):=(W i).r • n; have hZ(n)(hn:n∈conf 2): Z n∈ conf 2:= Work.A05.smul_conf (W i).rad hn
    have hsub:= integral_sub (T2.smearing ((smoothDisc A.F.room.kernel.smooth (n:=2) (fun _=>⟨4,f i⟩)).continuousOn.comp (Continuous.continuousOn (by fun_prop : Continuous Z)) hZ)) (T2.smearing (K:=fun _=> first_value 4 (f i)^2) continuousOn_const)
    unfold Test.applyTo
    change (∫ x, T2 x * (disc (fun _=>⟨4,f i⟩) ∘ Z) x)-(∫ x, T2 x * (first_value 4 (f i))^2) = _
    rw [← hsub]
    apply integral_congr_ae; filter_upwards with n
    dsimp only [Z,comp_apply];by_cases hx:n∈conf 2
    · change _= T2 n * custom (Z n) _ _;rw [focus_read A.F.room.kernel (Z n) (hZ _ hx),custom_self,mul_sub]
    rw [T2.vanishes hx]; simp
end YM.Trace
