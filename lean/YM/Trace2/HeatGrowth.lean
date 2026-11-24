import YM.Trace2.ScalarGrowth
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 240000
set_option maxRecDepth 2500
noncomputable section
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns WithLp
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
local notation "fb" => Bel C.book
local notation "Fv" => scalarLabel C.labels
variable (F : Spec.Final C φ S)

def pinH (n u:E4) := ∑ i,n i*u i
lemma pinning (w:E4): pinH w w=‖w‖^2:=by
   apply (show pinH w w=inner ℝ w w by unfold pinH; rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial];rfl).trans (real_inner_self_eq_norm_sq ..)
lemma pin_add (n u v:E4): pinH n (u+v)=pinH n u+pinH n v:= by unfold pinH; simp_rw [PiLp.add_apply,mul_add,Finset.sum_add_distrib]
def reflectHere (n u:E4):=u- (2*pinH n u/(‖n‖^2)) • n
def reflecting (n:E4):M4:=(1:M4) - (show M4 from Matrix.of (fun i j=> 2*n i*n j/(‖n‖^2)))
lemma reflecting_acted (n u:E4): M4.move (reflecting n) u=reflectHere n u:=by
   apply PiLp.ext;intro i; rw [M4.at_coord]; unfold reflecting; simp only [PiLp.sub_apply, Matrix.sub_apply,Matrix.of_apply,sub_mul, Finset.sum_sub_distrib,Matrix.one_apply, ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
   unfold reflectHere pinH; rw [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul, Finset.mul_sum,Finset.sum_div,Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun j _=>by ring
lemma reflec_swap (n:E4): Matrix.transpose (reflecting n) = reflecting n:= by ext i j; simp [reflecting,Matrix.one_apply,(eq_comm (a:=j) (b:=i)), mul_right_comm,mul_assoc,mul_comm, mul_left_comm]
lemma reflect_rev (n u:E4) (hn:n≠0): reflectHere n (reflectHere n u)= u:=by
   unfold reflectHere
   have hh(k:ℝ): pinH n (u-k • n) = pinH n u-k*‖n‖^2:=by unfold pinH; simp only [PiLp.sub_apply,PiLp.smul_apply, smul_eq_mul,mul_sub, Finset.sum_sub_distrib]; rw [←pinning, pinH, Finset.mul_sum (s:=Finset.univ)]; congr 1; exact Finset.sum_congr rfl fun j _=>by ring
   have hk := (pow_pos (norm_pos_iff.mpr hn) 2).ne'
   rw [hh,show (2 * (_-_)/‖n‖^2:ℝ) = -(2*pinH n u/‖n‖^2) from ?_,neg_smul,sub_neg_eq_add,sub_add_cancel];field_simp;ring
lemma reflecting_unit (n:E4)(hn:n≠0): reflecting n∈ Matrix.unitaryGroup Axis ℝ:=by
   let y:=reflecting n
   apply Matrix.mem_unitaryGroup_iff'.2
   change star y * y = (1:M4); rw [show star y = y.transpose from by simp [Matrix.star_eq_conjTranspose],show y.transpose=y from reflec_swap n];ext i j
   rw [← M4.move_basis (y*y) i j]; change M4.move (y*y) _ _ = _
   rw [M4.move_mul,show y=reflecting n from rfl,reflecting_acted,reflecting_acted,reflect_rev n _ hn, ← M4.move_basis 1]
   rw [M4.move_one]

def θDiagram (x : Points 2) := central F none x
lemma θ_moving (o:Ortho)(x:Points 2)(hx:x∈conf _): θDiagram F (Points.move o x) = θDiagram F x:=by
   let g:=F.sector.turns
   let q:= theta F 0
   have hm := first_value 4 q
   let T:=focus 4 q
   have hz : θDiagram F (Points.move o x) = custom (Points.move o x) T T:= raw_focus_exact ..
   rw [hz, show θDiagram F x = custom x T T from raw_focus_exact ..]
   have h:= F.phase.transport.motion 2 (fun _:Fin 2=>⟨4,T⟩) x hx o
   have hw:g.act 4 o T=T:=by change g.act 4 o (q - _)=_; rw [map_sub,map_smul,F.phase.transport.spots.identity,show g.act 4 o q=q from theta_fixed F 0 o];rfl
   rw [show g.label o ∘ (fun i:Fin 2=>⟨4,T⟩)=(fun i:Fin 2=>⟨4,T⟩) from funext fun _=> congr_arg _ hw] at h
   convert h using 1; all_goals rw [custom_self]; rfl
lemma θ_translating (v:E4)(x:Points 2)(hx:x∈conf _): θDiagram F (Points.across v x)=θDiagram F x:=by
   have h:=F.room.kernel.translations 2 x hx v
   simp_rw [θDiagram,raw_focus_exact,custom_self, Ward.disc]; let p:Fin 2→C.book.Token:= fun _=>⟨4,S.representative 4 (focus 4 (theta F 0))⟩
   have ha: S.classTokens ∘ p=fun _=>⟨4,focus 4 (theta F 0)⟩:= funext (fun j=> congr_arg (Sigma.mk (β:=S.Field) 4) (S.rep _ _))
   rw [← ha]; rw [S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (by intro i j (h:x i+v=x j+v); exact hx (add_right_cancel h)),S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) hx]; exact h p
   -- still use at_project
lemma rotation_exists (z : E4):∃ o:Ortho, Ortho.move o (‖z‖ • basis timeAxis)=z:=by
   let x:=‖z‖ • basis timeAxis; let n:=x-z
   by_cases hn:n=0
   · use 1; rw [Ortho.move_one]; exact sub_eq_zero.mp hn
   use (⟨reflecting n, reflecting_unit n hn⟩ : Ortho)
   unfold Ortho.move; rw [reflecting_acted]; change reflectHere n x = _; rw [reflectHere]
   have hx : ‖x‖=‖z‖:=by unfold x;rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),basis_norm,mul_one]
   have hsum: 2*pinH n x = ‖n‖^2:=by
      have hw(w:E4): pinH n w = pinH x w - pinH z w:=by unfold n pinH; simp only [PiLp.sub_apply,sub_mul,Finset.sum_sub_distrib]
      have hv : pinH n n = pinH n x-pinH n z:=by unfold n pinH; simp only [PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib]
      have hz : pinH z x = pinH x z := by unfold pinH; simp_rw [mul_comm]
      rw [← pinning,hv,hw,hw,pinning,pinning,hx,hz];ring
   rw [hsum,div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hn)),one_smul]; exact sub_sub_cancel x z
lemma θ_norm_rep(x:Points 2)(hx:x∈conf _): θDiagram F x=θDiagram F (separated ‖x 1-x 0‖):= by
   let z:= x 1-x 0
   obtain ⟨o,h⟩:=rotation_exists z
   let y:= separated ‖z‖;have hz: 0 < ‖z‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne (by decide : (1:Fin 2)≠0)))
   have hy:= room_conf y 0 _ 1 1 (room_separated _ hz.le) hz one_pos
   have he: x=Points.across (x 0) (Points.move o y):=by ext1 i;fin_cases i <;> simp [y,separated,← Ortho.motion_at];rw [← LinearIsometryEquiv.map_smul]; change _=(Ortho.move o _)+_;rw [h]; exact (sub_add_cancel _ _).symm
   change θDiagram F x=θDiagram F y
   conv_lhs=>rw [he,θ_translating F _ _ ((o).move_injective.comp hy)]
   exact θ_moving F o y hy
end YM.Trace
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns WithLp
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
local notation "fb" => Bel C.book
local notation "Fv" => scalarLabel C.labels
variable (F : Spec.Final C φ S) (A : PertExtension.Actual C φ S)
lemma toward_contrary : ContinuousOn (θDiagram F) (conf 2) := by convert (smoothDisc F.room.kernel.smooth (v:=fun i:Fin 2=>⟨4,focus 4 (theta F 0)⟩)).continuousOn using 1 <;> first | rfl | (funext x; rw [θDiagram,raw_focus_exact,custom_self])
lemma test_doms {m:ℕ}(f:Test m)(F:Points m→ℂ)(B:ℝ)(h:∀ u∈tsupport f,‖F u‖≤B): ‖f.applyTo F‖ ≤ (∫ u,‖f u‖)*B:=by
    unfold Test.applyTo; rw [← integral_mul_const]; apply MeasureTheory.norm_integral_le_of_norm_le ((f.continuous.norm.integrable_of_hasCompactSupport (f.hasCompactSupport.norm)).mul_const _) (ae_of_all _ fun w=>?_)
    by_cases hb: f w=0
    · simp [hb]
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h w (subset_closure (Function.mem_support.mpr hb))) (norm_nonneg _)

lemma focus_multiple (A:PertExtension.Actual C φ S)(a:ℝ)(y:S.Field 4)(x:Points 2)(h:focus 4 y=a•focus 4 (theta A.F 0)) : custom x (focus 4 y) (focus 4 y)= (a^2:ℝ) • θDiagram A.F x := by
    let u:= focus 4 (theta A.F 0)
    obtain ⟨L,hL⟩ := custom_linear (e:=4) x (a•u)
    obtain ⟨M,hM⟩ := cu_linear₂ (v:=u) (d:=4) x
    rw [h,θDiagram,raw_focus_exact]; change custom x (a•u) (a•u) = (a^2) • custom x u u
    calc _ = (L.restrictScalars ℝ) (a • u):= hL _
         _ = a • ((M.restrictScalars ℝ) (a • u)):= ((L.restrictScalars ℝ).map_smul ..).trans (congr_arg _ ((hL u).symm.trans (hM ..)))
         _ = _:=by rw [(M.restrictScalars ℝ).map_smul,smul_smul, sq, show M.restrictScalars ℝ u=M u from rfl,← hM]

lemma near_price (t : ℕ→ℝ)(ht:Tendsto t atTop (𝓝 0)) (c d:ℝ) (M h:ℕ→ℝ)(hc:0<c)(hM:∀ i,c ≤ M i ∧ M i≤d)(hh:∀ i,0<t i) {e:ℝ} (he1:0<e)(hb:Tendsto (fun i=> |h i|/(t i)^e) atTop (𝓝 0)) : Tendsto (fun i=> h i^2/(t i*M i)^(e*2)) atTop (𝓝 0) := by
    let u:=e*2
    let v i: ℝ:=|h i|/(t i)^e
    have hc':0<c^u:= Real.rpow_pos_of_pos hc u
    have hx:Tendsto (fun i=> (v i)^2/(c^u)) atTop (𝓝 0) := by simpa only [v,zero_pow (by decide : 2≠0),zero_div] using (hb.pow 2).div_const (c^u)
    apply squeeze_zero' (Eventually.of_forall fun i=> div_nonneg (sq_nonneg _) (Real.rpow_nonneg (mul_nonneg (hh i).le ((hM i).1.trans' hc.le)) _)) (Eventually.of_forall fun i=>?_ ) hx
    unfold v; rw [div_pow,sq_abs,Real.mul_rpow (hh i).le (hc.trans_le (hM i).1).le,Real.rpow_mul (hh i).le,Real.rpow_two, div_div] -- order
    exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (pow_pos (Real.rpow_pos_of_pos (hh i) e) _) hc') ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le (hM i).1 (by positivity : 0≤e*2)) (sq_nonneg _)).trans_eq (by ring)) -- need rfl denominator / / as product

lemma multiplication_test_bound {B:ℂ} {H f s q:ℕ→ℝ}{p:ℝ} (hb:Tendsto (fun i=> q i^2 / s i^p) atTop (𝓝 0)) (h:Tendsto f atTop (𝓝 ‖B‖))(hs:∀ i,0<s i)(h0:B≠0){v:ℝ}(hv:0≤v)(hq : ∀ᶠ i in atTop,f i ≤ v*q i^2*H i): Tendsto (fun i=> s i ^ p * H i) atTop atTop := by
   apply tendsto_atTop.2; intro a
   have hz:0<‖B‖/2:=half_pos (norm_pos_iff.mpr h0)
   have h2 := (hb.mul_const (v*a)); rw [zero_mul] at h2; filter_upwards [(tendsto_order.mp h).1 _ (half_lt_self (norm_pos_iff.mpr h0)), (tendsto_order.mp h2).2 _ hz, hq] with i hi hk hg -- zero_mul substitution orientation
   have hc:0<s i^p := Real.rpow_pos_of_pos (hs i) _
   by_contra! hn
   have h':=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn.le (show 0 ≤ v*q i^2 from mul_nonneg hv (sq_nonneg _))) (show 0 ≤ s i^p from hc.le)
   refine (not_lt_of_ge (hg.trans (le_trans ?_ hk.le)) hi)
   calc v*q i^2*H i= (v*(q i)^2)*(s i^p*H i)/s i^p := by field_simp
        _ ≤ _ :=h'
        _ = _:= by ring
   -- missing hk trans, rewrite

def Escape (F : Spec.Final C φ S) := ∃ s:ℕ→ℝ,Tendsto s atTop (𝓝[>]0) ∧
      ∀ ε:ℝ,0<ε→Tendsto (fun i=> (s i)^(8-ε:ℝ)*‖θDiagram F (separated (s i))‖) atTop atTop
lemma escapes (u:Services C φ S)(hg:QuotedWeak C φ)(hv:centering S 4 (theta A.F 0)≠0): Escape A.F:=by
   obtain ⟨R,hR,T1,T,h₁,h₂,h₃,hp⟩:= finds_probes A u.simpleGate
   obtain ⟨W,k,x,ht,h,hk,hx,hw⟩:=quoted_scalar_cheap A.F u A.M hg R hR
   have h' := cheap_center_pair A u T1 T R hR h₁ h₂ h₃ W k x h hk
   let K:=tsupport T; have hK:IsCompact K:= T.hasCompactSupport; have hconf(n)(hn:n∈K):= T.tsupport_subset hn
   let t:=fun n0=> (W n0).r; let Y:=θDiagram A.F
   let v(i):= focus 4 (S.project 4 (x i)); let 𝒞:=focus 4 (theta A.F 0)
   have hθ : 𝒞≠0:=by dsimp only [𝒞]; rw [focus_eq]; exact hv
   have hnK: K.Nonempty:=by
      apply nonempty_iff_ne_empty.mpr
      intro h
      have he(i : Points 2) : T i = 0:= by
         apply not_ne_iff.mp; intro h'; have : i∈K:=subset_closure (Function.mem_support.mpr h'); exact Set.notMem_empty _ (h ▸ this)
      unfold Test.applyTo at hp; exact hp ((integral_congr_ae (μ:=(volume:Measure (Points 2))) (g:=0) (ae_of_all _ fun i=>by rw [he i,zero_mul];rfl)).trans (integral_zero _ _))
   choose b hb hb' using fun i=> (hK.exists_isMaxOn hnK (((toward_contrary A.F).comp (Continuous.continuousOn (show Continuous fun n:Points 2=> t i • n by fun_prop)) (fun n hn=>Work.A05.smul_conf (W i).rad (hconf n hn))).norm)) -- comp args
   let M(n:Points 2):= ‖n 1-n 0‖
   have hz n (h:n∈K):0<M n:=norm_pos_iff.mpr (sub_ne_zero.mpr ((hconf n h).ne (by decide : (1:Fin 2)≠0)))
   have hM: Continuous M:=continuous_norm.comp ((PiLp.continuous_apply ..).sub (PiLp.continuous_apply ..))
   have he: ∀ᶠ i in atTop,∃ a:ℝ,v i=a • 𝒞:=by filter_upwards [hx] with i hi; simp_rw [v,𝒞,focus_eq];exact Fixedτ.against_trace u.simpleGate (Fixedτ.fixed_center hi.1 hi.2) hv
   obtain ⟨j,hj⟩:=eventually_atTop.mp he; choose! a ha using hj
   let r(i):= t i*M (b i); have ht'(i):0<t i:= (W i).rad
   obtain ⟨cv,hc,hc'⟩:= hK.exists_isMinOn hnK hM.continuousOn; obtain ⟨d,hd,hd'⟩:=hK.exists_isMaxOn hnK hM.continuousOn
   have hρ:Tendsto r atTop (𝓝[>] 0):= tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (Eventually.of_forall fun i=>(mul_pos (ht' i) (hz _ (hb _))).le) (Eventually.of_forall fun i=>mul_le_mul_of_nonneg_left (hd' (hb i)) (ht' i).le) (by simpa only [zero_mul] using! ht.mul_const (M d)), Eventually.of_forall (fun i=> mul_pos (ht' i) (hz _ (hb _)))⟩
   let v'(i):=T.applyTo fun n:Points 2=>custom ((W i).r • n) (v i) (v i)
   let f(i):= ‖v' i‖; let H(i):=‖(Y (separated (r i)))‖; let c:=∫ n:Points 2,‖T n‖
   have hq : ∀ᶠ i in atTop,f i ≤ c*a i^2*H i:=by
      filter_upwards [eventually_ge_atTop j] with i hx; change ‖v' i‖ ≤ _; apply (test_doms T _ (a i^2*H i) (fun n hn=> by
         unfold H;change _ ≤ a i^2 * ‖θDiagram A.F (separated (r i))‖; rw [show r i= ‖((W i).r • b i) 1-((W i).r • b i) 0‖ from by dsimp only [r]; rw [PiLp.smul_apply,PiLp.smul_apply,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (W i).rad],
            ← θ_norm_rep A.F _ (Work.A05.smul_conf (W i).rad (hconf _ (hb _))), focus_multiple A (a i) _ _ (ha i hx), norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; apply mul_le_mul_of_nonneg_left (hb' i hn) (sq_nonneg _))).trans_eq ?_
      ring
   have hqRate(e) (hε:0<e)(he:e<(8:ℝ)):Tendsto (fun i=>a i^2/r i^(8-e)) atTop (𝓝 0):=by
      have hbank(i)(hi:j ≤ i): ‖v i‖/t i^(4-e/2)=‖𝒞‖* (|a i|/t i^(4-e/2)) :=by rw [ha i hi,norm_smul];rw [Real.norm_eq_abs,mul_comm, mul_div_assoc]
      have hc1:=hw (e/2) (by positivity) (by linarith only [he])
      -- maybe simp_rw
      refine (show 8-(e:ℝ) = (4- e/2)*2 by ring) ▸ (near_price t ht (M cv) (M d) (M ∘ b) a (hz cv hc) (fun i=> ⟨hc' (hb i),hd' (hb i)⟩) ht' (by linarith only [he]) ?_) -- b shadow!
      have H := (hc1.div_const ‖𝒞‖).congr' (f₂:=fun i=> |a i| / t i^(4-e/2)) ((eventually_ge_atTop j).mono fun i hi=> ?_)
      · simpa only [zero_div] using! H
      change (‖centering S 4 (S.project 4 (x i))‖/ _)/_= _;rw [←focus_eq,hbank i hi]; field_simp
   refine ⟨r,hρ,fun ε hε=> ?_⟩
   have htL:= multiplication_test_bound (s:=r) (p:=8-min 1 ε) (hqRate _ (lt_min one_pos hε) ((min_le_left (1:ℝ) ε).trans_lt (by norm_num))) h'.norm (fun i=>mul_pos (ht' i) (hz _ (hb _))) (B:=_) hp (v:=c) (integral_nonneg (fun _=>norm_nonneg _)) hq
   apply tendsto_atTop_mono' atTop ?_ htL
   filter_upwards [hρ.eventually (eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show 0 < (1:ℝ) by norm_num)))] with i hi
   refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge (mul_pos (ht' i) (hz _ (hb _))) hi.le (by linarith [min_le_right (1:ℝ) ε])) (norm_nonneg _)
end YM.Trace
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns WithLp
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book}{φ:Extraction.Order}
variable (F : Spec.Final C φ S) (A : PertExtension.Actual C φ S) (u:Services C φ S)
local notation "uv" => 𝓝[>] (0:ℝ)
def heatEta (v:Viewers F)(s:ℝ):ℂ:=central F v (separated s)
lemma rpow_fades (p:ℝ)(h:0<p): Tendsto (fun s:ℝ=> s^p) uv (𝓝 (0:ℝ)):= by simpa [Real.zero_rpow h.ne'] using! (Real.continuousAt_rpow_const (0:ℝ) p (.inr h.le)).tendsto.mono_left (show uv≤𝓝 0 from nhdsWithin_le_nhds)
private lemma error_fades (p q b:ℝ)(h:0<p)(he:0<p+q): Tendsto (fun s:ℝ=> s^p*(b+2*s^q)) uv (𝓝 0):=by
    refine (((rpow_fades p h).mul_const b)|>.add ((rpow_fades (p+q) he).const_mul 2)).congr' ((show ∀ᶠ s:ℝ in uv,0<s from self_mem_nhdsWithin).mono (fun s hs=>?_)) |> (by simpa only [zero_mul,mul_zero,zero_add] using ·)
    rw [Real.rpow_add hs]; ring
include u
lemma seam_errors (p:ℝ)(hp:7<p)(v v':ℝ→Viewers F): Tendsto (fun s=>s^p*(‖heatEta F (v s) s‖-‖heatEta F (v' s) s‖)) uv (𝓝 0):=by
    let q:= heatEta F; let L:=cape F
    let b:ℝ:= p-7
    have hd : ∀ᶠ s in uv, ∀ i j, ‖q i s-q j s‖≤ 2*L^2+2*s^(-7-b/2):= by
       filter_upwards [centered_phased F u (M:=1) (η:=1) zero_le_one (show 0<(b/2:ℝ) by dsimp [b];linarith) one_pos,self_mem_nhdsWithin] with s h hs i j; exact h _ 0 (room_separated _ (show (0:ℝ)<s from hs).le) i j
    have hT := error_fades p (-7-b/2) (2*L^2) (by linarith) (by unfold b; linarith)
    apply squeeze_zero_norm' ?_ hT
    filter_upwards [hd,self_mem_nhdsWithin] with s hs hi; change 0<s at hi; rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hi _)]; exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _ |>.trans (hs (v s) (v' s))) (Real.rpow_pos_of_pos hi _).le
lemma escape_phases (hg:Escape F): ∃ s:ℕ→ℝ,Tendsto s atTop uv ∧ ∀ ε:ℝ, 0<ε→∀ v:ℕ→Viewers F,Tendsto (fun i=>s i^(8-ε:ℝ)*‖heatEta F (v i) (s i)‖) atTop atTop:=by
    obtain ⟨s,hs,hg⟩:=hg; refine ⟨s,hs,fun ε h v=>?_⟩;let e:=min ε (1/2)
    have he:e>0:=lt_min h (by norm_num)
    have hl : Tendsto (fun i=>s i^(8-e:ℝ)*(‖heatEta F (v i) (s i)‖-‖heatEta F none (s i)‖)) atTop (𝓝 0):=by
        rw [Metric.tendsto_nhds]; intro δ hδ; have hw(j:ℕ):=seam_errors F u (8-e) (by change 7<8-min ε _; linarith [min_le_right ε (1/2)]) (fun _=> v j) (fun _=>none)
        -- uniformize
        filter_upwards [hs.eventually (OPE.universalize (p:=fun t v=> dist (t^(8-e)*(‖heatEta F v t‖-‖heatEta F none t‖)) 0 < δ) (fun f=>Metric.tendsto_nhds.mp (seam_errors F u (8-e) (by change 7<8-min ε _; linarith [min_le_right ε (1/2)]) f (fun _=>none)) _ hδ))] with i hi using hi _
    apply tendsto_atTop_mono' atTop _ (f₁:=fun i => (s i)^(8-e:ℝ) * ‖heatEta F none (s i)‖ + s i^(8-e:ℝ)*(‖heatEta F (v i) (s i)‖-‖heatEta F none (s i)‖)) ((hg e he).atTop_add hl)
    filter_upwards [hs.eventually (show ∀ᶠ (s:ℝ) in uv,0<s from self_mem_nhdsWithin),(tendsto_nhds_of_tendsto_nhdsWithin hs).eventually (ge_mem_nhds zero_lt_one)] with i hi hx
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hi hx (show 8-ε ≤ 8-e by unfold e; linarith [min_le_left ε (1/2:ℝ)])) (norm_nonneg (heatEta F (v i) (s i)))).trans_eq' (by ring)

open OPE.Prescription in
lemma raw_upper (p:ℝ)(hp:8<p): Tendsto (fun s=>s^p*‖heatEta F none s‖) uv (𝓝 0):=by
    obtain ⟨P,hP⟩:=OPE.Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
    have hQ:= OPE.one_radius F hP u
    let x(s:ℝ) := (separated s).ofLp; let b:Fin 2→C.book.Token:=fun _=>⟨4,S.representative 4 (theta F 0)⟩
    let z: Empty→ C.book.Token:=Empty.elim; let Y:Empty→E4:=Empty.elim
    let K (s:ℝ):=P.truncated S 0 (x s) b 0 Y z
    let e:=(p-8)/2
    have he:0<e:=half_pos (sub_pos.mpr hp)
    have hu:sigma b = 8:=by unfold b OPE.sigma; norm_num [Fin.sum_univ_two]
    have hW:= rpow_fades (p-8-e) (by dsimp [e];linarith)
    have hz(o:Mode F.sector.derivatives)(ho:o∈bands F.sector.derivatives 0): Tendsto (fun s=>s^p*‖P.termRead S (x s) b 0 o Y z‖) uv (𝓝 0):=by
       let V:= ‖observe S (beside (sole 0) Y) (beside (sole (P.letter o)) z)‖
       apply (squeeze_zero' (show ∀ᶠ s in uv,0 ≤ s^p*‖P.termRead S (x s) b 0 o Y z‖ from (show ∀ᶠ s in uv,0<s from self_mem_nhdsWithin).mono (fun s hs=> mul_nonneg (Real.rpow_pos_of_pos hs _).le (norm_nonneg _))) ?_ ((by simpa only [zero_mul] using! hW.mul_const V)))
       filter_upwards [hQ.terms _ b 1 1 e one_pos zero_le_one he o,self_mem_nhdsWithin] with s hs hw
       change 0<s at hw; have hA:=hs _ 0 (room_separated _ hw.le); unfold Prescription.termRead; simp only [norm_mul, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg (E:=ℂ) _)
       apply (mul_le_mul_of_nonneg_left (show ‖P.ope o (x s) b 0‖ ≤ s^(-(8:ℝ)-e) from by simpa only [hu, Nat.eq_zero_of_le_zero ((full_bands ..).1 ho),Nat.cast_ofNat,Nat.cast_zero,zero_sub] using hA.2) (Real.rpow_pos_of_pos hw _).le).trans_eq (by rw [←Real.rpow_add hw];ring_nf)
    have hK : Tendsto (fun s=> s^p*‖K s‖) uv (𝓝 0):=by
       refine squeeze_zero' ((show ∀ᶠ s in uv,0<s from self_mem_nhdsWithin).mono fun s hs=> mul_nonneg (Real.rpow_pos_of_pos hs _).le (norm_nonneg (K s))) ?_ (g:=fun s=> ∑ i∈bands F.sector.derivatives 0,s^p*‖P.termRead S (x s) b 0 i Y z‖) (by simpa using tendsto_finsetSum _ hz)
       filter_upwards [self_mem_nhdsWithin] with t hw; rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.rpow_pos_of_pos (show 0<t from hw) _).le
    have hp' := error_fades 0 0 0
    have he' := rpow_fades (p+1-8-e) (by dsimp [e]; linarith)
    apply (squeeze_zero' ((show ∀ᶠ s in uv,0<s from self_mem_nhdsWithin).mono (fun s hs=> mul_nonneg (Real.rpow_pos_of_pos hs _).le (norm_nonneg _))) ?_ ((by simpa only [zero_mul,zero_add] using! ((rpow_fades p (zero_lt_one.trans_le (by linarith : 1≤p))).mul_const ((cape F)^2)).add (he'.add hK))) : Tendsto _ _ _)
    filter_upwards [hQ.horizons _ _ b z 1 1 1 e one_pos zero_le_one one_pos he 0,self_mem_nhdsWithin] with s hS hs; change 0<s at hs
    specialize hS (x s) (0:E4) Y (room_separated _ hs.le) ⟨fun i=>Empty.elim i,fun i=>Empty.elim i⟩
    have hc:= hS.2.2.phaseBound none
    have hconf:=room_conf (separated s) 0 _ 1 1 (room_separated _ hs.le) hs one_pos
    rw [observe_beside_empty (spectate F none).laws.toSymmetric (x s) hconf] at hc
    change ‖uncenter F none _ - K s‖ ≤ _ at hc
    have hy:=personality F none hconf
    calc s^p * ‖heatEta F none s‖ ≤ s^p*(‖central F none (separated s) - uncenter F none (separated s)‖ + ‖uncenter F none (separated s)-K s‖+‖K s‖):= mul_le_mul_of_nonneg_left (by
           change ‖central F none (separated s)‖ ≤ _; have hb:= norm_sub_le_norm_sub_add_norm_sub (central F none (separated s)) (uncenter F none (separated s)) (K s); linarith only [abs_norm_sub_norm_le (central F none (separated s)) (K s) ,  norm_sub_le_norm_sub_add_norm_sub (central F none (separated s)) (uncenter F none (separated s)) (K s) ,  (le_abs_self (‖central F none (separated s)‖-‖K s‖)) ]) (Real.rpow_pos_of_pos hs _).le
         _ ≤ _:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hy hc) le_rfl) (Real.rpow_pos_of_pos hs _).le
         _ = _:= by rw [hu]; rw [mul_add,mul_add,← Real.rpow_add hs (y:=p)];push_cast;ring_nf
lemma uniform_upper (p:ℝ)(hp:8<p) (v:ℝ→Viewers F): Tendsto (fun s=>s^p*‖central F (v s) (separated s)‖) uv (𝓝 0):= by
    have he: 7<p:=by linarith
    have h:=(raw_upper F u p hp).add (seam_errors F u p he v (fun _=>none)); rw [zero_add] at h; exact h.congr (by intro i;change _=i^p*‖heatEta F (v i) i‖;ring)
end YM.Trace
