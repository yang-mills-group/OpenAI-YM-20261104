import YM.OPE.Coverage.Store

/-!
## Relative sub-log bounds and same-depth replay in *two* measured frames

In a comparison from a finer stored receipt to a coarser weak shelf, probe
at the COARSE radius. Short signed budgets not substituted for one another.
This local transfer is one-sided in the radius hypothesis, hence never a
cost accumulated as a bounded constant over all scales. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Maxwell Next.Extract Spec
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Order}{C:Family G}{S:Table C.book}{d D D' n n':ℕ}{μ R:ℝ}{r r':ℕ→ℝ} (H:Final C F S)
set_option quotPrecheck false
local notation "mCb" => Bel C.book
local notation "V" => (mCb).Field
variable (p:Shelf H r D n R)(p':Stored H r' D' n' μ)
variable (hd:d ≤ D)(hd':d≤D')(hn:2≤n)(hn':2 ≤ n')
variable (hs:∀ t∈silver C d,tsupport t ≤Scaling.window R 2)(hR: 0 < R)(hμ:0<μ)
local notation "𝗰" => p.path
local notation "𝗳" => p'.path
-- `p'` is finer than the clearance of `p` used for testing.
variable (hq:∀ᶠ k:ℕ in atTop, (p'.path k:ℝ) / (2*(μ:ℝ)) < (p.path k:ℝ) / (R:ℝ))
include hs hR hμ hd' hn' hq
private lemma shift_into {t:Test 2}(ht:t∈ silver C d)(z:ℕ→Points 2) (hz:∀i,z i∈tsupport t):
    ∀ᶠ i in atTop, 𝗰 i • z i ∈ airy 2 ((p'.wheel i).r/(2*μ)):=by
    filter_upwards [hq] with i hi a b hb
    rw [p'.spot i]; apply lt_of_lt_of_le hi
    change p.path i / R ≤ cubedist ((p.path i • z i) a) ((p.path i • z i) b)
    have hu := hs t ht (hz i) |>.1 a b hb
    simp only [cubedist, PiLp.smul_apply, WithLp.ofLp_smul] at *
    rw [dist_eq_norm,← smul_sub, norm_smul, Real.norm_eq_abs,abs_of_pos (p.window.1 _), div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left (by rwa [← dist_eq_norm]) (p.window.1 _ |>.le)

-- event uniformization at the test profile. No common finite-cutoff index
-- across radii is needed.
local notation "𝗳𝘁" => fare p'.path
private lemma replay_visit (x y:V d) {t:Test 2}(ht:t∈silver C d) (s:ℝ)(hs':0<s): ∀ᶠ i in atTop,∀ z∈tsupport t, ‖pointwise S d (p.path i) ((p'.maps i) d x) ((p'.maps i) d y) z‖ ≤ Real.exp (s*𝗳𝘁 i):=by
   rcases (tsupport t).eq_empty_or_nonempty with ht₀|ht₀
   · simp only [ht₀,notMem_empty]; exact Eventually.of_forall fun i z h=> h.elim
   haveI : Nonempty (tsupport t):= ht₀.to_subtype
   have he(i:ℕ)(z:Points 2): disc (panels (p'.maps i) ∘ hang (fun _:Fin 2=>d) ![x,y]) (𝗰 i • z) = pointwise S d (p.path i) ((p'.maps i) d x) ((p'.maps i) d y) z:=by
      unfold pointwise; apply congrArg (fun x:Fin 2→ S.Tag=>disc x _); funext j; fin_cases j<;>rfl
   have hz(z:ℕ→ tsupport t) := airy_list H p' (fun _:Fin 2=> d) ![x,y] (fun _=>hd') hn' hμ (fun i=> 𝗰 i • (z i).val) (shift_into H p p' hd' hn' hs hR hμ hq ht (fun i=>(z i).val) (fun i=>z i|>.prop)) s hs'
   filter_upwards [OPE.universalize (p:=fun i (u:tsupport t) => ‖disc (panels (p'.maps i) ∘ hang (fun _:Fin 2=>d) ![x,y]) (𝗰 i • u.val)‖ ≤ Real.exp (s*𝗳𝘁 i)) hz] with i hi z ez
   rw [← he]; exact hi (⟨z,ez⟩)


private lemma visit_integrated (x y:V d) (t:Test 2)(ht:t∈silver C d):RateLE atTop (fare p'.path) (fun i=> scene S d (p.path i) t ((p'.maps i) d x) ((p'.maps i) d y)) 0 :=by
   have hf (i:ℕ) : Integrable (fun z:Points 2=>t z*pointwise S d (p.path i) ((p'.maps i) d x) ((p'.maps i) d y) z):=t.smearing ((smoothZoom H.room.kernel.smooth _ (p.fades.1 i)).continuousOn)
   let mass:= ∫ z:Points 2, ‖t z‖
   intro s hs₀; obtain ⟨b,hb,hb'⟩:= exists_between hs₀
   filter_upwards [RateLE.const mass (fare_large p'.path p'.fades) (s-b) (by linarith), replay_visit H p p' hd' hn' hs hR hμ hq x y ht b hb] with i h ht
   let f:= pointwise S d (p.path i) ((p'.maps i) d x) ((p'.maps i) d y)
   calc ‖∫ z:Points 2,t z*f z‖
        _ ≤ ∫ z:Points 2, ‖t z*f z‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z:Points 2, ‖t z‖*Real.exp (b*𝗳𝘁 i) := by
             apply integral_mono (hf i|>.norm) ((t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).norm.mul_const _) (fun z=>?_)
             rw [norm_mul]
             by_cases e:z∈tsupport t
             exacts [mul_le_mul_of_nonneg_left (ht _ e) (norm_nonneg _), by rw [image_eq_zero_of_notMem_tsupport e]; simp]
        _ = mass*Real.exp (b*𝗳𝘁 i):=by rw [integral_mul_const]
        _ ≤ _:=by
            refine (mul_le_mul_of_nonneg_right (by linarith only [h,Real.le_norm_self mass] : mass ≤ Real.exp ((s-b)*𝗳𝘁 i)) (Real.exp_pos _).le).trans ?_
            rw [← Real.exp_add, sub_mul]; simp
include hd hn
private lemma travel_basis (s:ℝ)(hs':0 < s)(x:V d): ∀ᶠ i in atTop,∀ y:V d,p'.maps i d x = p.maps i d y → ‖y‖ ≤ Real.exp (s*fare p'.path i):=by
   let P(t:Test 2)(i:ℕ) := scene S d (𝗰 i) t ((p'.maps i) d x) ((p'.maps i) d (Levy.reflect d x))
   have h(t:Test 2)(ht:t∈silver C d):= visit_integrated H p p' hd' hn' hs hR hμ hq x (Levy.reflect d x) t ht
   obtain ⟨B,hB,hV⟩:= determinant H p hn hd hs
   have h' := RateLE.mul (RateLE.const B (fare_large p'.path p'.fades)) (RateLE.sum (S:=silver C d) (fare_large p'.path p'.fades) (f:=fun t i=>‖P t i‖) fun q hq=>(h q hq).norm)
   have eq' := h' (2*s) (by simp only [zero_add]; linarith only [hs'])
   filter_upwards [hV,eq'] with i hi he y hv
   have hz: p.maps i d (Levy.reflect d y)=p'.maps i d (Levy.reflect d x):=by
      have w: p.maps i d (Levy.reflect d y)=Levy.bar H d (p.maps i d y):= ((p.realism i d hd).reflects _ _) |>.trans (congr_arg _ ((p.realism i d hd).bars _))
      rw [w,←hv]; exact Eq.symm (((p'.realism i d hd').reflects _ _) |>.trans (congr_arg _ ((p'.realism i d hd').bars _)))
   have hP(t:Test 2):payPair H p t i y (Levy.reflect _ y) = P t i :=by change scene S d (𝗰 i) t (p.maps i d y) _=_; rw [←hv,hz]
   replace hi : ‖y‖^2 ≤ B * (∑ t∈silver C d, ‖P t i‖) := by simpa only [replay,hP] using hi y
   change ‖B*(∑ t∈silver C d, ‖P t i‖)‖ ≤ _ at he
   rw [Real.norm_eq_abs,abs_of_nonneg (by
     have ht : 0 ≤ ∑ t∈silver C d, ‖P t i‖:=by positivity
     exact mul_nonneg (zero_le_one.trans hB) ht), mul_assoc, two_mul, Real.exp_add] at he
   nlinarith only [hi,he,Real.exp_pos (s*𝗳𝘁 i)]
/-- One-sided inverse-change bound (all labels at once). -/
lemma travel (earlier:Scaling S)(s:ℝ)(hs':0<s) : ∀ᶠ i in atTop,∀ v w:(Bel C.book).Field d,p'.maps i d v=p.maps i d w → ‖w‖ ≤ Real.exp (s*fare p'.path i) * ‖v‖:=by
   obtain ⟨α,hα,h'α⟩:= exists_between hs'
   let B:= Module.finBasis ℂ ((mCb).Field d)
   let A:= ∑ i, ‖(B.coord i).toContinuousLinearMap‖
   filter_upwards [shelf_bijective H p hn hd hs ⟨earlier.U 0 d⟩, eventually_all.mpr (fun j=> travel_basis H p p' hd hd' hn hn' hs hR hμ hq α hα (B j)), ((RateLE.const A (l:=atTop) (fare_large _ p'.fades)) ((s:ℝ)-α) (by linarith))] with i hb hi h_A x v hv
   let z:=p'.maps i d; choose u h using fun j=> hb.2 (z (B j))
   have he : p.maps i d (∑ j,B.repr x j • u j)=z x:=by rw [map_sum]; simp_rw [map_smul,h,← map_smul, ← map_sum,Module.Basis.sum_repr]
   rw [(show v=(∑ j,B.repr x j • u j) from (hb.1 (he.trans hv)).symm)] -- need v replacement
   calc _ ≤ ∑ j, ‖(B.coord j).toContinuousLinearMap‖ * ‖x‖ * Real.exp (α*𝗳𝘁 i) := (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=>by rw [norm_smul]; exact mul_le_mul ((B.coord j).toContinuousLinearMap.le_opNorm x) (hi j (u j) (h j).symm) (norm_nonneg _) (mul_nonneg (norm_nonneg ((B.coord j).toContinuousLinearMap)) (norm_nonneg x)))
        _ = A*Real.exp (α*𝗳𝘁 i) * ‖x‖:= by rw [← Finset.sum_mul,← Finset.sum_mul, mul_right_comm]
        _ ≤ _ :=by
          have h': (A:ℝ) ≤ _:= (Real.le_norm_self _).trans h_A
          refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add, sub_mul]; congr 1; abel)) (norm_nonneg _)
end YM.OPE.Coverage