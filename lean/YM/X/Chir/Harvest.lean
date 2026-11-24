import YM.X.Chir.Flurry
/-!
# Cost of spin wire on arbitrary clouds. integrates Γ unweighted singular line. point ∶ terminals.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "D"=> Interval.mass
local notation "o"=> side q k
local notation "L"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
variable (p t u v : Tet)(i j:Axis)(X Y Z:Fielding.Walk)
abbrev wef (q:ℕ+)(X:Fielding.Walk)(l:ℕ)(A:Scaff): Weave q:= skyView q X l A
def fog (q:ℕ+)(X:Fielding.Walk):Weave q:= fun k i=> if i=transit q X k then (volS q k)⁻¹ else 0
abbrev readAt (q:ℕ+)(X:Fielding.Walk)(F:Weave q)(k:ℕ) := F k (transit q X k)
lemma fog_eval (F:Weave q): crow q (fog q X * F)= readAt q X F:= by
    ext1 i; simp only [crow,Pi.mul_apply,fog,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,readAt]; rw [mul_inv_cancel_left₀]; unfold volS; norm_cast; exact (pow_pos (epsilon_pos q i) 4).ne'
def hazeV (q:ℕ+)(k:ℕ):ℂ:= Complex.ofReal ((epsilon q k * (side q k).val)⁻¹^4)
def coinW (q:ℕ+):Weave q:= ensign q (hazeV q)
def bore (q:ℕ+)(k:ℕ):ℂ:=Complex.ofReal (epsilon q k)
lemma pulse_v : wef q X 2 (exchangeF (-1) p (-1) t)=ensign q (bore q) * wef q X 3 (slag p t)+(if p=t then fog q X - coinW q else 0) := by
   ext1 k; ext1 z; let e:=ε k; let x:=transit q X k; change (↑(Wpp e (-1) p (-1) t _ x z):ℂ)=_; rw [slag_plot p t e x z (epsilon_pos ..)]; simp only [Pi.add_apply,Pi.mul_apply]; rw [Complex.ofReal_add,Complex.ofReal_mul]; apply congr_arg₂ (·+·) rfl; by_cases ht:p=t
   · rw [if_pos ht,if_pos ht,Pi.sub_apply]; change _=(if z=x then (volS q k)⁻¹ else 0) - hazeV q k; unfold volS hazeV; unfold e; rw [mul_inv,mul_pow]; by_cases hx:x=z <;> first| (rw [if_pos (by assumption), if_pos hx.symm]; push_cast; simp only [inv_pow,zpow_neg,zpow_ofNat]; ring)| (rw [if_neg (by assumption),if_neg (Ne.symm hx)]; push_cast; simp only [inv_pow,zpow_neg,zpow_ofNat]; ring)
   · rw [if_neg ht,if_neg ht]; rfl
lemma kiteV (x:Fielding.Walk)(a:G.ColorIndex)(r:ℝ): wef q x 1 (transfer r p i)= wire q x (spin r p a) (columnA i a):= by
   ext1 k; ext1 z; unfold wire; rw [entryp_ce,if_pos rfl,wrap_lift];rfl; exact epsilon_pos .. -- he goal?
lemma kiteP (x:Fielding.Walk)(a:G.ColorIndex)(r r':ℝ): wef q x 2 (exchangeF r p r' t)= wire q x (spin r p a) (upMark (spin r' t a)):= by
   ext1 k; ext1 z; unfold wire; rw [entrym_ce,if_pos rfl,wrap_lift];rfl; exact epsilon_pos ..
variable (hq:1<q.val)
lemma μ_l (k:ℕ): ‖hazeV q k‖=(ε k * (side q k).val)⁻¹^4:= by rw [hazeV,Complex.norm_real]; exact Real.norm_of_nonneg (by positivity)
lemma idyllic (F G:Scaff)(k:ℕ): crow q (wef q X 1 F * wef q Y 1 G) k= ↑(Tr q X Y F G k):= by
   simp only [crow, volS, wef,skyView,LinearMap.coe_mk,AddHom.coe_mk, Pi.mul_apply]; rw [Finset.mul_sum]; unfold Tr traceL; simp_rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum,sprite_val]; have he:=epsilon_pos q k; refine Finset.sum_congr rfl fun i hi=>?_ ; push_cast; norm_num; field_simp
lemma ideal_cost (F G:Scaff){a b:ℝ}(h:Paying (transit q X k) 3 a (F o (transit q X k)))(ht:Paying (transit q Y k) 3 b (G o (transit q Y k)))(hc:a≥0)(hd:b≥0) :
    ‖crow q (wef q X 1 F*wef q Y 1 G) k‖≤ (140000*a*b)*(segment q X Y k)⁻¹^2:= by
      rw [idyllic]; let x:=transit q X k; let y:=transit q Y k; have he:=epsilon_pos q k; unfold Tr traceL; rw [Complex.norm_real, norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (ε k)⁻¹^2)]; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans ?_;
      have hp : ∑ i:Site o, ‖F o x i*G o y i‖ ≤ (a*b)*(140000*fund 2 x y):= by
            refine le_trans ?_ (mul_le_mul_of_nonneg_left (bal₀ x y Finset.univ) (mul_nonneg hc hd)); rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; unfold balance; rw [norm_mul, mul_mul_mul_comm]; exact mul_le_mul (h i) (ht i) (by positivity) (mul_nonneg hc (live _ _|>.le))
      refine le_trans (mul_le_mul_of_nonneg_left hp (by positivity : 0≤ (ε k)⁻¹^2)) (le_of_eq ?_); unfold Imprint.segment fund; rw [mul_inv,mul_pow];change (ε k)⁻¹^2*_=(140000*a*b)*(_*(D x y)⁻¹^2); ring
include hq
lemma thinning : Tendsto (hazeV q) atTop (𝓝 0):= by
   rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [μ_l]; simpa using! (show Tendsto (fun i=> (ε i* (side q i).val)⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_zero.comp (Pert.Align.large (paths hq))).pow 4
lemma bore_f : bore q∈ fades ℂ:= by
   change Tendsto (bore q) L (𝓝 0); exact (show (0:ℂ)=Complex.ofReal 0 from rfl) ▸ Complex.continuous_ofReal.continuousAt.tendsto.comp (paths hq).cutoff
lemma alcove (h: Clear q r X Y)(hr:0 ≤ r)(F G:Scaff)(hh:F∈air 1)(ht:G∈air 1): CostF (crow q (wef q X 1 F * wef q Y 1 G * coinW q)) 0:= by
   rw [coinW,crowd_time]; apply CostF.zero; let A:= crow q (wef q X 1 F * wef q Y 1 G); obtain ⟨a,ha,hh⟩:=costF hq F hh; obtain ⟨b,hb,ht⟩:=costF hq G ht; refine rent_cost hq h hr (A*hazeV q) (fun k=>140000*a*b* ‖hazeV q k‖) (by simpa using! (thinning hq).norm.const_mul (140000*a*b)) (k:=2) ?_; filter_upwards [hh,ht] with i hi ht; let t:= (segment q X Y i)⁻¹^2; rw [Pi.mul_apply,norm_mul, abs_of_nonneg (by positivity : 0 ≤ 140000*a*b* ‖hazeV q i‖),mul_right_comm (140000*a*b)]; exact mul_le_mul_of_nonneg_right (ideal_cost X Y _ _ (hi _) (ht _) ha.le hb.le) (norm_nonneg _)
-- entirely unmasked collapse (including y,z weights from real contraction). CostF statement. colored spelling $$ not needed.
variable (χ: Floor R)(a:G.ColorIndex)
include χ a
set_option maxHeartbeats 400000 in
lemma collapse_v (h: Geom q r X Y Z)(hr:R<r) (r1 r2:ℝ):
    let A:= wef q Y 1 (transfer r1 u i); let B:=wef q Z 1 (transfer r2 v j); let V:=wef q X 2 (exchangeF (-1) p (-1) t); CostF (crow q (V*(A*B))) (if p=t then readAt q X (A*B) else 0):= by
     intro A B V; unfold V; rw [pulse_v,add_mul,crowd_plus]
     let f:=slag p t; let F:= wef q X 3 f; let E:= ensign q (bore q)*F
     have he:Released (crow q (F*(A*B))):= by
          unfold A B; rw [kiteV u i Y a, kiteV v j Z a,← mul_assoc]; exact lift_view a χ hq X Y Z h hr f 3 (slag_h p t) (by norm_num) _ _ _ _
     have ht : CostF (crow q (E*(A*B))) 0:= by
          rw [show E*(A*B)=(F*(A*B))*ensign q (bore q) from by unfold E;ring,crowd_time]; exact CostF.zero (usual_fading _ _ he (bore_f hq))
     by_cases hh:p=t
     · rw [if_pos hh,if_pos hh,sub_mul,crowd_sub,fog_eval,mul_comm (coinW q)]; let W:=readAt q X (A*B); have hf:= alcove Y Z hq h.2.1 (χ.positive.trans hr).le (transfer r1 u i) (transfer r2 v j) (transfer_air i u r1) (transfer_air j v r2); have hy:CostF (W-crow q ((A*B)*coinW q)) W := by simpa using CostF.sub (a:=W) CostF.reflexive hf
       have hh:=ht.add hy; rw [zero_add] at hh; exact hh
     rw [if_neg hh,if_neg hh,zero_mul,show crow q 0=0 from funext fun i=>by simp [crow]]; rw [add_zero]; exact ht
end YM.PositionX.Chir
