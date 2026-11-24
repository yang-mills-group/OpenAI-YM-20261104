import YM.MSbar.Bout.Barge
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Set
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Parma Portal
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(v:S.Choices)(x:Positions (Primary c G))(w:Positions (Key F G))(l:List (Primary c G))(i:Primary c G)(p:ℕ)
variable {t B K r:ℝ}
local notation "Y"=>Positions (Primary c G)
local notation "E"=>Positions (Joint F G)
local notation "X"=>meetVar x w
local notation "L"=>l++[i]
local notation "J"=> Lis.rope i
local notation "C"=> pushChart F G v
local notation "A₀"=> arch F v (Lis.rope i)
local notation "A"=>singularity (pushChart F G v) 2
local notation "H"=>singularity (pushChart F G v) 2
local notation "T"=>rungP (hands F G)
noncomputable def Jets (F:Forest S.ratio)(v:S.Choices)(l:List (Primary c G)): SpringK (Joint F G) := rungP (hands F G) l (-singularity (pushChart F G v) 2)
lemma lensK (p':SpringK (Joint F G))(y:E) : eval y (PowerSeries.coeff p (rungP (hands F G) l p'))=roc (fun z=> eval z (PowerSeries.coeff p p')) (l.map (hands F G)) y:=by -- b remove
    induction l generalizing p' y with|nil=>rfl | cons i l ih=> rw [rungP,List.map_cons,roc,flux,ride, ← dimY]; congr 1; exact congr_arg (fun f=>fderiv ℝ f y) (funext fun y=> ih _ y) -- overcongr
variable (h:S.patch.Branches S.kernel G)
include h
lemma forth {β:ℝ} (hβ:β=t⁻¹^2)(ht:t≠0) : taste p (picture (meetVar x w) (Jets F v l)) t= -β*roc (blockTaylor (2+p) (pushChart F G v)) (l.map fun i=> t • hands F G i) (t • X):=by
    let m:E→ℝ:=fun v=>taste p (picture v (-A)) t; let B:=blockTaylor (2+p) (pushChart F G v); have hp(z:E):m z= -β* B (t • z):=by
         have hz:= drives (pushChart F G v) (2+p) t z; have hx: Premier C:= (bornCosts v h).line (relayB F G)
         rw [Rolling.lens 2 p C (fun i hi z=> hx.zeroP i z hi) t z] at hz; unfold m B;rw [←hz,hβ]; unfold taste picture; rw [_root_.map_neg]; simp_rw [LinearMap.map_neg,mul_neg, Finset.sum_neg_distrib]; field_simp
    let T':= (l.map (hands F G)); have he: taste p (picture X (Jets F v l)) t= roc m T' X :=by
         unfold Jets m taste picture; simp_rw [PowerSeries.coeff_map,← Fin.sum_univ_eq_sum_range]; rw [Lis.tot T'.length _ Finset.univ (fun i:Fin (p+1)=>fun x:E=> t^i.val * eval x (PowerSeries.coeff i.val (-A))) (fun i _=> (contDiffAt_const.mul ((vent ..).contDiffAt.of_le le_top))) le_rfl]; apply Finset.sum_congr rfl; intro i _; rw [Lis.wed T'.length T' (t^i.val) (fun v=>eval v (PowerSeries.coeff i.val (-A))) ((vent ..).contDiffAt.of_le le_top) le_rfl]; congr 1; exact lensK F l i _ X
    rw [he,show m = (fun z:E=> -β* B (t • z)) from funext hp]; let W:=t •(ContinuousLinearMap.id ℝ E); have hC:ContDiff ℝ ω B:=blockTaylor_contDiff ..; change roc (fun i:E=> -β*(B ∘ W) i) _ _ = _; rw [Lis.wed T'.length _ (-β) (B ∘ W) ((hC.comp W.contDiff).contDiffAt.of_le le_top) le_rfl,Lis.toe W T'.length _ (hC.contDiffAt.of_le le_top) le_rfl,List.map_map];rfl
variable (ht: 0<t)(hx:‖t • meetVar x w‖ < r) {n:ℕ}(ha: p+2+1 ≤ n)(hL:l.length < n)(hK:∀ i:Bond c,∀ x:Positions (Joint F G),‖x‖<r → Allows n (arch F v i) x B)
include ht hK hx ha hL
lemma ebb {ρ:ℝ}(hB:1≤ρ)(hz:‖meetVar x w‖≤ ρ)(hg:t≤1): let β:= t⁻¹^2; |buoy (tribe S β t (parmaM F w t) v) x (l++[i])-taste p (picture (meetVar x w) (Jets F v (l++[i]))) t| ≤ t^(p+1)*(B*ρ^(p+3)):=by
    intro β; let I:E→ℝ:= A₀; let k:= (l++[i]).length; let i':= v; let y:=t •X; let M:=(l++[i]).map fun i=>t• hands F G i; let g:= parmaM F w t; have hm:M.length=k:=List.length_map ..; have hu: M.length ≤ n:=by rw [hm]; unfold k; simp only [List.length_append,List.length_cons,List.length_nil]; omega
    have hc(i:Bond c) : ContDiffAt ℝ ω (Parma.arch F v i) (0:E):=(hK i _ ((show ‖(0:E)‖=0 from norm_zero).trans_lt ((norm_nonneg _).trans_lt hx))).1
    have hV:roc (A₀) M y= S.kernel.penalty * buoy (rowS G 1 t (rope i) (wing S (parmaM F w t) v (rope i))) x (l++[i]):=by
        unfold M y; rw [← ground F x w (l++[i]) t A₀ ((hK (rope i) _ hx).1.of_le le_top),funds]; unfold buoy; rw [Lis.wed k _ _ (rowS G 1 t (rope i) (wing S (parmaM F w t) v (rope i))) ?_ (by simp [k])]; -- smooth.
        exact (((stage_Row t 1 (rope i)).comp (f:=fun x:Y=>(x,(wing S (parmaM F w t) v (rope i)))) (contDiff_id.prodMk contDiff_const)).of_le le_top).contDiffAt
    let O:=2+p; let F' : E→ℝ := blockTaylor O A₀; let H₀ := ‖iteratedFDeriv ℝ M.length (I-F') y‖; have hs:ContDiffAt ℝ n I y:= (hK J y hx).1.of_le le_top; have hh:ContDiffAt ℝ n F' y:= ((blockTaylor_contDiff ..).contDiffAt)
    have ht' : buoy (tribe S β t g v) x (l++[i])= -β*roc I M y:=by rw [dock,hV,mul_assoc]
    rw [ht',forth F v x w (l++[i]) p h rfl ht.ne',chosen F v x w l i _ hc, ← mul_sub, abs_mul]; let Δ : E→ℝ:= I-F'; have hZ : 0 ≤ β:=sq_nonneg _; have hW:roc Δ M y= roc I M y-roc F' M y:=by rw [rod n M _ (show ContDiffAt ℝ n Δ y from hs.sub hh) hu,rod n M _ hs hu,rod n M _ hh hu]; unfold Δ; rw [iteratedFDeriv_sub_apply (hs.of_le (Nat.cast_le.mpr hu)) (hh.of_le (Nat.cast_le.mpr hu))]; rfl
    rw [show _ - roc _ _ _= roc Δ M y from hW.symm,rod n M y (show ContDiffAt ℝ n Δ y from hs.sub hh) hu,abs_neg,abs_of_nonneg hZ]; let S':= O+1-M.length; have hv : 0 ≤ B :=(hK (rope i) y hx).nonneg
    have hy: H₀ ≤ B *‖y‖^S':= permit (show 2+p+1 ≤ n by omega) (hK J) hx _ hu
    have hY : ‖y‖ ≤ t*ρ:=by unfold y; rw [norm_smul,Real.norm_of_nonneg ht.le];exact mul_le_mul_of_nonneg_left hz ht.le
    have hP : ∀ j:Fin M.length, ‖M.get j‖ ≤ t:=by
        intro j; obtain ⟨u,hu,he⟩:=List.mem_map.mp (show M.get j ∈ M from M.get_mem j); rw [← he, norm_smul, Real.norm_of_nonneg ht.le, hands, norm_meet, norm_zero]; exact mul_le_of_le_one_right ht.le (max_le (CrossH.piano _) zero_le_one)
    apply (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ M.length (I-F') y) M.get) hZ).trans; have hh :(∏ i:Fin M.length, ‖M.get i‖) ≤ t^M.length:=by simpa only [prod_const,card_univ,Fintype.card_fin] using (Finset.prod_le_prod (s:=Finset.univ) (g:=fun _ : Fin M.length=>t) (fun i _=> norm_nonneg _) (fun i _=> hP i))
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hy.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hY _) hv)) hh (prod_nonneg fun i _=> norm_nonneg _) (mul_nonneg hv (by positivity))) hZ); -- normalize
    have ht' :2+p+1 ≤ S'+M.length:=by unfold S' O; omega
    have hA : S'≤ p+3:=by unfold S' O; omega
    calc
       _ = (t⁻¹^2)*(t^(S'+M.length))*(B*ρ^S'):=by unfold β; rw [pow_add];ring
       _ ≤ t⁻¹^2*t^(2+p+1)*(B*ρ^(p+3)):=by apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hg ht') (sq_nonneg _)) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hA) hv) (by positivity) (by positivity)
       _ = _:=by rw [add_assoc,pow_add]; field_simp
end YM.MSbar.Bout
