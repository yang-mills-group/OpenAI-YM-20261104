import YM.MSbar.Wave.Tilt
import YM.MSbar.Rolling.Melt
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c:Side}
open Set MvPolynomial
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> Positions (Primary c G)
variable (b:PowerSeries ℝ)(p:ℕ)(A:PowerSeries (Pot (Primary c G)))(R:PathData G)(c':Clip)
noncomputable def ink (c:Side)(c':Clip)(R:PathData G) := potter (main c c' R ∘ (tint G (Body 1 c))) 2
-- V.G.Verify signature.pick.
variable {F:ℝ → Config G c→ℝ}{S:ℝ→ℝ}(h:Trend F A R c' p)(hS:Approx S b p)(hb:µ 0 b=1)
include h
lemma inkUnder (x:X): MvPolynomial.eval x (ink c c' R)=height c c' R x:=by
    have he:=h.quiet; let K:= (tint G (Body 1 c)).toContinuousLinearMap; let f:=main c c' R
    unfold ink; rw [pots];change Tensor.diagonal (Tensor.coeff (f ∘ K) 2 0) x=_; rw [(he.line K).second]; rw [show rim (f ∘ K) x x = _ from he.carriage K x x,height,he.second]; rfl
include hS hb
lemma given : Trend (fun x=>F (x/S x)) (bley b A (ink c c' R)) R c' p:=by
    let Q:= ink c c' R; have hp:= tends b hb p hS; let Y:=bley b A Q
    refine ⟨?_,?_, hp.eventually h.base,?_, h.quiet,fun n=> ?_⟩
    · unfold Kind bley; rw [_root_.map_sub, ticket,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; simp [fare,show PowerSeries.constantCoeff A=0 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,h.bond],show PowerSeries.constantCoeff b=1 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,hb], PowerSeries.coeff_zero_eq_constantCoeff_apply] -- constantCoeff defeq
    · refine ⟨fun i hi=>?_⟩; unfold bley; rw [_root_.map_sub,PowerSeries.coeff_mk,sub_eq_add_neg]; apply (totalDegree_add ..).trans; refine max_le ((parcel A p h.plane b).profile i hi) ?_; rw [totalDegree_neg]; exact (totalDegree_smul_le ..).trans ((potsD ..).trans (by omega))
    · obtain ⟨m,a,ha,hA⟩:=h.control; refine ⟨m+1,a/4,by positivity,?_⟩
      filter_upwards [hp.eventually hA,width, hp.eventually width, boundsS b hb p hS,(eventually_lt_nhds (inv_pos.mpr (show 0 < (2:ℝ)^m by positivity))).filter_mono nhdsWithin_le_nhds] with x ht ⟨hx,he,hV⟩ ⟨hL,hG,hW⟩ hs hN U; refine (ht U).trans (div_le_div₀ (Real.exp_pos _).le (Real.exp_monotone ?_) (pow_pos hx _) ?_)
      · have hv:0 ≤ energy U:= Finset.sum_nonneg fun i _ => coast G _; rw [neg_mul, neg_div, neg_mul,neg_div,neg_le_neg_iff]; exact le_trans (le_of_eq (show _=a*energy U/(2*x)^2 from (by ring))) (div_le_div_of_nonneg_left (mul_nonneg ha.le hv) (pow_pos hL 2) (pow_le_pow_left₀ hL.le hs.2 2))
      rw [pow_succ]; have hz: (x /2)^m≤ (x/S x)^m:=pow_le_pow_left₀ (by positivity) hs.1 _; exact (mul_le_mul_of_nonneg_left hN.le (pow_nonneg hx.le m)).trans ((le_of_eq (by rw [div_pow]; ring)).trans hz)
    have hF:= pays b hb p hS n h.tune; let g:=fun (x:ℝ) (p: X)=> p; let H:=payY X n; have hV:= decks A p hb h.plane g H hS; obtain ⟨Z,hv⟩:=hS.powA 2
    have ht: Price (yard n (E:=X)) (p+1) (fun t _=> S t^2- taste p (b^2) t):=⟨Z,hv.mono fun x he _ _=> he () trivial⟩; let K:= ht.product (volley _ H Q)
    refine ((hF.nsum hV).cut K).egress ?_; filter_upwards [hS.little hb] with t ⟨hr,hk⟩ x hx; let y:= S t; have hp:0 < y:= lt_of_lt_of_le (by norm_num) hr
    have hh:postcard G c (t/y) (y • x)=postcard G c t x:=by unfold postcard; rw [smul_smul,div_mul_cancel₀ ..]; exact hp.ne'
    have he: height c c' R (y • x)= y^2 * MvPolynomial.eval x Q:=by unfold height; rw [map_smul,Tensor.homogeneous]; exact congr_arg _ (inkUnder p A R c' h x).symm -- b param?
    have hL : taste p (picture x Y) t = taste p (picture x (ticket b A)) t-(taste p (b^2) t-1)*MvPolynomial.eval x Q:=by
        nth_rw 1 [← single t p]; -- parser occurrences first maybe 
        unfold taste picture Y bley; rw [← Finset.sum_sub_distrib (f:=fun i=>t^i*_), Finset.sum_mul,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_
        rw [PowerSeries.coeff_map,PowerSeries.coeff_map,_root_.map_sub,_root_.map_sub,PowerSeries.coeff_mk,← C_mul',_root_.map_mul,eval_C, _root_.map_sub]; ring
    dsimp only [g]; rw [show taste p (picture x (bley b A (ink c c' R))) t=_ from hL, show height c c' R (S t • x)= _ from he,show postcard G c (t/S t) (S t • x) = postcard G c t x from hh,← show MvPolynomial.eval x Q=height c c' R x from inkUnder p A R c' h x]; unfold y Q; ring -- supplies
end YM.MSbar.Wave
