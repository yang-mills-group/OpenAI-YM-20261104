import YM.MSbar.Ballet.Rails
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Work.G05
variable {n:Side}{k p m q:ℕ}{B Y K R t:ℝ}{σ:Type}[Fintype σ][DecidableEq σ]{f g:Positions σ→ℝ}
local notation "Q"=>Positions σ
variable {J:Type}[Fintype J]{L:σ→ Site n}{G:Positions σ→ℝ}
variable (Z:J→Site n)(F:J→Positions σ→ℝ)(he:G=fun i=>∑ j,F j i)
     (hv: 1 ≤ Y)(ht:0 < t)(hr:t ≤ 1)(hY:t*Y <1)(hp:p+3  ≤ m)
     (hj:0≤B)(hn:∀ i:J,∀ x:Positions σ,‖x‖<1→Allows m (F i) x B)
open Metric
noncomputable def starP (t:ℝ)(p:ℕ)(F:Positions σ→ℝ)(x:Positions σ):= -(t⁻¹^2)*((F-blockTaylor (2+p) F) (t • x))
local notation "K!"=> closedBall (0: Q) Y
include hv ht hr hY hp hn hj
lemma scores (x:Q)(hx:x∈closedBall 0 Y)(l:List σ)(hk:l.length ≤ m) (i:J): |buoy (starP t p (F i)) x l| ≤ t^(p+1)*(B*Y^(p+3)) ∧ContDiffAt ℝ m (starP t p (F i)) x:=by
    let Y' := t •x; have hW':‖Y'‖ ≤ t*Y:=by unfold Y'; rw [norm_smul, Real.norm_of_nonneg ht.le]; exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) ht.le
    let g:= F i-blockTaylor (2+p) (F i); let W:=t •(ContinuousLinearMap.id ℝ Q); let V:=-(t⁻¹^2); have h': ContDiffAt ℝ m g Y':=(hn _ _ (hW'.trans_lt hY)).1.of_le (m:=(↑m)) le_top|>.sub (blockTaylor_contDiff ..|>.contDiffAt)
    have hc:ContDiffAt ℝ m (g ∘ W) x:= (show ContDiffAt ℝ m g (W x) from h').comp x W.contDiff.contDiffAt
    let M:= (l.map Uniform.bolt); let M':=M.map W; let s:=M'.length; have hL:s=l.length:=(by simp only [s,M',M,List.length_map]); have hm:M.length ≤ m:=List.length_map (as:=l) bolt |>.trans_le hk
    have he':starP t p (F i)=fun x:Q=> V*(g ∘ W) x := rfl
    rw [he']; refine ⟨?_, contDiffAt_const.mul hc⟩
    unfold buoy;rw [Lis.wed m _ _ _ hc hm, toe W m M (show _ from h') hm, abs_mul, Aqua.rod m M' (W x) h' (hL.trans_le hk)] -- rod namespace?
    have hA:= Bout.permit (p:=2+p) (by omega : 2+p+1 ≤ m) (hn i) (x:=W x) (hW'.trans_lt hY) M'.length (hL.trans_le hk)
    let s':= 2+p+1-M'.length
    have hb:∀ j:Fin M'.length, ‖M'.get j‖ ≤ t:=by
        intro j; obtain ⟨y,hy,h⟩:=List.mem_map.mp (show M'.get j∈ M.map W from M'.get_mem j); obtain ⟨u,_,rfl⟩:=List.mem_map.mp hy; rw [←h,show W (bolt u)= t •bolt u from rfl,norm_smul,Real.norm_of_nonneg ht.le]; exact mul_le_of_le_one_right ht.le (CrossH.piano ..)
    have hC: (∏ i:Fin M'.length, ‖M'.get i‖) ≤ t^M'.length:=by simpa only [prod_const,card_univ,Fintype.card_fin] using (Finset.prod_le_prod (s:=Finset.univ) (g:=fun _ : Fin M'.length=> t) (fun i _=>norm_nonneg _) (fun i _=>hb i))
    have hK:s' ≤ p+3:=by unfold s'; omega
    unfold V;rw [abs_neg,abs_of_nonneg (sq_nonneg _),←Real.norm_eq_abs]; apply le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ M'.length g (W x)) M'.get) (sq_nonneg ..)); apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hW' s') hj)) hC (prod_nonneg fun _ _=>norm_nonneg _) (mul_nonneg hj (by unfold Y' at *; positivity))) (sq_nonneg _)); calc
       _ = (t⁻¹^2)*(t^(s'+M'.length))*(B*Y^s'):=by rw [pow_add];ring
       _ ≤ t⁻¹^2*t^(2+p+1)*(B*Y^(p+3)):=by apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hr (show 2+p+1 ≤ s'+M'.length from (by unfold s'; omega))) (sq_nonneg _)) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv hK) hj) (by positivity) (by positivity)
       _ = _:=by rw [add_assoc,pow_add]; field_simp
end YM.MSbar.Ballet
