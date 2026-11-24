import YM.MSbar.Aqua.Path
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Primary n G
local notation "X"=>Positions (Primary n G)
variable {k p m s:ℕ}{D a b r w C C' B:ℝ}{A:Rep G n}{F:ℝ→ Config G n→ℝ}{f:Nesting G n}
variable (hF:Trend F f A.path A.clip p)(ha:Touch A.eval)
local notation "R"=>film A f r p
local notation "V₀"=>vine A r
local notation "W"=> fun i=> atlas f p i A.path A.clip
variable (hp:ContDiffAt ℝ k (vine A r) 0) (hk:4 ≤ k)(h:G.Simple)
local notation "q"=> PowerSeries.coeff
include hF ha hp hk h
lemma ground (g:G.El) : V₀∘ hue (n:=n) g=ᶠ[𝓝 0] V₀:=Eventually.of_forall (fun x=>by
      unfold vine walnut palace; dsimp only [Function.comp_apply]; let G':= Wave.panel G n; let t(r:ℝ):=r • x; rw [←map_smul (hue g) r x]; have hp(z) : G' (hue g z)=AnalyticBridge.VerifiedReset.colorMove g (G' z):=(panel G n).apply_symm_apply _
      rw [show panel G n _= _ from hp _,AnalyticBridge.VerifiedReset.exp_move,ha.shield]; -- fix variable
      )
lemma litG (g:G.El) : R ∘ hue (n:=n) g=ᶠ[𝓝 0] R:=by
    filter_upwards [ground hF ha hp hk h g] with x he; change vine A r _-_=vine A r _-_; refine congr_arg₂ (·-·) he (Finset.sum_congr rfl (fun i hi=>congr_arg (r^i*·) (inh _ _ _ _ hF i (Nat.lt_succ_iff.mp (mem_range.mp hi)) g x)))
local notation "j!"=>0+0 -- remove
lemma zen : fderiv ℝ R 0=0:= zero_hit ((hp.sub (Aqua.pure A f r p|>.contDiffAt.of_le le_top)).of_le (by exact_mod_cast (show 2 ≤ k from by omega))) h (litG hF ha hp hk h)
variable (hr:0<r)
include hr
open AnalyticBridge.VerifiedReset
lemma booking : Ribbon (rim R):=by
    let g(k:X) := R k; have hh(k:G.El):g ∘ hue k=ᶠ[𝓝 0] g:= litG hF ha hp hk h k
    have hg(s:Signed)(b:Site n):g ∘ bandE s b=ᶠ[𝓝 0] g:= Eventually.of_forall fun x=>by
         change vine _ r (bandE _ _ _)- _=_-_; refine congr_arg₂ (·-·) ?_ (Finset.sum_congr rfl (fun i hi=>congr_arg (r^i*·) (ins _ _ _ _ hF i (Nat.lt_succ_iff.mp (mem_range.mp hi)) s b x)))
         unfold vine walnut palace; rw [←map_smul (bandE s b)]; let G':=panel G n; have hp(z) : G' (bandE s b z)=pullDir s b (G' z):= G'.apply_symm_apply _
         rw [show panel _ _ _= _ from hp _,pull_increment,ha.even_]
    have hs : ContDiffAt ℝ k g 0:= hp.sub ((Aqua.pure ..).contDiffAt.of_le le_top); have hf: ContDiffAt ℝ 2 g 0:=hs.of_le (by exact_mod_cast (show 2 ≤ k from by omega)); have hz :=zen hF ha hp hk h
    refine ⟨fun k=> classR (hh k) hf hz, fun k b=>classR (hg k b) hf hz,fun t x=>?_⟩
    -- lower via direct R vine ward and all jets
    let X':= vine A r; let V:= ore A f r p; have hV:ContDiffAt ℝ 2 V 0:= (Aqua.pure ..).contDiffAt.of_le le_top; have hX:ContDiffAt ℝ 2 X' 0:= hp.of_le (by exact_mod_cast (show 2≤k from by omega)); have he:fderiv ℝ X' 0=0:=zero_hit hX h (ground hF ha hp hk h); let l: X→ X→L[ℝ]ℝ:=fderiv ℝ X'; let T (v:X):= speedsK t (r • v); have hl : T 0=grad t:=by unfold T; rw [smul_zero,speedStart]
    let f':X→ℝ:= fun x=> fderiv ℝ X' x (T x)
    have hv:f'=ᶠ[𝓝 0] 0:=by
        obtain ⟨d,hd,ht⟩:= beeps G; have he : Tendsto (fun x:X=>‖tint G _ (r • x)‖) (𝓝 0) (𝓝 0):=by
            let P:X→L[ℝ]fieldDir G n 1 := (tint G _).toContinuousLinearMap.comp (r • ContinuousLinearMap.id ℝ X); have ht:= P.continuous.norm.tendsto 0; rw [show ‖P 0‖=0 from (by rw [map_zero,norm_zero])] at ht; exact ht
        filter_upwards [he.eventually (eventually_lt_nhds hd),hp.eventually (by simp)] with x hx hv; exact vineyard A r ht ha x t (fun i=>(norm_le_pi_norm _ i).trans_lt hx) (hv.differentiableAt (by exact_mod_cast (show k≠0 from by omega))) hr.ne'
    have hl' : DifferentiableAt ℝ l 0:= (hX.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp); have hp': DifferentiableAt ℝ T 0:=by
         refine DifferentiableAt.comp (f:=fun x:X=> r • x) (g:=speedsK t) (𝕜:=ℝ) 0 ?_ ?_; · rw [smul_zero]; exact (speedV t).differentiableAt (by simp)
         exact (r • ContinuousLinearMap.id ℝ X).differentiableAt
    have hi: rim X' x (grad t)=0 := by
         have hb:= hl'.hasFDerivAt.clm_apply hp'.hasFDerivAt; have hu := (hb.fderiv).symm.trans (hv.fderiv_eq (𝕜:=ℝ)); have hv := congr_arg (fun i:X→L[ℝ]ℝ=>i x) hu; rw [fderiv_zero] at hv
         change l 0 _ + (fderiv ℝ l 0 x) (T 0)=0 at hv; rw [show l 0=0 from he,_root_.zero_apply,zero_add,hl] at hv; exact hv
    have hT(t':ℕ)(ht:t' ≤ p+1): iteratedFDeriv ℝ 2 (fun z=> ∑ i∈range t',r^i*W i z) 0 ![x,grad t]=0:=by
        induction t' with|zero=> simp -- zero jet >0
                         |succ j ih=>
           have hf(i:ℕ): ContDiffAt ℝ 2 (W i) 0 := (vent ..).contDiffAt.of_le le_top; have he : ContDiffAt ℝ 2 (fun z=>∑ i∈range j,r^i*W i z) 0:=ContDiffAt.sum fun i _=> (hf i).const_smul (r^i)
           simp_rw [Finset.sum_range_succ]; change iteratedFDeriv ℝ 2 ((fun z=>∑ i∈range j,r^i*W i z)+ (r^j • W j)) 0 _= _
           rw [iteratedFDeriv_add_apply he (show ContDiffAt ℝ 2 (r^j • W j) 0 from (hf j).const_smul (r^j)),iteratedFDeriv_const_smul_apply (hf j),_root_.add_apply,_root_.smul_apply,ih (by omega),iteratedFDeriv_two_apply]; change 0+r^j * rim (W j) x (grad t)=0; rw [show rim (W j) x (grad t)=0 from gentle _ _ _ _ hF j (by omega) h t x, mul_zero,zero_add]
    change rim (X'-V) x (grad t)=0; rw [show rim _ x (grad t)=_ from (iteratedFDeriv_two_apply (X'-V) 0 ![x,grad t]).symm, iteratedFDeriv_sub_apply hX hV,_root_.sub_apply, show iteratedFDeriv ℝ 2 V 0 _=0 from hT _ le_rfl, sub_zero,iteratedFDeriv_two_apply]; exact hi
end YM.MSbar.Aqua
