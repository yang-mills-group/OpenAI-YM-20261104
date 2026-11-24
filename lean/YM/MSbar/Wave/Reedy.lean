import YM.MSbar.Rolling.Stays
import YM.Next.FOUNDATIONS.LinkBounds
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Function Filter Rolling Price Tensor
open scoped Topology Classical BigOperators ContDiff
variable {n:ℕ}{f:ℝ→ℝ}
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
def Grade (f:ℝ→ℝ)(n:ℕ): Prop := Price (fun _ (_:Unit)=> True) n (fun t _=> f t)
local notation "µ"=>Tensor.coeff
noncomputable def bill(f:ℝ→ℝ)(n:ℕ):= Tensor.diagonal (Tensor.coeff f n 0) 1
lemma certified (hf:ContDiffAt ℝ ω f 0)(n:ℕ) : Grade (fun x=> f x-∑ i∈ Finset.range (n+1), x^i*bill f i) (n+1):=by
    obtain ⟨r,C,H,hc,h⟩:= taylorQuote (hf.of_le (m:=↑(n+1:ℕ)) le_top); refine Price.fixed 0 C ?_
    filter_upwards [width,(eventually_lt_nhds H).filter_mono nhdsWithin_le_nhds] with x ⟨hx,he,hF⟩ hk i _
    let g(j:ℕ):=Tensor.diagonal (Tensor.coeff f j 0); have hu(j:ℕ): g j x=x^j*bill f j:=by nth_rw 1 [← show x • (1:ℝ)=x from mul_one x]; exact homogeneous ..
    rw [show (∑ i∈ Finset.range (n+1),x^i*bill f i)=Work.G05.blockTaylor n f x from ?_]; swap; · unfold Work.G05.blockTaylor; rw [Finset.sum_apply]; exact Finset.sum_congr rfl (fun i _=> (hu i).symm)
    have hm : x∈Metric.closedBall (0:ℝ) r:= Metric.mem_closedBall.mpr (show _ ≤ _ from by rw [dist_zero_right,Real.norm_of_nonneg hx.le]; exact hk.le)
    exact (h x hm).trans_eq (by rw [Real.norm_of_nonneg hx.le]; ring)
open Finset
lemma magnitude {f:ℕ→ℝ}(hf : Grade (fun x=>∑ i∈ Finset.range (n+1),x^i*f i) (n+1)):∀ i,i≤n → f i=0:=by
    intro i; induction i using Nat.strong_induction_on with
    | h i ih=>
        intro he; obtain ⟨q,H⟩:= Price.poorly hf (by omega : i+1≤n+1); let X:= Finset.range (n+1)
        let g(x:ℝ):=f i + ∑ j∈ X, if i<j then x^(j-i)*f j else 0; have hg : Continuous g:=continuous_const.add (by apply continuous_finsetSum; intro j hj; split; fun_prop; fun_prop)
        have hG(x:ℝ): x^i*g x=∑ j∈ X,x^j*f j:=by
            have hn:i∈X:=mem_range.mpr (by omega); unfold g
            rw [← sum_erase_add _ _ hn,if_neg (by omega : ¬i < i),add_zero,mul_add,mul_sum,add_comm,← sum_erase_add _ _ hn]; congr 1; refine sum_congr rfl (fun j hj=>?_); have hu: j ≠ i:=ne_of_mem_erase hj; split; next hP=> rw [← mul_assoc,←pow_add,show i+(j-i)=j from (by omega)]
            next he'=> rw [ih j (by omega) (by omega), mul_zero,mul_zero]
        have hp : g 0=f i:=by unfold g; rw [Finset.sum_eq_zero,add_zero]; intro j hj; split; rw [zero_pow (by omega : j-i≠0),zero_mul];rfl
        have hh : Tendsto (fun i:ℝ=>‖g i‖) Γ (𝓝 ‖f i‖):=hp ▸ ((continuous_norm.comp hg).continuousAt.mono_left nhdsWithin_le_nhds) -- Tendsto vs ContinuousAt
        suffices hx:Tendsto (fun i:ℝ=>‖g i‖) Γ (𝓝 0) by exact norm_eq_zero.mp (tendsto_nhds_unique hh hx)
        apply squeeze_zero' _ _ (subs q); exact Eventually.of_forall (fun _=> norm_nonneg _)
        filter_upwards [width,H] with x ⟨hx,ht,hf'⟩ hh; have ht:=hh () trivial; rw [← hG x, norm_mul,norm_pow,Real.norm_of_nonneg hx.le,pow_succ,mul_assoc] at ht; exact le_of_mul_le_mul_left ht (pow_pos hx _)
lemma rebuilt (h:Grade f (n+1))(hf:ContDiffAt ℝ ω f 0):∀ i,i≤n→ bill f i=0:=
    magnitude (n:=n) (f:=fun i=> bill f i) ((Price.cut h (certified hf n)).egress (Eventually.of_forall (fun x _ _=>by ring)))
lemma sticky (h:Grade f (n+1))(hf:ContDiffAt ℝ ω f 0)(i:ℕ)(hi:i≤n) : iteratedDeriv i f 0=0:=by
    obtain he:=rebuilt h hf i hi; unfold bill Tensor.diagonal Tensor.coeff at he; rw [_root_.smul_apply,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at he; simp [(Nat.factorial_pos i).ne'] at he; exact he
-- interchange horizontal/vertical at origin for germs
variable (F:ℝ×ℝ→ℝ)(h:ContDiffAt ℝ ω F 0)
local notation "X"=> ℝ×ℝ
local notation "v₀"=> ((1:ℝ),(0:ℝ))
local notation "v₁"=>((0:ℝ),(1:ℝ))
def pine (f:ℝ×ℝ→ℝ)(n:ℕ) (y:X) (z:X):= Tensor.diagonal (Tensor.coeff f n y) z
lemma lion (z v:X) (n:ℕ) (hp:ContDiffAt ℝ ω F z) : bill (fun t=>F (z+t•v)) n=pine F n z v:=by
    let g(x:X):=F (z+x); have hG:ContDiffAt ℝ n g 0:= (show ContDiffAt ℝ n F (z+0) from add_zero z|>.symm ▸ hp.of_le le_top).comp _ (contDiffAt_const.add contDiffAt_id); let f'(x:ℝ):=F (z+x•v); have ht := Next.Foundations.iteratedDeriv_on_line hG v; unfold bill Tensor.diagonal pine Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,_root_.smul_apply]; apply congr_arg; rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; simp only [prod_const_one,one_smul]; unfold Tensor.diagonal g at ht; rw [iteratedFDeriv_comp_add_left] at ht; simpa only [add_zero] using ht
end YM.MSbar.Wave
