import YM.MSbar.Wave.Rider
import YM.MSbar.Rolling.Revenue
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open scoped Topology Classical BigOperators ContDiff
variable {σ: Type} [Fintype σ]
open Set MvPolynomial
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
variable (b: PowerSeries ℝ)(hb:µ 0 b=1)(p:ℕ){S:ℝ→ℝ}(hS:Approx S b p)
include hb hS
local notation "τ!"=> (fun x:ℝ=> x/S x)
lemma boundsS : ∀ᶠ t:ℝ in Γ,t/2 ≤ t/S t ∧ t/S t ≤ 2*t:=by
    filter_upwards [width,hS.little hb] with x ⟨hx,hT,hL⟩ hs; have hp:0 < S x:=lt_of_lt_of_le (by norm_num) hs.1; refine ⟨div_le_div_of_nonneg_left hx.le hp hs.2, (div_le_div_of_nonneg_left hx.le (by norm_num) hs.1).trans_eq (by ring)⟩
lemma tends : Tendsto τ! Γ Γ:=by
    let g:= τ!; have hg:Tendsto (fun x :ℝ=> x) Γ (𝓝 0):= tendsto_id.mono_left nhdsWithin_le_nhds
    have hx:Tendsto (fun x:ℝ=>x/2) Γ (𝓝 0):=by simpa using hg.div_const 2
    have h:Tendsto (fun x:ℝ=>2*x) Γ (𝓝 0):=by simpa using hg.const_mul 2
    have hV:=boundsS b hb p hS; have hf:Tendsto g Γ (𝓝 0):=tendsto_of_tendsto_of_tendsto_of_le_of_le' hx h (hV.mono fun i h=> h.1) (hV.mono fun i h=> h.2)
    exact tendsto_nhdsWithin_iff.mpr ⟨hf,(width.and hV).mono (fun x h=> lt_of_lt_of_le (half_pos h.1.1) h.2.1)⟩
lemma tunnel : ∀ᶠ t:ℝ in Γ, fuel (t/S t) ≤ 2*fuel t ∧ fuel t ≤ 2*fuel (t/S t):=by
    have hv:= tends b hb p hS; filter_upwards [width,hv.eventually width, boundsS b hb p hS,hS.little hb, awake.eventually_ge_atTop (Real.log 2), (awake.comp hv).eventually_ge_atTop (Real.log 2)] with t ⟨hx,h1,hz⟩ ⟨ht,hq,h₃⟩ ⟨hc,hc'⟩ ⟨hs,hS⟩ hl hw
    have hP: 0 < S t:= lt_of_lt_of_le (by norm_num) hs; have he: fuel (t/S t)=fuel t+Real.log (S t):=by unfold fuel; rw [Real.log_inv, Real.log_inv,Real.log_div hx.ne' hP.ne']; ring; -- log inv signature
    constructor
    · linarith only [he,hl,Real.log_le_log hP hS]
    have hy : - Real.log 2 ≤ Real.log (S t):=by apply le_trans _ (Real.log_le_log (by norm_num) hs); rw [one_div, Real.log_inv]
    linarith only [he,hy, (show Real.log 2 ≤ fuel (t/S t) from hw)]
variable {X:Type*} [NormedAddCommGroup X][NormedSpace ℝ X]
lemma couplings (n:ℕ): ∃ q:ℕ,∀ᶠ t in Γ,∀ i :X, yard n t i → yard q (t/S t) (S t • i):=by
    refine ⟨n+1,?_⟩; let C:=2*(2:ℝ)^n; filter_upwards [hS.little hb,width,(tends b hb p hS).eventually width,tunnel b hb p hS, (awake.comp (tends b hb p hS)).eventually_ge_atTop C] with t ⟨h1,h2⟩ ⟨hx,ht,hu⟩ ⟨ha,hS,hB⟩ ⟨hk,hl⟩ h i hp; have hv:0 ≤ S t:= le_trans (by norm_num) h1; change ‖S t • i‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hv]
    let f:=fuel (t/S t); change _ ≤ f ^ _; have hc: 0 ≤ f := zero_le_one.trans hB
    apply (mul_le_mul h2 ((show ‖i‖ ≤ _ from hp).trans (pow_le_pow_left₀ (zero_le_one.trans hu) hl n)) (norm_nonneg _) zero_le_two).trans; rw [pow_succ,mul_pow,← mul_assoc]; exact (mul_le_mul_of_nonneg_right h (pow_nonneg hc n)).trans_eq (mul_comm ..)
lemma pays {d:ℕ} {P:ℝ→X→ℝ} (n:ℕ)(h:∀ q, Price (yard q) d P) : Price (yard n) d (fun x v=> P (x/S x) (S x • v)):=by
   obtain ⟨q,hh⟩:= couplings (X:=X) b hb p hS n; obtain ⟨v,hv⟩:=h q; let C:ℝ:=2^d*2^v
   apply fixed v C; filter_upwards [hh,width, (tends b hb p hS).eventually hv,(tends b hb p hS).eventually width,tunnel b hb p hS,boundsS b hb p hS] with x hg ⟨hx,_h,hT⟩ hV ⟨hV',_,he⟩ hN hB k hd; refine (hV _ (hg k hd)).trans ((mul_le_mul (pow_le_pow_left₀ hV'.le hB.2 d) (pow_le_pow_left₀ (zero_le_one.trans he) hN.1 v) (pow_nonneg (zero_le_one.trans he) _) (by positivity)).trans_eq ?_); unfold C; ring
end YM.MSbar.Wave
