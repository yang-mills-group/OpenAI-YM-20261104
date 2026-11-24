import YM.OPE.Beams.Roll
/-! # Thinner geometry from exact birth plan. all ancestor views -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open Trunk Rhythm
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {T:L→ℝ}{M η P₀:ℝ}{v j k:I}
    {X:L→ I→ E4}{x:L→ (I→ E4)→ J→ E4}
    {H t n m:ℕ}{Q: Rhythm I}
    {R r:L→ℕ→ℝ}{α:ℕ→ℝ}{Y: L→ ℕ}
    (B:Border f T Q.limit R r α)
    (hh:H ≤ Q.age Q.star)(hm:0 ≤ M)(hη:0<η)(hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))
local notation "X'"=> (I→E4)
local notation "ξ!"=> Border.orbit Q H T r X
local notation "μ"=> Q.localTime H
variable (Q H T r)
def action (i:L)(k j:I):= Q.reaches H (r i (Q.localTime H k)/T i) k j
variable {Q H T r}
local notation "πc"=> action T H Q r
lemma acted (i:L)(j:I)(z:X') : ξ! i z j=X i j+ ∑ k, (πc i k j) • z k:=by
    unfold Border.orbit moveElig; rw [show (∑ a, (Q.reaches H (Border.pitches Q H T r i z a) a j))= _ from ?_]; exact sum_congr rfl fun a _=> by by_cases he: Q.tracked H a j<;> simp [reaches,he, action,Border.pitches]
include B hh hm hη hX
lemma slender_lane : Slender f T (ξ!) (πc):=by
    have ht:= B.trajectory hh hX hη; let γ:=η/2; let t:= M+γ; let h:=η/2/2; have he:0<γ:=half_pos hη; have hE:0 ≤ t:= add_nonneg hm he.le; have hG:0<h:=half_pos he; have hh'(i): μ i ≤ Q.limit:= (Q.timeBirth hh i).trans (Q.bounded i)
    refine ⟨⟨fun i=>?_,fun i z k a s=>?_,fun k i j hx a hb=>?_⟩,?_,?_⟩
    · apply differentiable_pi.mpr; intro j; simp_rw [acted]; exact differentiable_const _|>.add (Differentiable.fun_sum fun a _=>by fun_prop) -- lemma
    · funext j; simp_rw [along,acted,Pi.add_apply,smul_add,sum_add_distrib,Pi.smul_apply,← add_assoc]; congr 1; rw [sum_eq_single a]; · unfold ray; rw [Pi.single_eq_same,smul_smul,mul_comm]
      · intro b _ hk; simp [ray,Pi.single_eq_of_ne hk]; -- orientation
      simp
    · let d:= Q.gap i j; have hP:d ≤ Q.limit:= GapHomebound i j; let ν i:= r i d/T i; let v i:= jacket (T i); have hh := (B.rates d hP).mul (RateIs.const B.life (mul_pos hb hG)); have hU:∀ᶠ i in f, jacket (T i) < r i d*(a*h):= hh.overtakes ((jacket_price B.life).pays B.life) B.life (show (-3:ℝ)< - α d+0 from (by linarith only [B.pace d hP|>.2]))
      filter_upwards [hU,ht,(B.rates d hP).pos,(B.rates (μ k) (hh' k)).pos,B.life.eventually_gt_atTop 0,(tendsto_inv_atTop_zero.comp B.life).eventually (ge_mem_nhds (mul_pos hb hG)), (show ∀ᶠ i in f,∀ t∈ Iic Q.limit,d ≤ t→ r i t ≤ r i d from (eventually_all_finset _).mpr (fun t hi=> eventually_all.mpr fun hp:d ≤ t=> (B.in_order hp (mem_Iic.mp hi)).mono fun i h=> h.1))] with i' hu ht hp hp' hi hv hi' z hz; -- h shadows
      have hp'' : |πc i' k i-πc i' k j| ≤ ν i':=by
         rcases lt_or_ge (μ k) d with he|he; · unfold action; rw [Q.follow_finer _ (Or.inr (show d ≤ Q.gap i j from le_rfl)) he,sub_self,abs_zero]; exact div_nonneg hp.le hi.le
         have hU:r i' (μ k)/T i' ≤ r i' d/T i':= div_le_div_of_nonneg_right (hi' _ (mem_Iic.mpr (hh' k)) he) hi.le; let v':=r i' (μ k) /T i'; have hp:0 < v':= div_pos hp' hi; have hf:0 ≤ ν i':=(hp.trans_le hU).le; have het: abs (r i' (μ k)/T i') ≤ ν i':= (abs_of_nonneg hp.le).le.trans hU; by_cases he:Q.tracked H k i <;> by_cases ht:Q.tracked H k j <;> simp [action,reaches,he,ht,hf,het]
      unfold ν at hp''; rw [div_eq_mul_inv] at hp''; have he':= (ht z hz).reserve i j hx; change γ*r i' d < _ at he'; have hw : r i' d * (T i')⁻¹ ≤ r i' d*(a*h):= mul_le_mul_of_nonneg_left hv hp.le; have hx' : h+h=γ:=by unfold h γ; ring
      calc _ ≤ r i' d*(a*h)+r i' d*(a*h):= add_le_add (hp''.trans hw) hu.le
           _ = a*(γ*r i' d):=by rw [← hx']; ring
           _ ≤ _:=mul_le_mul_of_nonneg_left he'.le hb.le
    · intro a j; unfold action reaches; by_cases h: Q.tracked H a j
      · simp_rw [if_pos h]; simpa only [div_eq_mul_inv,mul_zero, Function.comp_apply] using (B.before (hh' a)).mul (tendsto_inv_atTop_zero.comp B.life)
      simp_rw [if_neg h]; exact tendsto_const_nhds
    intro j k hk; have hy:Tendsto (fun i=>2*(t*R i 0)) f (𝓝 0):=by simpa only [mul_zero] using! (((B.narrows 0 (Nat.zero_le _)).const_mul t)|>.const_mul 2)
    filter_upwards [hy.eventually (ge_mem_nhds hk), ht,(B.ahead (Nat.zero_le _)).pos,(eventually_all_finset (Iic Q.limit)).mpr (fun i hi=> B.in_order (Nat.zero_le i) (mem_Iic.mp hi))] with i hi ht hp hO z hz; have hw:= (show BlockFrame Q (fun t'=>t* R i t') _ _ H from ht z hz).whole (i:=j) hh (Nat.zero_le _) (fun i _ ht=> mul_le_mul_of_nonneg_left (hO i (mem_Iic.mpr ht)|>.2) hE) (mul_nonneg hE hp.le); rw [Q.lead_zero (Q.pinned_init j) _,sub_zero] at hw; exact hw.trans hi
end YM.OPE.Log.Reels
