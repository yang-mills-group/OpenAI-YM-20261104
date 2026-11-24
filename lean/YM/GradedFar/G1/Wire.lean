import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Price numerical windows

We'll first solve on `Edge`: 1≤T≤(g^K)^-1, K *integer*. This permits a
shape exponent comparison for any B via `move`. Uniform polynomial and log charging.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.G1.Wire
open Function Filter Set Real Asymptotics
open scoped Topology Classical BigOperators
variable {P U B K g T x : ℝ} {L : ℕ}
def Edge (K:ℕ) (g T:ℝ) := 1≤T ∧ T*g^K ≤ 1
lemma edge_iff (hg:0<g):Edge L g T ↔ 1≤T∧ T ≤ g^(-(L:ℝ)) := by unfold Edge; rw [Real.rpow_neg hg.le,Real.rpow_natCast,←one_div,le_div_iff₀ (by positivity : 0<g^L)]
lemma bounded (hg:0<g)(e:Edge L g T):T≤(g^L)⁻¹ := by simpa only [Real.rpow_neg hg.le,rpow_natCast] using ((edge_iff hg).mp e).2
lemma move (U B:ℝ)(b: B < L)(_hU:0<U) :
    ∀ᶠg in 𝓝[>] (0:ℝ), ∀ T≥1, T≤U*g^(-B) → Edge L g T := by
  have H : Tendsto (fun g:ℝ=>U*g^((L:ℝ)-B)) (𝓝[>] 0) (𝓝 0) := by
    have y:Continuous (fun g:ℝ=>g^((L:ℝ)-B)):=Real.continuous_rpow_const (by linarith : 0≤(L:ℝ)-B)
    have p:=((y.tendsto 0).const_mul U).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)); rwa [Real.zero_rpow (by linarith),mul_zero] at p -- missing mul_zero
  filter_upwards [H.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),self_mem_nhdsWithin] with g e gp T t c
  have p:0<g:=gp; refine ⟨t,?_⟩; apply le_trans (mul_le_mul_of_nonneg_right c (pow_nonneg p.le L));
  rw [mul_assoc, ←Real.rpow_natCast g L,←Real.rpow_add p, neg_add_eq_sub]; exact e.le

lemma exhaust {hg:0<g}(u : Edge L g T) (a:1≤x)(hx:x≤T) : Edge L g x :=
 ⟨a,(mul_le_mul_of_nonneg_right hx (pow_nonneg hg.le L)).trans u.2⟩

/-- Uniform log tariff even at T=1. -/
abbrev tick (T:ℝ) := 1+log T
lemma starts {T:ℝ}(t:1≤T):1≤ tick T:=le_add_of_nonneg_right (Real.log_nonneg t)
lemma distills {δ C:ℝ}(h:0<δ) (p:0 ≤ C) (a L:ℕ) :
    ∀ᶠg in 𝓝[>] (0:ℝ), ∀ T, Edge L g T → C*tick T^a * g ≤ δ := by
  let b:= ((L+1:ℕ):ℝ)
  have hb:1≤b:=by dsimp [b]; exact_mod_cast Nat.le_add_left 1 L
  let k:=δ/(1+C*b^a); have den : 0<1+C*b^a := by positivity
  have wk:0<k:=div_pos h den
  have c:= (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (a:ℝ) (s:=-1) (by norm_num)).bound wk
  filter_upwards [c, Real.tendsto_log_nhdsGT_zero.eventually_le_atBot (-1), self_mem_nhdsWithin] with g c hlog h₀ T u
  have hg:0<g:=h₀
  have pT:=zero_lt_one.trans_le u.1
  have e : tick T ≤ b*|log g| := by
    have he:=u.2; have ht := Real.log_le_log pT (bounded hg u); rw [Real.log_inv, Real.log_pow] at ht
    unfold tick b; rw [abs_of_nonpos (by linarith)]; push_cast; linarith
  have size : |log g|^a ≤ k*g⁻¹ := by
    rw [Real.rpow_natCast,Real.rpow_neg_one,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at c; exact c
  have H1:1 ≤ tick T:=starts u.1
  calc _ ≤ C*(b*|log g|)^a *g := by gcongr
       _ ≤ C*(b^a)*(k*g⁻¹)*g:=by rw [mul_pow, ←mul_assoc C]; gcongr
       _ = C*b^a*k:=by field_simp
       _ ≤ (1+C*b^a)*k := by gcongr; simp
       _ = δ:=mul_div_cancel₀ δ den.ne'

lemma receipts (hg:0<g)(u:Edge L g T) (b:ℕ): T^b*g^(L*b) ≤ 1 := by
  rw [pow_mul,←mul_pow]; exact pow_le_one₀ (mul_nonneg (zero_le_one.trans u.1) (by positivity)) u.2
lemma tiny (K:ℕ) (a:ℕ)(C δ : ℝ) (hc:0≤C)(h:0<δ) : ∀ᶠg in 𝓝[>] (0:ℝ), ∀ T, Edge K g T →
    (1+C*tick T^a)*g ≤ δ := by
  filter_upwards [distills (C:=C+1) h (by linarith) a K, self_mem_nhdsWithin (α:=ℝ) (a:=0)] with g H p T v
  have hs:=starts v.1
  have p':0<g:=p
  apply le_trans _ (H T v); apply mul_le_mul_of_nonneg_right _ p'.le; rw [add_mul,one_mul]
  linarith [one_le_pow₀ (n:=a) hs]
end YM.FVA2.GradedFar.G1.Wire
