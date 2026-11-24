import YM.RG16.GaugeCredit.Phase

/-!
# Precision ledger; Λ-age growth

NOT the spatial costs. Expansion ALWAYS in THIS step's g; prepay
using a calendar-only price at this stage, BEYOND the weak pilot. Uniform
in level m, history depth N, period. Coupling translation explicit. Slack
from strengthened post-L choices on this actual construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Function Filter Set Lattice RG Wilson OPE MeasureTheory
open Pert Pert.Asymptotics Bid Trace.Physical.GermGraph
open Literal
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}(C:Family G)(H:C.Makes)(hG:G.Simple)
set_option quotPrecheck false
local notation "S" => C.S.scale
local notation "P" => C.path.levels
local notation "L" => factor C
local notation "Λ" => Lambda C.path.levels
local notation "β" => C.path.levels.clock.hatBeta
local notation "g" => regulatorRun C
local notation "B" => C.path.β

def coin (x:ℝ)(i:ℕ) := Real.exp ((-x/2) * Lambda C.path.levels i)
local notation "μ" => coin C

include H
lemma cashable {p N i:ℕ}(hi : i ≤ N) : g N p i ^ 2 * (B N p i) = 1:=by
   let b:= B N p i; have hb : 0<b:= Overlay.beta_positive H.wilson hi
   change (Real.sqrt b)⁻¹^2*b=1; rw [inv_pow,Real.sq_sqrt hb.le,inv_mul_cancel₀ hb.ne']

lemma g_band {p N i:ℕ}(hi:i ≤ N) : Real.exp 1 * μ 1 i/2 ≤ g N p i ∧ g N p i≤ 2*Real.exp 1* μ 1 i := by
    let b:= β i; let x:= Real.exp 1 * μ 1 i
    have hb:0<b:=zero_lt_one.trans ((P).fits.delayed i)
    have hx:0<x:=mul_pos (Real.exp_pos _) (Real.exp_pos _)
    have hcash : x^2=b⁻¹ := calc
      _ = Real.exp (2 * (1 + -1 / 2 * Λ i)) := by unfold x coin; rw [←Real.exp_add,pow_two,←Real.exp_add]; ring_nf
      _ = b⁻¹ := by unfold Lambda; change Real.exp (2*(1+-1/2*(2+Real.log b)))= b⁻¹; rw [show 2*(1+-1/2*(2+Real.log b)) = -Real.log b from by ring, Real.exp_neg, Real.exp_log hb]
    have he:= cashable C H (p:=p) hi; let v:= g N p i; let y:= B N p i
    have hy:0<y:=Overlay.beta_positive H.wilson hi; have hv : 0<v:=g_pos H hi
    have hC : y∈ Icc (b/2) (2*b) := (H.wilson.represents N p i hi).band
    have hw : b*x^2=1:= by rw [hcash,mul_inv_cancel₀ hb.ne']
    have hp : v^2*y=1:=he
    rw [mul_assoc (2:ℝ)]; change x/2 ≤ v ∧ v ≤ 2*x
    have hz : x^2≤2*v^2 := le_of_mul_le_mul_left (a:=b) (by linarith only [hw,hp,mul_le_mul_of_nonneg_left hC.2 (sq_nonneg v)]) hb
    have ht : v^2≤2*x^2 := le_of_mul_le_mul_left (a:=b) (by linarith only [hw,hp,mul_le_mul_of_nonneg_left hC.1 (sq_nonneg v)]) hb
    constructor<;>nlinarith

omit H
lemma coin_pos (x i) : 0<μ x i := Real.exp_pos _
lemma coin_zero (i): μ 0 i=1:=by simp [coin]
include hG in
lemma coin_down {x:ℝ}(h:0≤x): Antitone (coin C x):=fun i j h₀=> Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ((lambda_mono C hG).monotone h₀) (by linarith only [h]))
lemma coin_weaken {x y:ℝ}(h:y≤x)(i:ℕ): μ x i ≤ μ y i:= Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [h]) (lambda_pos C i).le)
lemma coin_add (x y:ℝ) (i:ℕ) : μ (x+y) i= μ x i*μ y i:= by unfold coin; rw [←Real.exp_add]; ring_nf
lemma coin_rpower (x y:ℝ) (i:ℕ) : (μ x i)^y=μ (x*y) i:=by unfold coin; rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]; ring_nf
lemma coin_power (x:ℝ) (t i:ℕ) : (μ x i)^t=μ (x*t) i:=by simpa only [Real.rpow_natCast] using coin_rpower C x (t:ℝ) i

include H
lemma buys_at {p N i:ℕ}(hi:i ≤ N)(x:ℝ)(h:0≤x):
    (Real.exp 1/2)^x*μ x i ≤ (g N p i)^x ∧ (g N p i)^x ≤ (2*Real.exp 1)^x*μ x i:=by
   obtain ⟨hf,hv⟩:=g_band C H (p:=p) hi; have ht:= Real.rpow_le_rpow (show 0≤ Real.exp 1*μ 1 i/2 from by have := coin_pos C 1 i; positivity) hf h
   have hs:= coin_rpower C 1 x i; rw [one_mul] at hs
   rw [←hs, ←Real.mul_rpow (by positivity) (coin_pos C 1 i).le, ← Real.mul_rpow (show 0≤2*Real.exp 1 by positivity) (coin_pos C 1 i).le]
   exact ⟨by rw [show Real.exp 1/2*μ 1 i=Real.exp 1*μ 1 i/2 from by ring]; exact ht, Real.rpow_le_rpow (g_pos H hi).le hv h⟩

omit H
include hG
lemma coin_exact (x:ℝ) : RateIs atTop Λ (μ x) (-x/2) := RateIs.exp _ (lambda_leads C hG)

lemma blue : RateIs atTop Λ Λ 0 := ⟨Eventually.of_forall (lambda_pos C), by
    simpa only [Function.comp_def, pow_one,one_mul,add_zero] using
     (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp (lambda_leads C hG)⟩

variable (hpace: ∀ i,((C.S.block i).val:ℝ) ≤ Real.log (Lambda C.path.levels i))
include hpace in
lemma platelet : RateIs atTop Λ (L) 0 := RateIs.of_sandwich (f:=fun _ : ℕ=> 1) (RateIs.const (lambda_leads C hG) zero_lt_one) ((blue C hG).pays (lambda_leads C hG)) (Eventually.of_forall fun i=> (factor_positive C i).le)
  (Eventually.of_forall fun i=> (hpace i).trans (Real.log_le_self (lambda_pos C i).le)) (lambda_leads C hG)
omit hG in
lemma smaller_receipt {x:ℝ} (hx:0≤x)(i:ℕ): μ x i ≤ 1:=(coin_weaken C hx i).trans_eq (coin_zero C i)
-- use arbitrary δ slack for any geometric polynomial (allocated once per use)
lemma allocate {g_ T:ℕ→ℝ}{a b:ℝ}(ha:b<a)(he:RateLE atTop Λ g_ b) (ht: RateIs atTop Λ T a): ∀ᶠ i in atTop,g_ i ≤ T i := by
   filter_upwards [ht.outweigh he ha (lambda_leads C hG)] with i h using (Real.le_norm_self _).trans h

lemma spend {x y:ℝ}{g_:ℕ→ℝ}(hy:x<y)(hs:RateLE atTop Λ g_ 0):∀ᶠ i in atTop, g_ i*μ y i ≤ μ x i := allocate C hG (by linarith only [hy]) (hs.mul ((coin_exact C hG y).pays (lambda_leads C hG))) (coin_exact C hG x)

include H in
lemma convert_in {g_:ℕ→ℝ}(hs:RateLE atTop Λ g_ 0) {x y:ℝ}(hy:x<y)(h:0≤y) : ∀ᶠ i in atTop,∀ p N,i ≤ N → g_ i*(g N p i)^y ≤ μ x i:= by
    let e : ℕ→ℝ:=fun i=>‖g_ i‖*(2*Real.exp 1)^y
    filter_upwards [spend C hG (g_:=e) hy (by simpa only [zero_add] using! hs.norm.mul (RateLE.const ((2*Real.exp 1)^y) (lambda_leads C hG)))] with i hi p N hiN
    have h₀:= (buys_at C H hiN y h (p:=p)).2
    have hW:= mul_le_mul (Real.le_norm_self (g_ i)) h₀ (Real.rpow_nonneg (g_pos H hiN).le y) (norm_nonneg (g_ i))
    refine hW.trans ?_; rw [←mul_assoc];exact hi
-- include H

include H in
lemma convert_out {g_:ℕ→ℝ}{x y:ℝ}(hs:RateLE atTop Λ g_ (-y/2))(hy:x<y)(hx:0 ≤ x): ∀ᶠ i in atTop,∀ p N,i ≤ N → g_ i ≤ (g N p i)^x := by
    have hw:= (RateIs.const (c:=(Real.exp 1/2)^x) (lambda_leads C hG) (Real.rpow_pos_of_pos (by positivity) _)).mul (coin_exact C hG x)
    filter_upwards [allocate C hG (by linarith only [hy]) hs hw] with i hi p N hiN using hi.trans (buys_at C H hiN x hx).1

omit hG in
lemma factor_tends : Tendsto (L) atTop atTop:=by
   apply tendsto_atTop.mpr; intro a; let b:=max 1 a
   have hb:(0:ℝ)<b:=zero_lt_one.trans_le (le_max_left ..)
   filter_upwards [factor_large C b⁻¹ (inv_pos.mpr hb)] with i hi using le_trans (le_max_right ..) (inv_inv b ▸ hi.1)

omit hG in
lemma quarter {γ:ℝ}(hr:γ<rate) : ∀ᶠ i:ℕ in atTop, L i^γ * L i^(-rate) ≤ 1/8:= by
    filter_upwards [((tendsto_rpow_neg_atTop (show 0 < rate-γ from sub_pos.mpr hr)).comp (factor_tends C)).eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1/8))] with i hi
    rw [← Real.rpow_add (zero_lt_one.trans (factor_positive C i)), show γ + -rate = -(rate-γ) from by ring]
    exact hi.le
end YM.RG16.Guarding
