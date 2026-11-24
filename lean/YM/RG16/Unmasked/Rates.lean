import YM.RG16.Unmasked.Plot
import YM.OPE.Prices.Circuit
import YM.OPE.Log.Fees
/-!
# Power-scale room for the *exact* relation.Copies

Up through measurement at height 1 = both launch and capture. Modifies the
Levy preparation by using moment-normalized input coordinates, permitting
all cutoff-dependent frame conversions with subpower-spatial cost. Result is
true at **every** k in the price & layout regime, no late-top existential
stencils. We haven't asserted formal operations have such prices (coupling
power needs stronger inputs later, multi-marker estimates leading to capture).
These are just enough to register the *root relation* on all jobs.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG16.Literal
open Set Function Filter MeasureTheory Lattice RG OPE MergeProof Ribbons Accent Source Overlay Bid
open ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage Cells Push.GridApprox
open Extra.Histories Trace.Physical.GermGraph Pert.Asymptotics
open scoped BigOperators Topology Matrix.Norms.Frobenius
set_option quotPrecheck false
variable {G : Gauge} (C: Family G) (hG:G.Simple) {W r D} (L:Package C W r D)
local notation "P" => C.path.levels
local notation "α" => renal C.path.levels
local notation "κ" => fly C.path.levels
local notation "σ" => C.S.scale
local notation "β" => C.path.levels.clock.hatBeta
local notation "Θ" => near C.path.levels
local notation "τ" => bling C.path.levels
local notation "a!" => C.S.a -- drop if named arg
local notation "F" => C.labels.level

section frame
variable (h:C.Makes)(N p d:ℕ)
include h
-- loose g^-d cap using threshold ≤ 1. we don't spend it as a relative step cost, only for enlisting colonies
lemma threshold_cap {k:ℕ}(hi:k≤N)(v:C.label d) :
    (F d).coeffSize (thresholdMap C N p d k v) ≤
      (2*β k)^(degree (F d))*(F d).coeffSize v := by
   let P':= C.path.rep N p k; let Λ₀:= 2*(β k)
   have hg : 0<P'.beta:= Overlay.beta_positive h.wilson hi
   have hb : P'.beta ≤ Λ₀:= (h.wilson.represents _ _ _ hi).band.2
   let s:= Real.sqrt P'.beta
   have hz : 0<s:= Real.sqrt_pos.mpr hg
   have h1 : 1≤ Λ₀:=by have hh := (P).fits.delayed k; unfold Λ₀; linarith
   have hx : s≤ Λ₀:= le_trans (Real.sqrt_le_sqrt hb) (by nlinarith only [Real.sq_sqrt (zero_le_one.trans h1),h1,Real.sqrt_nonneg Λ₀])
   let t:= (P'.p.threshold / regulatorRun C N p k)
   have hy : t ≤ Λ₀:= by
      refine le_trans ?_ hx; change P'.p.threshold / s⁻¹ ≤ s; rw [div_inv_eq_mul]; apply mul_le_of_le_one_left hz.le P'.p.threshold_le
   have ht:0<t:=div_pos P'.p.threshold_pos (g_pos h hi)
   unfold Labels.Frame.coeffSize; rw [Finset.mul_sum]
   refine Finset.sum_le_sum (fun i hi₀=> ?_)
   rw [thresholdMap, Labels.Frame.scaled_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (show 0≤t^_ from pow_nonneg ht.le _)]
   refine mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ ht.le hy _).trans (pow_le_pow_right₀ h1 ?_)) (norm_nonneg _)
   exact Finset.le_sup (f:=fun i=>(F d|>.grades i).2) hi₀

-- includes true page evaluation and translation units on full stencil
lemma master_price (k:ℕ)(hk:Opened C d k p)(hi:k ≤ N) (x:C.label d) :
    Next.Rank.Spindle.paid C d k N p (master C N p d h k hk hi x) ≤
      2*((2*β k)^(degree (F d))*(F d).coeffSize x) := by
   let v:= (fitting d N p k h hk hi).symm (thresholdMap C N p d k x)
   have hs:= (size_gap d N p k h hk hi v).2
   rw [(show page d p k ((C.factory d N p).entries k v) = _ from (fitting d N p k h hk hi).apply_symm_apply (thresholdMap C N p d k x))] at hs
   let t:= (C.S.a k:ℂ)^d
   have hx := (h.calibrated d N p (hk.post.trans hi)).linear k hk.post hi
   have hg : ((C.factory d N p).entries k (t • v)).x=t • ((C.factory d N p).entries k v).x:= hx.1.map_smul ..
   have hp:= C.S.a_pos k
   apply le_of_mul_le_mul_left (a := a! k ^ d) -- binder check
   · rw [Log.obey_quota,Next.UVStress.quota,master,LinearEquiv.symm_apply_apply,hg,Size.smul, show ‖t‖=a! k^d from by unfold t; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le]]
     exact mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left (threshold_cap C h N p d hi x) zero_le_two)) (pow_nonneg hp.le _)
   exact pow_pos hp _
end frame

variable {b E A:ℕ→ℕ}{g z:ℕ→ℝ}(I:Type)[Fintype I][DecidableEq I](i₀:I)
local notation "ν" => Fintype.card I
variable {B:ℕ→ℕ}

def weight (d k:ℕ) := Real.exp ((d+1/16:ℝ)*(C.S.scale k))
lemma weight_pos (d k:ℕ) : 0 < weight C d k := Real.exp_pos _

-- Adapt Height prices to explicitly FIX u and J auxiliary reference & repayment.
lemma gain_toward (t:ℕ) (hb:Height C.S atTop σ b 1) :
    RateIs atTop σ (fun i=> gainChart C.path (b i) t) (1/8:ℝ) :=
  RateIs.exp' (by
    have hu:= (tendsto_const_nhds (x:=σ t)).div_atTop C.S.divergent
    simpa only [sub_zero,mul_one,←sub_div,←mul_div_assoc] using! ((hb.pace.sub hu).const_mul (1/8:ℝ)))

include L hG
lemma late_march (t d : ℕ)(ht:C.ref d ≤ t) (hb:Height C.S atTop σ b 1)
    (hg:RateIs atTop σ g (-(d:ℝ)))(he:RateIs atTop σ z 0) : ∀ᶠ k in atTop,
    march (fun _:Unit=> weight C d k) Θ t (b k) () ≤ α (b k)*(z k/(16*τ (b k))) ∧
    32*(1+(P|>.params (b k)).columns)*weight C d k*‖alto C.path t d‖*(g k/gainChart C.path (b k) t) ≤ κ d t/2:= by
    let f:= (κ d t); have hF : 0<f := L.system.grows d t ht
    have hv := C.S.divergent; let K:= (P|>.params t).columns
    have hw:RateIs atTop σ (weight C d) (d+1/16:ℝ):= RateIs.exp _ hv
    have ht':= height0 (mintN C hG|>.1) hb
    have hq:= ht'.mul (he.div ((RateIs.const (c:=16) hv (by norm_num)).mul (height0 (banket C hG) hb)))
    have hu:= RateIs.const hv hF
    have hp:= (hw.mul ((hb.mesh.div (RateIs.const hv (C.S.a_pos t))).power (d+1))).mul ((flyRate hG hb d).div hu)
    have he_:0< ‖alto C.path t d‖:= by rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos t) _)
    have hA := (RateIs.const (c:=32) hv (by norm_num)).mul ((RateIs.const (c:=1) hv one_pos).add (height0 (fuNote C) hb) hv)
    have h' := (((hA.mul hw).mul (RateIs.const hv he_)).mul (hg.div (gain_toward C t hb)))
    filter_upwards [hq.overtakes (hp.pays hv) hv (by push_cast; linarith), (hu.div (RateIs.const hv zero_lt_two)).overtakes (h'.pays hv) hv (by rw [max_self]; linarith),hb.grows.eventually_ge_atTop t] with k hp' he' hh
    exact ⟨(seeing C d L.system (weight_pos C d k) (b k) t ht hh).trans hp'.le,he'.le⟩
end YM.RG16.Literal
