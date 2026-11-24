import YM.SharpGram.Annulus.Horizon
import YM.Pert.Asymptotics.RawAxis

/-!
# RG05: accounting for actual log powers & coupling

`Lambda` from the `qfull` formulation, NOT beta used by LogTrace.
Stay explicitly in the band and allow a uniform local mismatch caller
expense of P^p (includes normalization losses) and fixed local truncation
loss η≤1. Prove precise conversion to reporting slack. Cannot consume
`juice` via this lemma (β growth results negative); see companion lemma
for spatial Qi-type errors. This is real coupling and actual trajectories;
not a prescription uniquely selecting running g in another scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Allow
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Lenses Weak.Portfolio OPE
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {k : ℕ}
local notation "P"=> C.path.levels.clock.hatBeta

-- All-small beta domains. Preserves true Wilson coupling, not a formal use of Z reset.
def Band (C : Family G) (k : ℕ) := Set.Icc (C.path.levels.clock.hatBeta k/2) (2*C.path.levels.clock.hatBeta k)
abbrev Lambda (C : Family G) (k : ℕ) := 2+Real.log (C.path.levels.clock.hatBeta k)
def outputPower (r p:ℕ):= r+1+2*p
abbrev coupling (β : ℝ) := (Real.sqrt β)⁻¹
lemma includes (C : Family G) (h:C.Makes) (k N p:ℕ) (hp:k≤N) : C.path.β N p k∈Band C k ∧ coupling (C.path.β N p k)=Pert.Asymptotics.regulatorRun C N p k:=
    ⟨(h.wilson.represents _ _ _ hp).band,rfl⟩
lemma allowed {b:ℝ} {l : Type*} (u:Filter l) [u.NeBot] (C:Family G) (hC:C.Makes) (N p:l→ℕ) (h:Tendsto (fun i=>C.path.β (N i) (p i) k) u (𝓝 b))
    (hv:∀ᶠ i in u,k ≤ N i) : b∈ Band C k := isClosed_Icc.mem_of_tendsto h (hv.mono fun _ hi=>(includes C hC k _ _ hi).1)
lemma lambda_pos (C:Family G) k : 0<Lambda C k := add_pos_of_pos_of_nonneg zero_lt_two (Real.log_nonneg (C.path.levels.fits.delayed k).le)
lemma beta_pos {β:ℝ} (h:β∈Band C k) : 0<β:= (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed k))).trans_le h.1
lemma coupling_pos {β:ℝ}(h:β∈Band C k):0<coupling β:=inv_pos.mpr (Real.sqrt_pos.2 (beta_pos h))
lemma later (C:Family G) (hG:G.Simple) : ∀ᶠ k in atTop, ∀ β∈ Band C k, coupling β≤1 := by
    filter_upwards [(Next.Rank.Station.hat_rate C.path.levels hG).eventually_ge_atTop 2] with k hk β h
    apply inv_le_one_of_one_le₀ (Real.le_sqrt_of_sq_le ?_); linarith only [hk,h.1]
lemma caps {β : ℝ} (h : β∈ Band C k) : P k * coupling β ^ 2 ≤ 2 := by
    refine le_trans (mul_le_mul_of_nonneg_right (by linarith only [h.1] : P k ≤2*β) (sq_nonneg _)) (le_of_eq ?_)
    have he := Real.sq_sqrt (beta_pos h).le; unfold coupling; rw [inv_pow,he,mul_assoc,mul_inv_cancel₀ (beta_pos h|>.ne'),mul_one]
lemma internal {β η : ℝ} (h : β∈ Band C k)(hv : coupling β≤1) {p r R:ℕ} (hm : outputPower r p ≤ R) (hη : η ≤ 1) :
   P k ^ p * coupling β ^ ((R:ℝ)+1-η) ≤ (2:ℝ)^p * coupling β ^ (r+1) := by
    let s:=coupling β; have hs : 0<s:= coupling_pos h
    have he := caps h; have hb: 0 < P k := zero_lt_one.trans (C.path.levels.fits.delayed k)
    unfold outputPower at hm
    have hR : s ^ ((R:ℝ)+1-η) ≤ s^(r+1+2*p) := by
       rw [← Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_ge hs hv; exact (Nat.cast_le (α:=ℝ).mpr hm).trans (by linarith)
    apply le_trans (mul_le_mul_of_nonneg_left hR (pow_pos hb _|>.le))
    calc
       _ = (P k*s^2)^p * s^(r+1):= by rw [pow_add s (r+1),pow_mul,mul_pow]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he p) (pow_pos hs _|>.le)
end YM.SharpGram.Allow
