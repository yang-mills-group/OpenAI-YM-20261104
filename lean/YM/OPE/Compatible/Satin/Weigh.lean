import YM.OPE.Compatible.Satin.Prices
/-! resolve polynomial earnings and uniform counting of finite readouts. applications exponent not per point. positivity and exponential weighting kept uniform for interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives){u:X}
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=> brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=> glen D U u
variable (p:X→ C.book.Token) (hu:u∈ rest U) {b d d' n:ℕ} {φ:Filter I} {s:I→X→ℝ} {r:I→ℝ} (Y:Burst D U φ r s)
-- several costs
local notation "p₀"=> fun i:V=>(p i.val).1
def leverage (U:Finset X)(p:brim D U→ℕ)(u:X)(s:X→ℝ)(d n:ℕ):= volume D U p s*(s (par D u)/s u)^d/s ⊥^n
def shortInk (U:Finset X)(p:brim D U→ℕ)(u:X)(s:X→ℝ)(d:ℕ):=area D p s (cove D U u)/s u^d
def tallInk (U:Finset X)(p:brim D U→ℕ)(u:X)(s:X→ℝ)(d n:ℕ):= s (par D u)^d*area D p s (univ\cove D U u)/s ⊥^n
variable (u)
local notation "C!"=> fun i=>leverage D U p₀ u (s i) d n
local notation "F!"=> fun i=> shortInk D U p₀ u (s i) d
local notation "R!"=>fun i=> tallInk D U p₀ u (s i) d n
lemma reloaded (d n:ℕ)(s:X→ℝ): leverage D U p₀ u s d n= shortInk D U p₀ u s d*tallInk D U p₀ u s d n := balance_units D (u:=u) p n (⟨d,0⟩: C.book.Token)
include hu Y
lemma atProfits : ∀ᶠ i in φ, 0<leverage D U p₀ u (s i) d n ∧ 0< F! i ∧ 0< R! i:=by
    have he:= Y.fresh 1 one_pos; have hh:= (rest_mem ..).1 hu; have hx:= he.crowned.roots (par_le D u) hh.2; filter_upwards [he.brim_paid D (picked V p),((time_bright D he).lit),area_pos D he p₀ (cove D U u),area_pos D he p₀ (univ \cove D U u)] with i hi ho hp ht
    have hu :0<s i ⊥:= ho.pos _ he.crowned.base; have hz:=ho.pos u hh.2; have hc:= ho.pos _ hx
    exact ⟨div_pos (mul_pos hi (pow_pos (div_pos hc hz) _)) (pow_pos hu _),div_pos hp (pow_pos hz _),div_pos (mul_pos (pow_pos hc d) ht) (pow_pos hu _)⟩
lemma earnsExp : ∀ᶠ i in φ,0 ≤ C! i∧ C! i ≤ Real.exp (((n:ℝ)+d)*r i):=by
    have he:= Y.fresh 1 one_pos; have hp: u∈U:=(rest_mem ..).1 hu|>.2; have hx:= he.crowned.roots (par_le D u) hp; have hh := he.fade _ he.crowned.base
    filter_upwards [(hh.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one),Y.fronts,time_bright D he|>.lit, weighing D (picked V p) Y n,atProfits (n:=n) (d:=d) D u p hu Y] with i hi hf hp' hw ht
    refine ⟨ht.1.le,?_⟩
    have hV : s i (par D u)/s i u ≤ (1:ℝ)/Real.exp (-r i):= div_le_div₀ (by norm_num) ((hp'.range' _ _ bot_le hx).trans hi) (Real.exp_pos _) (hf u hp)
    have hT : (s i (par D u)/s i u)^d ≤ Real.exp ((d:ℝ)*r i):=by rw [Real.exp_nat_mul]; apply pow_le_pow_left₀ (div_nonneg (hp'.pos _ hx).le (hp'.pos u hp).le); simpa only [Real.exp_neg,one_div,inv_inv] using hV
    unfold leverage; rw [show volume D U p₀ _*_ / (s i ⊥)^n=volume D U p₀ _/ ((s i ⊥)^n)* (s i (par D u)/s i u)^d from (by ring), add_mul,Real.exp_add]; exact mul_le_mul hw.2 hT (pow_nonneg (div_nonneg (hp'.pos _ hx).le (hp'.pos _ hp).le) _) (Real.exp_nonneg _)
-- absolute openness for all phases and given L. at real translation. survives bigger Ṁ
variable {η M c:ℝ} (x:X→E4)(z:I→J'→E4)
omit hu
include Y
lemma clear_scene [Fintype J'] (pQ:Crown F)(hp:F⊆ U) (hc:0 < c) (hz:∀ᶠ i in φ, ClearOf 0 (z i) c)(hη:0<η): ∀ᶠ i in φ,∀ x:X→E4,Ridge (s i) η M D U x→ Injective (beside (picked (brim D F) x) (z i)):=by
    have ht:= clear_shifted D z (Burst.heal D Y hp pQ) (M:=M) (row_root D (Burst.heal D Y hp pQ)) hc hz hη (⊥:X) (mem_union_left _ pQ.base); refine ht.mono fun i hi x hx=>?_; have he:= hi x (Ridge.heals D hp x hx)
    rw [hx.belly] at he; have hQ:away (x ∘ (Subtype.val:brim D F → X)) (0:E4)=picked (brim D F) x:=funext fun _=>sub_zero _; rw [hQ] at he; exact he
end YM.OPE.Arboreal.Trace
