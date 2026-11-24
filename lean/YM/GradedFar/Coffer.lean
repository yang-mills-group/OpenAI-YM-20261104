import YM.GradedFar.GaugeBook
/-!
# PoseFit's required C5 sale on r-homes and mounted Cash matrix

Bundles the actual hypotheses retained for W in proving H expansion. This isn't Bake at a smaller period.
Use actual θ = g and trial hypotheses of (C5) in `Pose`, e.g., θ-r price uniform on Mesh-grid &
t'ℓ from that common installation. `V` one map on those h slots even when comparing multiple fields;
only require estimates at that `h`. Note p in `Pose` or `Portal` denotes requested fixed power; exercise
C5 & F.3 with large enough M,Q_*, on those same operands. It does not require having already-coherent
choices across `p`, `k`, `W` file etc. H frames & t have to be committed globally before these.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
namespace Playbill
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open Fork (Sold Safe)
open Tickets
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(P J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Adj" => Scale.Measure.adjust (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n m h p q:ℕ}
local notation "V" => Sec G h
variable {X I : Type*} (u:Filter X) (W:X→I→Prop) (B:X→I→ℝ) (r:X→ℝ) (z:X→I→Points n)(t:ℝ→ℝ)
local notation "g∴" => strength G

-- C5P specific operands. placement arguments in r units (covers either fixed compact or moving grid).
-- unweighted norms suffice. precision negotiable: use suppliers at M>=p+10 to get these estimates.
-- weakened from `fixed-size job` when necessary because may take finite union basis. use only value n h.
-- requirement to re-use same evaluated clock and Cash for the evaluated comparison; assignment at each
-- installation, estimator/mesh prior hypotheses not being silently asserted for a different regulator.
structure Chosen (h p q:ℕ)(τ:X→ℝ)(D:X→Sec G h→ₗ[ℂ] Sec G h):Prop where
    purchases : p ≤ q
    zero : Tendsto τ u (𝓝 0)
    time : ∃ b:ℝ,0 ≤ b ∧ ∀ᶠ x in u, |τ x - t (r x)| ≤ b*g∴ (r x)^(p+1)
    entry (v:Sec G h) (a:Toon G h): ∃ b:ℝ,0 ≤ b ∧ ∀ᶠ x in u,
        ‖coord a (D x v)-coord a v‖ ≤ b*g∴ (r x)^(p+1)
    comparisons (v:ListInput G n h):∃ b:ℝ,0≤b ∧ ∀ᶠ x in u, ∀ i, W x i →
      ‖frank F J none h (r x) (z x i) v - appointedH140Crop q (τ x) (sent Before h (z x i) (fun j=>D x (v j)))‖ ≤ b*g∴ (r x)^(p+1)
-- J = W in use of Chosen. Actually needs `(Z)` and `n` implicit. `P` later H. Make quant.

def Portal (h p:ℕ) := ∃ (q:ℕ) (τ:X→ℝ) (D:X→Sec G h→ₗ[ℂ] Sec G h), Chosen F J Z u W r z t h p q τ D

variable {J Z u W B r z t}
variable {τ:X→ℝ} {D:X→Sec G h→ₗ[ℂ] Sec G h}
variable (hr:Tendsto r u trail) (ht:Coupling G t) (A:Safe u W B (fun _ _=>1))
local notation "t₁"=> t ∘ r
local notation "T₁"=> WithTax p u W B t₁

-- generic t/g repayment
include hr ht hG in
lemma closer (k:ℕ): ∀ᶠ x in u, g∴ (r x)^k ≤ 2^k*|t₁ x|^k:=by
    have hv:∀ᶠ a in trail, g∴ a ≤ 2*|t a|:= by
       filter_upwards [(ratio_clock hG ht).eventually_const_lt (by norm_num:(1/2:ℝ)<1),strength_positive hG] with x ht he;
       linarith [(lt_div_iff₀ he).1 ht, le_abs_self (t x)]
    filter_upwards [hr.eventually hv, hr.eventually (strength_positive hG)] with x hx h; rw [← mul_pow]; exact
      pow_le_pow_left₀ h.le hx _
include hr ht A hG in
lemma change_coins : Coins u W B t₁ := ⟨A,(Coupling.conforms hG ht).comp hr⟩
include hr ht A hG in
set_option linter.unusedSectionVars false in
lemma trading {p:X→I→ℂ} {k:ℕ} (H:∃ b:ℝ,0≤b ∧ ∀ᶠ x in u,∀ i,W x i → ‖p x i‖ ≤ b*g∴ (r x)^k):
    Sold u W B (fun x _=> |t₁ x|^k) p:=by
    obtain ⟨b,hb,H⟩:= H; refine Fork.Sold.bounded (show 0≤b*2^k from by positivity) ?_; filter_upwards [closer hr ht k (hG:=hG),H] with x h hx i hi
    exact (hx i hi).trans ((mul_le_mul_of_nonneg_left h hb).trans_eq (mul_assoc ..).symm)

include hr ht A hG
private lemma Chosen.field (H:Chosen F J Z u W r z t h p q τ D)(v: V)(a: Toon G h):
    T₁ (fun x _=> coord a (D x v)) (fun _ _=> PowerSeries.C (coord a v)):= by
    refine WithTax.correct (change_coins hr ht A (hG:=hG)) (WithTax.constant _) ?_; obtain ⟨b,hb,hv⟩:= H.entry v a
    exact trading hr ht A (hG:=hG) ⟨b,hb,hv.mono fun x hx i _=>hx⟩
private lemma Chosen.crop_value (H:Chosen F J Z u W r z t h p q τ D)(H':∀ v:ListInput G n h,Prospects u W B
    (fun i j=> sent Before h (z i j) v))(v:ListInput G n h): T₁ (fun x i=> appointedH140Crop q (τ x) (sent Before h (z x i) v))
      (fun x i=> sent Before h (z x i) v):= by
    apply WithTax.switch (change_coins hr ht A (hG:=hG)) τ H.zero _ H.purchases (H' v)
    obtain ⟨b,hb,h⟩:= H.time; apply trading hr ht A (hG:=hG); refine ⟨b,hb,h.mono (fun i hi j _=> ?_)⟩; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hi

variable (Z)
include H
-- derive actual C5 use version asserting the W *pre* expansion in t itself. exactly all h, all rows ballot receipts at same K.
lemma paidW (hp:Portal F J Z u W r z t h p)(hZ:∀ v:ListInput G n h, Prospects u W B
    (fun i j=> sent Post h (z i j) v))(v:ListInput G n h): T₁ (fun x i=> frank F J none h (r x) (z x i) v)
      (fun x i=> sent Before h (z x i) v):=by
    obtain ⟨q,τ,D,hhP⟩:= hp; let k:= change_coins hr ht A (hG:=hG); let D' x : ListInput G n h:=fun i=> D x (v i)
    refine WithTax.correct k (f:=fun x i=> appointedH140Crop q (τ x) (sent Before h (z x i) (D' x))) ?_ (trading hr ht A (hG:=hG) (hhP.comparisons v))
    have hh (i:Picks G (Ceiling n h)): T₁ (fun x _=> multipliers (D' x) i)
         (fun _ _=> PowerSeries.C (multipliers v i)):= by unfold multipliers; simp_rw [map_prod]; exact WithTax.product k _ (fun _ _=> Chosen.field F hr ht A (hG:=hG) hhP _ _)
    obtain H':= start_price Z M H (h:=h) k z hZ
    simp_rw [crop_as_is (D' _), as_is v]; exact WithTax.sum k _ fun i _=> (hh i).mul k (Chosen.crop_value F hr ht A (hG:=hG) hhP H' _)
-- P actual normalized H. derive charged coordinate expansions next.
end Playbill
end YM.Integration.GradedFar.Tariff
