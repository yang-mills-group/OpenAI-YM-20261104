import YM.Juniper.OrbitPrice.Course
/-!
 # Carry quantitative local E-budget through all UV steps and resets

 norm in local error contract one option: common `floor` in fixed Fitted and
 true heat budget. No restart required. Compare model phase input only with
 analogue actual K (and β). Persistent and stable even if Φ polydisk is not
 the Step's admissibility assumption; callers still owe their own local
 analytic estimates for this model/disk or a change-of-representation that
 suffices. Don't spatially regroup or replace labels without proving new
 estimates in this norm. Does NOT require output already along a path or any
 seam assumptions; exactly integrates all certified mix/critic inputs on a
 step including both their full K's & true gauges. Propagation to iteration
 & βPass estimate require small input piece and local E residual. No
 amplification of a fixed η loss even over unbounded cutoff range. See also
 A notes in PROGRESS.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
open UVExtension Function Filter Set Lattice Wilson RG Shoot Supply Pressure Precision
open Org PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open ThroughLaunch Roof Roost Input Progress.DirectedRecipe Time Camp Oriel
open Tabernacle Dales Guild Spire
open scoped Topology BigOperators InnerProductSpace Classical
variable {G : Gauge}
section math
variable (hG:G.Simple) (V:Levels G) (s:ℝ) (hs:0 ≤ s) (i : ℕ)
local notation "g"=> V.clock.hatCoupling
-- Choose r before schedule; all-order on supplied premises.
local notation "g₀"=> V.clock.hatCoupling i
local notation "g₁"=> V.clock.hatCoupling (i+1)
lemma sized_pos : 0<V.clock.hatCoupling i := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (V.fits.delayed _)))
lemma inverse_neat (W:ℝ)(s:ℝ)(h:0<s)(he: s ≤ W) : 0<W⁻¹ ∧ W⁻¹ ≤ s⁻¹:= ⟨inv_pos.mpr (h.trans_le he),inv_anti₀ h he⟩
lemma hats_fit : V.clock.hatCoupling i ≤ 1 := by
  let T:= V.clock.hatBeta i
  have ht : 1<T:= V.fits.delayed _
  have he : 1 ≤ Real.sqrt T:= (Real.sqrt_one|>.symm.trans_le (Real.sqrt_le_sqrt ht.le))
  exact le_trans ((inverse_neat _ _ one_pos he).2) (le_of_eq inv_one)
include hG
lemma sized_step : g₁ ≤ g₀ := by
  apply inv_anti₀ (Real.sqrt_pos.mpr (zero_lt_one.trans (V.fits.delayed i))) (Real.sqrt_le_sqrt ?_)
  change V.clock.bar+_*V.S.scale i ≤ V.clock.bar+_*V.S.scale (i+1); apply add_le_add_right; have he:= V.S.scale_succ i; apply mul_le_mul_of_nonneg_left _ (Gauge.slopeConstant_pos hG).le; exact (le_add_of_nonneg_right (logs_pos V i|>.le)).trans_eq he.symm
omit hG

def bill (R:ℝ) (i:ℕ) := V.clock.hatCoupling i ^ R
lemma bill_split (R:ℝ) (K:ℝ) : bill V R i = bill V (R-K) i * bill V K i := by
   unfold bill; rw [← Real.rpow_add (sized_pos V i)]; congr 1; ring
lemma bill_slack (R:ℝ): bill V R i=bill V (R-11/5) i * V.clock.allowance i := bill_split V i R (11/5)
include hG hs
lemma billed_le : bill V s (i+1) ≤ bill V s i := Real.rpow_le_rpow (sized_pos V _).le (sized_step hG V i) hs
omit hG hs
lemma worth_le : worth V i = bill V (4/25) i := by
  have hp:= (zero_lt_one.trans (V.fits.delayed i)).le
  unfold worth Yard.rake bill Calendar.hatCoupling
  rw [Real.inv_rpow (Real.sqrt_nonneg _), ← Real.rpow_neg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,← Real.rpow_mul hp]; norm_num
end math

variable {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) (hG:G.Simple)
    (S : Spire.Uses R hG) (N n : ℕ)(b:ℝ) (hb:(b:ℂ)∈ Camp.Broad A.B.a)
variable (m:ℕ) (hm:m ≤ N) (W Q U:ℝ)(α:ℕ→ℝ) -- W order with slack; Q local, U pulse
    (y: ∀ i:ℕ,(S.fits N n).Home i)
local notation "B" => A.B.a
local notation "q" => A.B.a.clock
local notation "θ" => A.B.a.budget
local notation "T"=> S.fits N n
local notation "Fn"=> S.cart N n
local notation "x!"=> genes R hG S N n b
local notation "d"=> fun i=> ‖trueE (x! i) - trueE (y i)‖
local notation "L"=> analyticPass R hG S N n b
local notation "P"=> pulsePass R hG S N n b
local notation "Δ"=> bill B (W-11/5)
local notation "ψ"=> S.realBeat b N n
/-- Input to one model purchase; separated so local producer can price
   only at j top and then one arbitrary step. ALL use same masks etc. These
   premises don't suffice for all-physical comparison or readout. Pulse target
   chosen BEFORE applying; there's no guarantee yet of knowing PT estimates
   to supply it. Not an inverse ordering assumption. -/
structure Boot : Prop where
  order : 11/5 ≤ W
  costs : 0 ≤ Q
  prices : (Tabernacle.floor (θ N) ((x! N-y N).val)).EBound (θ N) (Q*bill B W N)
  shell (i:ℕ) (hi:i<N) (hr:m ≤ i): ‖trueE (y (i+1))‖< rim
  wager (i:ℕ)(hi:i<N)(hq:m ≤ i): (Tabernacle.floor (θ i) (L i hi (y (i+1))- y i).val).EBound (θ i) (Q*bill B W i)

include hb
lemma carry (h: Boot R hG S N n b m W Q y) (i:ℕ)(hi:i ≤ N)(hv:m ≤ i) : let A':=Q/(1-soft)
    (Tabernacle.floor (θ i) (x! i-y i).val).EBound (θ i) (A'*bill B W i) ∧
    ∀ hn:i<N,
     let T':= L i hn (y (i+1)); let θ':= θ i
     let R':= Tabernacle.floor (θ i) (x! i - T').val
     R'.Valid θ' (soft*A'* Δ (i+1)*(q).allowance i) (soft*A'* Δ (i+1)*(q).forcedAllowance i) ∧
     |(ψ i|>.beta)-(ψ (i+1)|>.beta)- P i hn (y (i+1))| ≤ A'*bill B (W-11/5+4/25) (i+1):= by
  intro A'
  have hQ:= h.costs; have h₀:0 ≤ soft:=by norm_num [soft,rim]
  have hu:0<1-soft:=by norm_num [soft,rim]
  have ha:0 ≤ A':= div_nonneg hQ hu.le
  have hp (i:ℕ):0 ≤ Δ i:= Real.rpow_nonneg (sized_pos ..|>.le) _
  have hg(i:ℕ): Q*bill B W i= (Q* Δ i)*(q).allowance i:= by rw [bill_slack B]; ring -- rw i W capture
  have hx (i:ℕ)(hN:i ≤ N)(hh:m ≤ i): (d i) ≤ A'* Δ i := by
    induction hN using Nat.decreasingInduction with
    | self=>
       apply le_trans ((standard_le_emission (x! N) (y N) (Q*Δ N) (mul_nonneg hQ (hp N))).2 ((hg N) ▸ h.prices))
       exact mul_le_mul_of_nonneg_right (le_div_self hQ hu (by norm_num [soft,rim])) (hp N)
    | of_succ i hi ih=>
       let E:= L i hi (y (i+1)); let J:= x! i
       have he := (native R hG S N n b hb y i hi (h.shell i hi hh)).1
       have hU := ih (hh.trans (Nat.le_succ _))
       have hL: ‖trueE J - trueE E‖ ≤ soft * (d (i+1)) := le_trans (le_max_left (‖trueE J-trueE E‖) (‖trueK J-trueK E‖)) ((total_split J E).symm.trans_le he)
       have hY := (standard_le_emission E (y i) _ (mul_nonneg hQ (hp i))).2 ((hg i) ▸ h.wager i hi hh)
       have hh' := (norm_sub_le_norm_sub_add_norm_sub (trueE J) (trueE E) (trueE (y i)))
       refine le_trans (hh'.trans (add_le_add hL hY)) ?_
       have ht : Q=(1-soft)*A':= Eq.symm (mul_div_cancel₀ Q (show (1-soft)≠0 from hu.ne')) -- order
       calc
        _ ≤ soft*(A'* Δ (i+1)) + Q* Δ i:= add_le_add (mul_le_mul_of_nonneg_left hU h₀) le_rfl
        _ ≤ soft*(A'* Δ i)+Q* Δ i:=add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (billed_le hG B (W-11/5) (sub_nonneg.mpr h.order) i) ha) h₀) le_rfl
        _ = _ := by nth_rw 1 [ht]; ring
  refine ⟨?_,fun hn=>?_⟩
  · rw [bill_slack B i W, ← mul_assoc]; exact (standard_le_emission (x! i) (y i) _ (mul_nonneg ha (hp i))).1 (hx i hi hv)
  let E:= x! i; let H:=L i hn (y (i+1)); intro T' θ' R'
  have hD:= native R hG S N n b hb y i hn (h.shell i hn hv)
  constructor
  · have he := hD.1
    dsimp only [R']
    -- NOTE mass ∅ 0? B.mass multiplies b by exp left? check
    refine (pay_total (E-H) (soft*A'* Δ (i+1))).1 ?_; rw [map_sub]
    apply he.trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hx _ hn (hv.trans (Nat.le_succ _))) h₀
  apply hD.2.1.trans
  rw [worth_le B, bill_split B (i+1) (W-11/5+4/25) (4/25),add_sub_cancel_right]
  exact (mul_le_mul_of_nonneg_left (hx _ hn (hv.trans (Nat.le_succ _))) (by rw [← worth_le]; exact (worth_pos B (i+1)).le)).trans_eq (by ring)

-- Reset loss exported; extra 3 levels of truncation a sufficient reserve if one
-- has those estimates (also applying θ comparison assumptions). Interpret alpha only
-- as evaluation of a specified finite PT increment prediction after supplying
-- its analytic defect, and don't retune on β' at each level! Estimate relative
-- to actual inherited β with a slightly larger slack (51/25=2.04).
lemma reset (h:Boot R hG S N n b m W Q y)
    (hz : ∀ i : ℕ,∀ hi:i<N,m ≤ i → |P i hi (y (i+1))-α i| ≤ U*bill B (W-11/5+4/25) (i+1)) :
    ∀ i<N,m ≤ i→ |(ψ i|>.beta)-(ψ (i+1)|>.beta)-α i| ≤ (Q/(1-soft)+U)* bill B (W-11/5+4/25) (i+1):= by
  intro i hi hm; rw [show (ψ i|>.beta)-(ψ (i+1)|>.beta)-α i=_ from ?_, add_mul]
  · apply le_trans (abs_add_le ..); exact add_le_add (((carry R hG S N n b hb m W Q y h i hi.le hm).2 hi).2) (hz i hi hm)
  exact Eq.symm (show (ψ i|>.beta)-(ψ (i+1)|>.beta)-P i hi (y (i+1))+(P i hi (y (i+1))-α i) = _ by ring)
end YM.Juniper.Native
