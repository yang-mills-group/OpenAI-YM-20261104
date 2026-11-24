import YM.LocalLTE.Pond.Owners
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
open Time Urns
section numbers
variable (G) (p:RG.Stage)(L:Side)
variable {F:ℝ→ℕ} {s W N α Δ c:ℝ}
-- `hurt` exponent shock. Numeric purser. ROI multipliers
local notation "H$"=> Time.credit G p
local notation "δ₀"=> (Time.probe p)
def Penny (M:ℕ)(a b:ℝ)(p:RG.Stage)(G:Gauge): Prop :=
    0<a∧0<b∧ 2*a ≤ Time.credit G p ∧ 8*(1+Price.tH (Time.probe p))*(1+Time.base G p)*a ≤ b ∧ turnFee (Time.probe p)* (M+2:ℕ)*(2*b) ≤ (1/32:ℝ)
lemma earn (M:ℕ):∃ a b:ℝ,Penny M a b p G:=by
    have ht:= credit_pos G p; let T:=turnFee (Time.probe p); have he:0<T:=turnFee_pos _
    let C:=8*(1+Price.tH (Time.probe p))*(1+Time.base G p)
    have hp:= (Time.base_nonneg G p).1; have hv:0<Price.tH (Time.probe p):= Real.exp_pos _; have hC:0<C:=by unfold C; positivity
    let d:= 2*(T*(M+2:ℕ)); have hd:0<d:= by unfold d; positivity
    let b:= (1/32:ℝ)/d; have hb:0<b:=div_pos (by norm_num) hd
    let a:= min (b/C) (Time.credit G p /2)
    refine ⟨a,b,lt_min (div_pos hb hC) (half_pos ht),hb,?_,?_,?_⟩
    · exact (le_of_eq (mul_comm 2 a)).trans ((le_div_iff₀ (show 0<(2:ℝ) by norm_num)).1 (min_le_right ..))
    · exact (le_of_eq (mul_comm C a)).trans ((le_div_iff₀ hC).1 (min_le_left ..))
    have hz:= div_mul_cancel₀ (1/32:ℝ) hd.ne'; linarith only [show b*(2*(T*(M+2:ℕ)))=1/32 from hz]

section
variable {a b:ℝ}
lemma validS {q : BudgetPoint} (h: Time.Same p q) : let c:=p.clip; let s:=p.width; let C:=p.paths
    turnFee q=turnFee (Time.probe p) ∧ Price.tH q=Price.tH (Time.probe p) ∧ lowBase G c q s C=lowBase G c (Time.probe p) s C∧ highBase G q s C=highBase G (Time.probe p) s C ∧resetFee G q=resetFee G (Time.probe p):= by
    intro c s C; unfold tH resetFee resetLoss multiplier turnFee lowBase highBase anchoredFee lowFee Geo.both lowCost rowCost faceCost highFee Time.probe rowDegree pairBill; dsimp; rw [h.1,h.2.1,h.2.2]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma cloud (t:ℝ) (ht:0<t) : (betaF G t L)^(chip 0) ≤ δE t:= by
    have hz : t≤ betaF G t L := le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
    rw [Coup.chip_zero, ← Coup.e_now L t (ht.trans_le hz)]; unfold incomingE; change _≤ (Real.sqrt t)⁻¹ ^ ((11:ℝ)/5); exact Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_le_sqrt hz)) (by norm_num)
lemma chi (m:ℕ)(h:Penny m a b p G){t:ℝ}(ht:0<t)(P:BudgetPoint)(he:Time.Same p P):
    let β:= betaF G t L; Price.bars P m (2*b) β ≤ β^(chip 0) ∧ Price.bars P m (2*b) β ≤ δE t/32∧2*a*β^(chip 0) ≤ H$*δE t := by
    intro β; have hv:0≤β^(chip 0):=Real.rpow_nonneg (ht.trans_le (le_add_of_nonneg_right (Work.E04.shift_nonneg ..))).le _
    obtain ⟨h,hb,hB,ht',hV⟩:=h
    have hp:= validS G p he; unfold bars; rw [hp.1]; have hh:= cloud G L t ht
    refine ⟨?_,?_, mul_le_mul hB hh hv (credit_pos G p|>.le)⟩
    · linarith only [mul_le_mul_of_nonneg_right hV hv,hv]
    linarith only [mul_le_mul_of_nonneg_right hV hv, hh] -- edit
variable (Q:ℝ) (m:ℕ) (h:Penny m a b p G)
-- knock.Income extras.softNeed.
variable {K:Gauge}
lemma solvable (P:BudgetPoint) (H: ℝ) (h:0 ≤ H):H ≤ softReset G P H:= by
    have hx:= P.exponent_pos
    unfold softReset Footprint.payment Footprint.degreeIncome
    have hb : 1 ≤ resetLoss G P:= le_trans (show (1:ℝ) ≤ 2 by norm_num) (le_add_of_nonneg_right (multiplier_nonneg ..))
    have ht: (1 :ℝ) ≤ (Footprint.spread 1 (4*P.B+2)):=(Nat.one_le_cast.mpr ?_); swap
    · unfold Footprint.spread ballCost; apply Nat.one_le_iff_ne_zero.mpr; positivity -- edit
    have hv:1 ≤ (1-Real.exp (-(1:ℝ)))⁻¹:= (one_le_inv₀ (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).mpr (sub_le_self _ (Real.exp_nonneg _))
    calc
       H ≤ Real.exp ((P.supportExponent+1)*81)* resetLoss G P * ↑(Footprint.spread 1 (4*P.B+2)) * ((1:ℝ)⁻¹^(4:ℕ)*(↑(4:ℕ).factorial)*Real.exp 1) * (1-Real.exp (-1))⁻¹ * H := by
          apply le_mul_of_one_le_left h
          have hz:1 ≤ (1:ℝ)⁻¹^(4:ℕ)*(↑(4:ℕ).factorial) :=by norm_num [Nat.factorial]
          exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hb) ht) (one_le_mul_of_one_le_of_one_le hz (Real.one_le_exp zero_le_one))) hv
       _=_ := by ring_nf -- edit
lemma risk (P:BudgetPoint)(p':Stage){α H x:ℝ}(hx:x ≤ H): softNeed G P p'.clip p'.width p'.paths α x + (H-x) ≤ softNeed G P p'.clip p'.width p'.paths α H:=by
    have hp : softReset G P x + (H-x) ≤ softReset G P H:=by
       refine (add_le_add_right (Price.solvable G P (H-x) (sub_nonneg.mpr hx)) _).trans_eq (?_); unfold softReset Footprint.payment Footprint.degreeIncome; ring
    have ht:=P.threshold_pos; have hh:=pair_nonneg G P; have hu: hitNeed P G α x ≤ hitNeed P G α H:= by unfold hitNeed; gcongr
    unfold softNeed; linarith only [hp, mul_le_mul_of_nonneg_right hu (budget_pos _ G _ p'.width_pos p'.paths_pos.le|>.2.2 : 0 ≤ lowHard P p'.clip p'.width p'.paths)] -- edit unfold
end
end numbers
end YM.AnalyticBridge.VerifiedReset.Collection.Price
