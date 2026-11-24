import YM.Integration.WilsonEmittedSparseRows

/-! The actual support strip can be strengthened before taking the long
tail. Its paid wallet changes by at most a fixed factor, even if its
previous spare strip was very small. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedLengthWindow
open Function Finset Lattice RG Wilson QuadraticLocal QuadraticLocal.Earn
open Push.AbsoluteSums Filter
open scoped BigOperators
def strip (θ σ:ℝ) := max θ (min 1 (σ/4))

theorem opened {B:BudgetPoint} {K a g σ θ:ℝ}
    (paid:Invoice.Supports B K a g σ θ) (placed:a*(B.B:ℝ)⁻¹ ≤ σ/2) :
    Invoice.Supports B K a g σ (strip θ σ) := by
  obtain ⟨hg,w,hK,ht,hσ,ha,he,hwidth⟩:=paid
  refine ⟨hg,w,hK,ht,hσ,ha,he.trans_le (le_max_left ..),?_⟩
  unfold strip
  rcases le_total θ (min 1 (σ/4)) with h|h
  · rw [max_eq_right h]
    linarith [min_le_right (1:ℝ) (σ/4)]
  · rw [max_eq_left h]
    exact hwidth

theorem rebilled (P W k:ℕ) {θ σ C t a v:ℝ}
    (pos:0<θ) (cpos:0 ≤ C) (bpos:0 ≤ t) :
    Footprint.payment P W k (strip θ σ) C t a v ≤
      Real.exp 1 * Footprint.payment P W k θ C t a v := by
  let ζ:=strip θ σ
  have widen:θ≤ζ:=le_max_left .. 
  have zpos:0<ζ:=pos.trans_le widen
  have ei:ζ⁻¹ ≤ θ⁻¹:=inv_anti₀ pos widen
  have ew:(ζ⁻¹)^(4+k) ≤ (θ⁻¹)^(4+k):=pow_le_pow_left₀ (inv_nonneg.mpr zpos.le) ei _
  have ez:ζ≤1+θ:=max_le (by linarith) ((min_le_left ..).trans (by linarith))
  have lift:Real.exp ζ ≤ Real.exp θ * Real.exp 1:=by rw [←Real.exp_add];exact Real.exp_le_exp.mpr (by linarith)
  have h1:0<1-Real.exp (-θ):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr pos))
  have hz:(1-Real.exp (-ζ))⁻¹≤(1-Real.exp (-θ))⁻¹:=
    inv_anti₀ h1 (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg widen)) _)
  set d:ℝ:=Real.exp (a*v)*t*C*Footprint.spread P W
  have dn:0 ≤ d:=by unfold d; positivity
  have hp:0 ≤ (4+k).factorial*(Real.exp ζ):=by positivity
  change d*((ζ⁻¹)^(4+k)*((4+k).factorial:ℝ)*Real.exp ζ)*(1-Real.exp (-ζ))⁻¹≤_
  apply (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right ew (Nat.cast_nonneg _))
    lift (Real.exp_nonneg _) (mul_nonneg (pow_nonneg (inv_nonneg.mpr pos.le) _) (Nat.cast_nonneg _))) dn)
    hz (inv_nonneg.mpr (h1.le.trans (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg widen)) _))) (by positivity)).trans
  unfold Footprint.payment Footprint.degreeIncome
  dsimp [d]
  linarith only []

theorem decays {B:BudgetPoint} {K a g σ θ x:ℝ} (paid:Invoice.Supports B K a g σ θ)
    (sized:B.B=Nat.ceil ((Real.log x)^2)) (reserve:Real.exp ((σ⁻¹)^2)≤x)
    (bounded:a≤102) (r:ℕ) (late:(256*((r:ℝ)+1))^2 ≤ Real.log x) :
    Invoice.Supports B K a g σ (strip θ σ) ∧
    Real.exp (-(strip θ σ))^(B.B/32) ≤ (x^r)⁻¹ := by
  let s:=Real.sqrt (Real.log x)
  have lx:0 ≤ Real.log x:= (sq_nonneg (256*((r:ℝ)+1))).trans late
  have ss:s^2=Real.log x:=Real.sq_sqrt lx
  have order:256*((r:ℝ)+1)≤ s:=by exact (Real.le_sqrt (by positivity) lx).mpr late
  have ls:256 ≤ s:=by linarith [show (0:ℝ)≤r by positivity]
  have sp:0<s:=by linarith
  have D:(Real.log x)^2 ≤ (B.B:ℝ):=sized ▸ Nat.le_ceil _
  have gr:0<σ:= by
    have h:=paid.2.2.2.2.2
    linarith [mul_nonneg h.1 (inv_nonneg.mpr (Nat.cast_nonneg B.B)),h.2.1,h.2.2]
  have x0:0<x:=(Real.exp_pos _).trans_le reserve
  have hs:(σ⁻¹)^2≤Real.log x:= by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) reserve
  have invs:σ⁻¹≤ s:=(Real.le_sqrt (inv_nonneg.mpr gr.le) lx).mpr hs
  have under:s⁻¹≤σ:=by simpa only [inv_inv] using (inv_anti₀ (inv_pos.mpr gr) invs)
  have s1:1≤ s:=by linarith
  have lb:s*s≤(Real.log x)^2:=by
    rw [←ss]
    nlinarith [pow_le_pow_right₀ s1 (show 2≤4 by decide),pow_mul s 2 2]
  have Bs: 204*s ≤ (B.B:ℝ):= (by nlinarith only [mul_nonneg (show 0≤ s-204 by linarith) sp.le] : 204*s≤ s*s).trans (lb.trans D)
  have B0:0<(B.B:ℝ):=by nlinarith
  have room:a*(B.B:ℝ)⁻¹≤σ/2:=by
    apply le_trans _ (div_le_div_of_nonneg_right under (by norm_num))
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ B0).mpr
    field_simp [sp.ne']
    nlinarith [mul_le_mul_of_nonneg_right bounded sp.le]
  have raw : s⁻¹/4 ≤ strip θ σ := by
    apply le_trans _ (le_max_right ..)
    apply le_min _ (div_le_div_of_nonneg_right under (by norm_num))
    have h:s⁻¹≤1:=inv_le_one_of_one_le₀ s1
    linarith
  have Bbig : 64≤B.B:=by exact_mod_cast (show (64:ℝ)≤B.B by nlinarith)
  have Bm : B.B≤64*(B.B/32):=by omega
  have cash : (r:ℝ)*Real.log x ≤ strip θ σ*(B.B/32:ℕ):=by
    apply le_trans _ (mul_le_mul_of_nonneg_right raw (Nat.cast_nonneg _))
    have prod: (Real.log x)^2≤64*(B.B/32:ℕ):=D.trans (by exact_mod_cast Bm)
    have rate:256*(r:ℝ)*s ≤ Real.log x:=by
      rw [←ss];nlinarith [mul_nonneg (show 0≤ s-256*r by linarith) sp.le]
    have z:=mul_le_mul_of_nonneg_right rate lx
    field_simp [sp.ne']
    nlinarith
  refine ⟨opened paid room,?_⟩
  calc
    _ = Real.exp (-(strip θ σ*(B.B/32:ℕ))) := by rw [←Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-((r:ℝ)*Real.log x)) := Real.exp_le_exp.mpr (neg_le_neg cash)
    _ = (x^r)⁻¹ := by rw [Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos x0 _)]

end YM.Integration.WilsonEmittedLengthWindow
end
