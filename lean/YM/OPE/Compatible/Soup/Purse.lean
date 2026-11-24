import YM.OPE.Compatible.Soup.Lunge
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Jargon Metric
section
variable {D}
-- exact unit-station ball lower
local notation "W!"=>Merchant.Chamber G r
abbrev onH (G:Gauge) (r:ℕ):= Chart.tangent G (fieldP r)
noncomputable abbrev ShoreP (D:I→ Law (Merchant.Chamber G r)) (i:I):= quart (D i) (onH G r)
variable {x:I→ℝ}
include hD
lemma D_Grain (h:Tendsto β φ atTop): Grain (ShoreP D) φ (Counters β) (fun _ p=>‖p‖) 0:=by
       intro i hi; let z:= hail (E:=W!) (Fract S r) i; refine ⟨_,RateLE.const z (carth h),Eventually.of_forall fun j=>?_⟩; exact Aloof.halo (D j) _ (hD.rate j) (Fractage ..) hi
lemma D_tail (h:Tendsto β φ atTop)(hp:Wick β φ (fun i=>Real.exp (-x i)))(hx:∀ᶠ i in φ,0 ≤ x i): Wick β φ (fun i=> (ShoreP D i).real {z:Merchant.Chamber G r|maxion (Merchant.Chamber G r)*x i<‖z‖}):=by
       intro a; let f:=Γθ (E:=W!) (Fract S r); have hh:Wax β φ (fun i=> f*Real.exp (-x i)) a:=(by simpa only [zero_add] using! (RateLE.const f (carth h)).mul (hp a)); apply RateLE.of_norm_le hh; filter_upwards [hx] with i hi; rw[Real.norm_of_nonneg measureReal_nonneg]; exact gale (D i) _ (hD.rate i) (Fractage ..) hi
include hs
omit hs hD in
private lemma lifted_habit (j:I)(y:Merchant.Chamber G r) : SerT (Stair A U j y) (WorkB A j) := by
  exact SerT.raise (sparse_s G (Punched A U j) y) (broader A U j)

omit hs hD in
private lemma lifted_inside (j:I)(y:Merchant.Chamber G r){z:ℝ}(hy:y∈ball (0:Merchant.Chamber G r) z) :
    ‖Stair A U j y‖<z := by
  have paid:=money_s G (Punched A U j) y
  have fee:‖Stair A U j y‖≤‖y‖:=by unfold Stair; match_account_types paid
  exact fee.trans_lt (mem_ball_zero_iff.mp hy)

omit hD in
private lemma lifted_cost {f g:I→ℝ} (H:MintL (A:=A) (φ:=φ) f g)(j:I)(y:Merchant.Chamber G r){z:ℝ}
    (hy:y∈ball (0:Merchant.Chamber G r) z) :
    ‖jet (KPole A j) 2 (Stair A U j y)‖≤z^2*f j := by
  have he:=lifted_inside (A:=A) (U:=U) j y hy
  have hh:=lifted_habit (A:=A) (U:=U) j y
  have hP:Past (KPole A j) (Stair A U j y) 5 z (f j):=(H.ν j _ hh z he).1
  have sm:ContDiffAt ℝ ω (KPole A j) 0:=(Variance.DuneAt _ hs).sm
  exact Pat_charge (i:=2) sm hP two_pos (by decide) ((norm_nonneg _).trans he.le) (H.fare j).1

omit hs in
private lemma local_quadratic (j:I)(y:Merchant.Chamber G r) :
    (D j).P y y=2*jet (KPole A j) 2 (Stair A U j y) := by
  have eqn:=(hD.obey j).sat _ _ _ y y
  exact eqn.symm.trans (chrom2 ..)

private lemma dCost {f g:I→ℝ} (H:MintL (A:=A) (φ:=φ) f g)(j:I)(y:Merchant.Chamber G r){z:ℝ}
    (hy:y∈ball (0:Merchant.Chamber G r) z)(hx:z^2*f j ≤ 1):(D j).P y y ≤ 2*(1:ℝ):=by
  rw [local_quadratic hD j y]
  exact mul_le_mul_of_nonneg_left
    ((Real.le_norm_self _).trans ((lifted_cost (U:=U) hs H j y hy).trans hx)) zero_le_two
include h
lemma D_purses : Receipt β φ (fun i=> (rentF (D i) (onH G r))⁻¹):=by
        obtain ⟨f,g,H⟩:=merit A h; let K(i:I):=f i+1; let x(i:I):=(K i)⁻¹; have hx(j:I):1 ≤ K j:=le_add_of_nonneg_left (H.fare j).1; have hp(j:I):0 < x j:=inv_pos.mpr (zero_lt_one.trans_le (hx _)); let μ:=onH G r; let v₀ := μ.real (ball (0:W!) 1); let dK:= Module.finrank ℝ (Merchant.Chamber G r); let z(j:I):= (x j)^dK*v₀*Real.exp (-1); have ht(j:I):∀ y∈ball (0:Merchant.Chamber G r) (x j),(D j).P y y ≤ 2*(1:ℝ):=fun y hx=> dCost hs hD H j y hx (by have hz:=H.fare j; have hv: x j≤ 1:= inv_le_one_of_one_le₀ (show 1 ≤ K j from le_add_of_nonneg_left hz.1); calc
                    _ ≤ x j * K j:=mul_le_mul (by nlinarith only[hv, hp j]) ((lt_add_one _).le) (H.fare j).1 (hp j|>.le)
                    _ = _:=inv_mul_cancel₀ (zero_lt_one.trans_le (show 1 ≤ K j from le_add_of_nonneg_left hz.1)).ne')
        have hY : 0 < v₀:=ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr zero_lt_one)).ne' measure_ball_lt_top.ne; have hk: Receipt β φ K:= H.meat.plus (YM.OPE.Score.steady _ (carth h)) (carth h); have hK: Receipt β φ (fun i=> (z i)⁻¹):= by
            have ht:= (hk.power dK (carth h)).product (YM.OPE.Score.steady ((v₀)⁻¹*(Real.exp (-1))⁻¹) (carth h)); apply ht.congr; filter_upwards with i; dsimp only [z,x]; rw [_root_.mul_inv,_root_.mul_inv, ← inv_pow,inv_inv,mul_assoc]
        apply hK.pointwise _ (Eventually.of_forall fun i=> inv_nonneg.mpr (spent (onH G r) (D i)|>.le)); exact Eventually.of_forall fun i=> inv_anti₀ (show 0<z i from mul_pos (mul_pos (pow_pos (hp i) _) hY) (Real.exp_pos _)) (ballE (D i) _ (hp i) (ht i))
end
end YM.OPE.Owl.HillZ
