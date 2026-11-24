import YM.RG04B.Envelope
import YM.RG04B.Start.Catalog

/-!
# Sufficient actual-stage gates for startup at all orders

Booked once with arbitrary other post-demand gates. No need to alter
estimates in the established vacuum construction. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open RG Lattice Wilson Function Filter Real
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G}

-- threshold comparisons usable even on larger spans as long as beta band is shared
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "S" => C.path.levels.params
local notation "F" => C.path.levels.clock
local notation "X" => C.path.rep

lemma ratioHat (h : C.Makes) {N p m : ℕ} (hx : m ≤ N) : (F).hatCoupling m ≤ 2*gAt C N p m ∧
    gAt C N p m ≤ 2*(F).hatCoupling m := by
  obtain ⟨hf,hb⟩:= inBand h N p m hx
  let x := sqrt ((F).hatBeta m)
  let y := sqrt ((X N p m).beta)
  have hz :0<(F).hatBeta m:= zero_lt_one.trans (P|>.fits.delayed _)
  have hX:0<x:=sqrt_pos.mpr hz; have hY:0<y:=sqrt_pos.mpr (beta_positive h _ _ _ hx)
  have hg:y^2= (X N p m).beta := Real.sq_sqrt (beta_positive h _ _ _ hx).le
  have he : x^2=(F).hatBeta m:= Real.sq_sqrt hz.le
  change _ ≤ (X N p m).beta at hf; change (X N p m).beta ≤ _ at hb
  have h₁:x≤ 2*y := by rw [← he, ← hg] at hf; nlinarith
  have h₂:y≤2*x:= by rw [←he,←hg] at hb; nlinarith
  change x⁻¹ ≤ 2*y⁻¹ ∧ y⁻¹ ≤ 2*x⁻¹
  rw [← div_eq_mul_inv,← div_eq_mul_inv,← one_div,← one_div,div_le_div_iff₀ hX hY,div_le_div_iff₀ hY hX]
  simpa only [one_mul] using And.intro h₂ h₁

lemma thresholdHat (h : C.Makes) {N p m : ℕ} (hx : m≤N) :
    let t := ((C.path.levels).budget m).threshold -- notation needs braces
    let g := gAt C N p m
    t ≤ g*(2*(F).monitor m) ∧ g ≤ 2*t := by
  obtain ⟨hf,hb⟩:=ratioHat h (p:=p) hx
  intro t g
  have hm : 1 ≤ (F).monitor m:= Real.one_le_exp (sq_nonneg _)
  exact ⟨(mul_le_mul_of_nonneg_right hf (zero_le_one.trans hm)).trans_eq (by change 2*g*_=_; ring),
    hb.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) hm) zero_le_two)⟩

namespace Startup

private def startupFee (G : Gauge) : Fees where
  first := fun _ W e m =>
    let s := W m
    |offered G e s.order s.power|+(required G e s.order s.power)⁻¹ +
      Real.exp (s.supportExponent * 5^4)
  paid := fun _ _ _ _ _ _ => 0

/-- Joint extra request (include also Fees T for remaining producers). -/
def temperatures (G : Gauge) := (startupFee G).reserve

private lemma tail_prices (hG:G.Simple) (h : Booked (temperatures G) P) (e : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      offered G e (S m).order (S m).power ≤ geo P m ∧
      ((required G e (S m).order (S m).power)⁻¹ ≤ geo P m ∧
      WilsonStartup.Start.overhead ((C.path.levels).budget m) ≤ geo P m) := by
  let s : ℕ→Stage:= S
  have hs: stripe (startupFee G) P := h
  obtain ⟨n,H⟩:= eventually_atTop.1 (common hs e (ε:=1) (by norm_num))
  filter_upwards [eventually_ge_atTop (n+1)] with m hm
  cases m with
  | zero=> omega
  | succ k=>
    have He:= H k (by omega) |>.1
    rw [Real.rpow_one] at He
    have hk: firstBill (startupFee G) P e k ≤ geo P (k+1) :=
      He.trans ((limitRatio hs k).trans (monotone_geo P hG (Nat.le_succ _)))
    let A:=offered G e (S (k+1)).order (S (k+1)).power
    let B:=(required G e (S (k+1)).order (S (k+1)).power)⁻¹
    let V:=WilsonStartup.Start.overhead ((C.path.levels).budget (k+1))
    have hA:0<A:= offered0 ..; have hB:0<B:= inv_pos.2 (required0 ..); have hV:0<V:= Real.exp_pos _
    change 2+abs (|A|+B+V) ≤ _ at hk
    rw [abs_of_pos (by positivity : 0< abs A+B+V),abs_of_pos hA] at hk
    change A≤_ ∧ B≤_ ∧ V≤_
    refine ⟨?_,?_,?_⟩ <;> linarith

lemma pre_cost (hC : C.Makes) (hG:G.Simple) (h : Booked (temperatures G) P) (r : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ m in atTop, ∀ N p, m ≤ N →
      let t := (C.path.levels).budget m; let g := gAt C N p m
      t.threshold ≤ required G (r+2) t.order t.power ∧
        cost G t (C.path.β N p m) (r+2) ≤ δ * g^((r : ℝ)+1-ε) := by
  let T:= C.path.levels
  let Y := geo P
  let A (m:ℕ):= T.budget m
  let W (m:ℕ):= 2*T.clock.monitor m
  have hw: Budgeted T W:= Budgeted.mul (Budgeted.const zero_le_two) (livingPrices hG).2.1
  let D : ℝ:= (Fintype.card Signed : ℝ)*Fintype.card PlaqAxes
  let u(m:ℕ):= D*Y m*Y m*(W m)^(r+3)
  have hc:Budgeted T u:= ((Budgeted.const (show 0 ≤ D by dsimp [D]; positivity)).mul y_spend|>.mul y_spend)|>.mul (hw.pow _)
  filter_upwards [keepPaid hC hG hε hδ hc, tail_prices hG h (r+2), keepPaid hC hG zero_lt_one zero_lt_one (Budgeted.mul y_spend hw)] with m he hm hs N p hN
  obtain ⟨hf,hr,hu⟩:=hm
  intro P₀ g
  have hK : 0<g:= running_pos hC _ _ _ hN
  have ha := (thresholdHat hC hN (p:=p)).1
  change P₀.threshold ≤ g*W m at ha
  constructor
  · have H (x y z:ℝ) (hx:x>0) (hy:y≥0) (h : x⁻¹ ≤ z) (hM:z*y ≤ 1): y ≤ x:= by
      calc
       y = x*(x⁻¹*y) := by field_simp
       _ ≤ x*1 := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right h hy).trans hM) hx.le
       _ = x := mul_one _
    have hx:= hs N p hN; rw [Real.rpow_one] at hx
    apply H _ _ (Y m) (required0 ..) P₀.threshold_pos.le hr
    exact (mul_le_mul_of_nonneg_left ha (zero_le_one.trans (geo_hi P m))).trans (by change Y m*(g*W m) ≤ 1; linarith only [show (Y m*W m)*g ≤ 1 from hx])
  change D * (WilsonStartup.Start.overhead P₀*(C.path.β N p m*(offered G (r+2) P₀.order P₀.power * P₀.threshold ^ _ ))) ≤ _
  rw [← reset_sq hC _ _ _ hN]
  have H : D*(WilsonStartup.Start.overhead P₀*(g⁻¹ ^2*(offered G (r+2) P₀.order P₀.power * P₀.threshold ^ (r+2+1))))
      ≤ D*(Y m*(g⁻¹ ^2*(Y m*(g*W m)^(r+3)))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul (by exact hu) (mul_le_mul_of_nonneg_left (mul_le_mul hf
      (pow_le_pow_left₀ P₀.threshold_pos.le ha _) (pow_nonneg P₀.threshold_pos.le _) (zero_le_one.trans (geo_hi ..))) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (mul_nonneg (offered0 ..).le (pow_nonneg P₀.threshold_pos.le _))) (zero_le_one.trans (geo_hi ..))) (by unfold D; positivity)
  refine H.trans ?_
  have hx:= he N p hN
  calc
    _ = u m * g^((r:ℝ)+1) := by unfold u; rw [← Nat.cast_add_one, Real.rpow_natCast]; field_simp; ring
    _ = (u m * g^ε) * g^((r:ℝ)+1-ε) := by rw [mul_assoc (u m) (g^ε),← Real.rpow_add hK]; congr 1; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hK.le _)
end Startup
end YM.RG04B
