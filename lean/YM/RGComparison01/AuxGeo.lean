import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Canvas
import YM.RGComparison01.AuxGrace
import YM.RGComparison01.AuxCurtain

/-! # Fixed-stage currencies. Polygonal in the fine monitor (vs Bolt, polygonal
in the bill / support radius). Only converts to a subpower at a fixed stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric MeasureTheory ProbabilityTheory Lattice Wilson RG Pressure RG Gauge
open Input Precision Tree Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix Work.G05 Push.AbsoluteSums
open AuxJets PhysicalNext PhysicalNext.Repeat WilsonStartup Tensor Lapis Lantern Sienna ConnectedActivityE6.Coat
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal

def Geo (G : Gauge) (L : Side) (f : ℝ→ℝ) := ∃ (C : ℝ) (k:ℕ),0 ≤ C ∧
    ∀ᶠ x in atTop, |f x| ≤ C*Delay.fineMonitor G L x^k
namespace Geo
variable {G : Gauge} {L : Side} {f g : ℝ→ℝ} {u v d : ℝ}
local notation "z" => Delay.fineMonitor G L
local notation "y" => (fun t=> Pressure.betaF G t L)
local notation "r" => (fun t=> 2*gStep (y t))
lemma rate (h : Geo G L f) : Rate G L 0 f:= by
  obtain ⟨C,k,hc,h⟩:=h
  exact Rate.compare ((Brim.prep (Rate.monitor (G:=G) (L:=L)) k).mul_left C) (h.mono fun x hx=> hx.trans (le_abs_self _))
lemma basic (h : Bolt G L f) : Geo G L f:= by
  refine ⟨1,1,zero_le_one,?_⟩; simpa only [one_mul, pow_one,Real.rpow_one] using h.listens zero_lt_one
lemma fixed (C:ℝ) : Geo G L (fun _=> C) := basic (Bolt.still _)
lemma mean (h : Geo G L f) : Geo G L (fun x=> |f x|):= by obtain ⟨C,k,hc,H⟩:=h; exact ⟨C,k,hc,by simpa using H⟩
lemma joins (h : Geo G L f) (H : Geo G L g) : Geo G L (fun x=> f x+g x):= by
  obtain ⟨C,k,hc,h⟩:=h; obtain ⟨D,j,hd,H⟩:=H; refine ⟨C+D,k+j,add_nonneg hc hd,?_⟩
  filter_upwards [h,H] with x hx hy
  have he:1 ≤ z x:=Real.one_le_exp (sq_nonneg _)
  rw [add_mul]; exact (abs_add_le _ _).trans ((add_le_add hx hy).trans (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (by omega)) hc) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (by omega)) hd)))
lemma times (h : Geo G L f) (H : Geo G L g) : Geo G L (fun x=> f x*g x):= by
  obtain ⟨C,k,hc,h⟩:=h; obtain ⟨D,j,hd,H⟩:=H; refine ⟨C*D,k+j,mul_nonneg hc hd,?_⟩
  filter_upwards [h,H] with x hx hy
  rw [abs_mul,pow_add]; exact (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)).trans_eq (by ring)
lemma power (h : Geo G L f) (k : ℕ) : Geo G L (fun x=> f x^k):= by
  induction k with
  | zero=>simp only [pow_zero]; exact fixed 1
  | succ i ih=>simp only [pow_succ]; exact ih.times h
lemma expel {κ : Type} (s : Finset κ) (f : κ→ℝ→ℝ) (h : ∀ i∈s, Geo G L (f i)) :
    Geo G L (fun x=> ∑ i∈s,f i x) := by
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty]; exact fixed 0
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).joins (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma by_delay : Geo G L (Delay.fineMonitor G L) := ⟨1,1,zero_le_one,Eventually.of_forall fun x=> by simp [abs_of_pos (Delay.monitor_pos ..)]⟩
lemma rot (j:ℕ) (h : Geo G L f) (hp : Geo G L g) : Geo G L (fun x=> Lantern.clump j (f x) (g x)) := by
  unfold Lantern.clump; simp only [mul_one]; exact ((fixed _).times hp).times (((fixed _).joins ((fixed _).joins h)).power _)
lemma fee (j:ℕ) (h : Geo G L f) (hp : Geo G L g) : Geo G L (fun x=> Lantern.fee j (f x) (g x)) := by
  have he:=(((fixed 1).joins h).joins hp)
  have ht:= rot j (he.joins he) h; have hw:= hp.times (hp.times ht); exact ((h.joins h).joins (hw.joins hw)).joins (ht.joins ht)
lemma primary (P : Patch) (O : ChartRatio G) (b : Clip) {σ C:ℝ} {Q : KernelChoices} {n:ℕ}
    (A : Before G σ C P.J Q (n+3)) (E : FiberFee O ((n+3)+1))
    (h : Bolt G L f) : Geo G L (fun t=> pam n O b P A (f t) (f t) E (ConnectedActivityE6.loopBill G L t)):= by
  obtain ⟨a,v,ha,hv,he⟩:= posts L P O b A E h|>.2; rw [funext he]; exact (basic ha).joins ((basic hv).times by_delay)
lemma short (h : Geo G L f) (ha : 0 < u) : ∀ᶠ t in atTop, |f t| * r t < u := Sienna.below' _ _ ((rate (mean h)).mul (glim G L)) (by norm_num) ha
lemma uniform (h : Geo G L f) (ha : 0 < u) : ∀ᶠ t in atTop, ∀ β, y t/2≤ β → |f t| * gStep β < u := by
  filter_upwards [short h ha,Delay.shift_pos G L] with t ht hx β hB using lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Sienna.lamp G L hx β hB).2 (abs_nonneg _)) ht
lemma wiggle (d:ℝ) (hd : 0 < d) : ∀ᶠ x in atTop, 1 ≤ Sienna.wick G L d x := by
  filter_upwards [(Bolt.still d⁻¹).listens (G:=G) (L:=L) zero_lt_one] with x hx
  rw [Real.rpow_one] at hx
  simpa only [Sienna.wick, mul_comm d] using (inv_le_iff_one_le_mul₀ hd).mp ((le_abs_self _).trans hx)
-- corridor
lemma strip {β : ℝ} (hx : 0 < u) (hβ : 0<β) (H : β ≤ 2*u) : gStep u ≤ 2*gStep β:= by
  -- positivity, inverse-square ν
  have hu:= Fare.gS u hx; have hr:= Fare.gS β hβ
  apply (sq_le_sq₀ hu.1.le (show 0≤2*gStep β from mul_nonneg (by norm_num) hr.1.le)).mp; apply le_of_mul_le_mul_right _ hβ
  rw [mul_pow,mul_assoc,hr.2,mul_one]; nlinarith only [hu.2, mul_le_mul_of_nonneg_left H (sq_nonneg (gStep u))]
lemma advance (k : ℕ) : ∀ᶠ t in atTop, ∀ β,
    0<β → β≤2*y t → y t^(-((k:ℝ)/2 + 1)) ≤ (gStep β)^k:= by
  let a:ℝ:=-(k/2+1); have hv:= Rate.power (G:=G) (L:=L) (a:=a) |>.mul_left (2^k:ℝ)
  filter_upwards [hv (-(k/2)) (by unfold a; linarith),Delay.shift_pos G L] with t ht hh β hβ hV
  have he := Fare.gS β hβ
  have h0 : y t^(-(k/2:ℝ))=(gStep (y t))^k:= by
    rw [show (-(k/2:ℝ))=-(1/2:ℝ)*k by ring,Real.rpow_mul hh.le,Real.rpow_neg hh.le, Real.rpow_natCast,← Real.sqrt_eq_rpow]; rfl
  have hp:=Fare.gS (y t) hh
  refine le_of_mul_le_mul_left (((le_abs_self _).trans ht).trans ?_) (show (0:ℝ)<2^k by positivity)
  rw [← mul_pow]; exact h0.trans_le (pow_le_pow_left₀ hp.1.le (strip hh hβ hV) _)
lemma loss (h : Geo G L f) {η : ℝ} (hc : 0 < η) (j:ℕ) : ∀ᶠ x in atTop,
    ∀ β, 0 < β → y x/2 ≤ β → |f x| * (gStep β)^j ≤ gStep β^((j:ℝ)-η):= by
  have hv:= (rate h|>.mul_left ((2:ℝ)^η)) (η/2) (by linarith)
  filter_upwards [Delay.shift_pos G L,hv] with x hx ht β hβ H
  have he:=Fare.gS β hβ; have hk:=Fare.gS (y x) hx
  rw [abs_mul,abs_of_pos (show (0:ℝ)< (2:ℝ)^η from Real.rpow_pos_of_pos (by norm_num) _)] at ht
  rw [Real.rpow_sub he.1,Real.rpow_natCast]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos he.1 η)).2
  have ha : |f x| * (gStep β)^η ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he.1.le (Sienna.lamp G L hx β H).2 hc.le) (abs_nonneg _)).trans ?_
    have he: y x^(η/2)= (gStep (y x)^η)⁻¹:= by
      rw [show η/2=(1/2:ℝ)*η by ring,Real.rpow_mul hx.le,← Real.sqrt_eq_rpow]; unfold gStep; rw [Real.inv_rpow (Real.sqrt_nonneg _), inv_inv]
    rw [he] at ht
    rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) hk.1.le, ← mul_assoc,mul_comm |f x|]; exact (mul_le_mul_of_nonneg_right ht (Real.rpow_pos_of_pos hk.1 η).le).trans_eq (inv_mul_cancel₀ (Real.rpow_pos_of_pos hk.1 η).ne')
  exact le_trans (le_of_eq (show _= (|f x| * gStep β^η)*gStep β^j by ring)) (mul_le_of_le_one_left (pow_nonneg he.1.le _) ha)
end Geo
end YM.RGComparison01
