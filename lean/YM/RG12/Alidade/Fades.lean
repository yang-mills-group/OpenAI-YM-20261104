import YM.RG12.Alidade.Logbook
/-!
# Interpret the intermediate accuracy.

Beats previous earned fare tier *on this Family*, but CANNOT imply full reference-g matching
using additional internal orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Finset Wilson Lattice RG Source Real Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Commission Rail
open scoped Topology BigOperators Classical
variable {G:Gauge}(Y:Levels G)(h:G.Simple)(d:ℕ)(hd:1 ≤ d)
local notation "χ"=> Y.clock.hatBeta
local notation "σ"=> G.slopeConstant
include h
-- neighboring from the schedule already enforced in checkpoint4 yields χ k ≤ k* K * boil(χ k)
-- hence χ*bill(-eps) negligible vs k. Not purchasing power powers from sublinear exponent!
lemma factor_sum (hs:Slugg Y):∃ A:ℝ,0≤A∧∀ᶠ i in atTop, χ i ≤ A*(i:ℝ)*boil (χ i):=by
   let J:=Y.clock.J; let L(i:ℕ):ℝ:= (Y.clock.factor (J i)).val
   have hu(i):0 < L i:=by unfold L; positivity
   have he(k): Y.S.scale k ≤ (k:ℝ)*Real.log (L k):=by
      induction k with
      | zero=>rw [Schedule.scale_zero,Nat.cast_zero,zero_mul]
      | succ k hk=>
        rw [Y.S.scale_succ,← Y.fits.sameFactor,Nat.cast_add_one,add_mul,one_mul]
        have hlo:L k ≤ L (k+1):=by unfold L J; exact Nat.cast_le.mpr (Y.fits.monotoneL (Y.fits.mono (Nat.le_succ k)))
        exact add_le_add (hk.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (hu k) hlo) (Nat.cast_nonneg k))) (by exact le_rfl)
   have hE:Tendsto (fun k:ℕ=>k-1) atTop atTop:=tendsto_atTop_atTop.mpr fun i=> ⟨i+1,fun _ _=>by omega⟩
   have hT := Perch.y_rate.comp (year_late Y h); let σ':=σ; have hh:=Gauge.slopeConstant_pos h
   refine ⟨Y.clock.bar+σ', by unfold σ';linarith [Y.clock.bar_pos],?_⟩
   filter_upwards [hE.eventually (hs 1 zero_lt_one),hE.eventually (Rail.bill_mono Y h (b:=1) zero_le_one),eventually_ge_atTop (1:ℕ),hT.eventually_ge_atTop 1] with i hk ht hv hf
   rw [← Y.fits.sameFactor] at hk
   have hx: L i ≤ bill 1 (χ i) := by
      have hk' := hk.trans ht; simp only [Nat.sub_add_cancel hv] at hk'; exact hk'
   have hM := Real.log_le_log (hu i) hx
   unfold bill at hM; rw [mul_one,Real.log_exp] at hM
   have hf':1≤boil (χ i):= one_le_pow₀ hf
   have he':(1:ℝ)≤ (i:ℝ):= Nat.one_le_cast.mpr hv
   change Y.clock.bar+σ'*Y.S.scale i≤ _
   nlinarith only [mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le he' hf') (Y.clock.bar_pos).le,
       mul_le_mul_of_nonneg_left ((he i).trans (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg i))) hh.le]
omit h Y in
include hd in
lemma cutoff_pos :0 < cut₀ d/4:=by
   have hx : (0:ℝ)< (d:ℝ):=(Nat.cast_pos.mpr hd); unfold cut₀ σ₀; positivity
-- include hd etc
include hd
lemma waste (hs:Slugg Y): Tendsto (fun i:ℕ=>quote Y d i/(i:ℝ)) atTop (𝓝 0):=by
   obtain ⟨A,ha,hA⟩:=factor_sum Y h hs
   let δ := cut₀ d /4; have he : 0<δ:=cutoff_pos d hd
   let q:= fun i=>boil (χ i); have hv: Tendsto q atTop atTop:= (tendsto_pow_atTop (by decide : 2≠0)).comp (Perch.y_rate.comp (year_late Y h))
   have hf : Tendsto (fun i=> A*q i*Real.exp (-(q i*δ))) atTop (𝓝 0):=by
      have hx:= Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n:=1)
      have hh:= (hx.comp (hv.atTop_mul_const he)).const_mul (A*δ⁻¹)
      simp only [mul_zero] at hh
      exact hh.congr fun i=>by
        dsimp only [Function.comp_apply]; rw [pow_one]; field_simp
   apply squeeze_zero' (g:=fun i=> A*q i*Real.exp (-(q i*δ))) ?_ ?_ hf
   · refine Eventually.of_forall fun i=> div_nonneg (mul_nonneg (Real.exp_pos _).le (year Y i).le) (Nat.cast_nonneg _)
   filter_upwards [hA,eventually_gt_atTop 0] with i hi he
   rw [div_le_iff₀ (Nat.cast_pos.mpr he)]
   unfold quote halo bill; rw [mul_neg];nlinarith only [mul_le_mul_of_nonneg_left hi (Real.exp_pos (-(q i*δ))).le]
-- EXPONENT χ i*Ω(i) goes to infinity faster than logχ, and slower than k; no near-coupling bootstrap at that price
omit hd
lemma price_loss : Tendsto (fun i=> quote Y d i / Real.log (χ i)) atTop atTop:=by
   have hl:=year_late Y h
   have hh:= mass_control Y h (cut₀ d/4)
   -- from little-o and reciprocals
   have hx:Tendsto (Real.sqrt ∘ χ) atTop atTop:=Real.tendsto_sqrt_atTop.comp hl
   have hf := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hx).const_mul 2; simp only [mul_zero] at hf
   refine tendsto_atTop.2 fun x:ℝ=>?_
   filter_upwards [hh,hf.eventually (ge_mem_nhds (show 0 < (1+|x|)⁻¹ from by positivity))] with i he ht
   rw [le_div_iff₀ (Real.log_pos (Y.fits.delayed _))]
   apply le_trans _ he
   let t:=Real.sqrt (χ i)
   have hs:0<t:=Real.sqrt_pos.mpr (year Y i)
   have hq := Real.log_sqrt (year Y i).le
   have hk: (1+|x|)*(2*Real.log t) ≤ t:=by
      change 2*(Real.log t/t) ≤ _ at ht
      rw [← mul_div_assoc,div_le_iff₀ hs,inv_mul_eq_div,le_div_iff₀ (by positivity)] at ht
      linarith only [ht]
   rw [← show 2*Real.log t = Real.log (χ i) from by unfold t; rw [hq];ring]
   exact (mul_le_mul_of_nonneg_right (by linarith only [le_abs_self x]) (mul_nonneg (by norm_num) (Real.log_nonneg (by unfold t; exact Real.one_le_sqrt.mpr (delay Y i))))).trans hk

lemma cannot (A:ℝ)(ha:0 < A)(p:ℕ):Tendsto (fun i=> exp (A*quote Y d i)/(χ i ^ p)) atTop atTop:=by
  let q(k:ℕ):= Real.log (χ k); have hx:=Real.tendsto_log_atTop.comp (year_late Y h)
  have he : Tendsto (fun i:ℕ=>A*quote Y d i-(p:ℝ)*Real.log (χ i)) atTop atTop:=by
      apply tendsto_atTop_mono' (f₁:=q) (l:=atTop) _ hx
      filter_upwards [(price_loss Y h d).eventually_ge_atTop ((1+p)/A)] with i hi
      rw [div_le_div_iff₀ ha (Real.log_pos (Y.fits.delayed i))] at hi
      unfold q; linarith only [hi]
  exact (Real.tendsto_exp_atTop.comp he).congr fun i=>by rw [Function.comp_apply,Real.exp_sub,Real.exp_nat_mul,Real.exp_log (year Y i)]
end YM.RG12.Alidade
