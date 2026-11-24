import YM.RG12.Alidade.Map
import YM.RG12.Budget.Logs
/-! # Age and exposure pricing -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak Commission
open Pert.Dense Rail Finset
open scoped Topology BigOperators

variable {G: Gauge} (Y : Levels G) (h:G.Simple)
local notation "χ"=> Y.clock.hatBeta
local notation "nY"=>Y.clock.J
def epoch (Y:Levels G)(i:ℕ):=1+Y.S.scale i/Real.log 3
lemma year (i:ℕ):0< χ i:=zero_lt_one.trans (Y.fits.delayed i)
lemma delay (i:ℕ):1 ≤ χ i:=(Y.fits.delayed i).le
lemma arc3:0<Real.log 3:=Real.log_pos (by norm_num)
lemma epoch_step (i:ℕ) : epoch Y i+1 ≤ epoch Y (i+1):=by
   unfold epoch; rw [Schedule.scale_succ,add_div]
   have he : Real.log 3 ≤ Real.log ((Y.S.block i).val:ℝ):=Real.log_le_log (by norm_num) (by exact_mod_cast Y.S.block_large i)
   linarith only [(one_le_div arc3).mpr he]
@[simp] lemma epoch_initial : epoch Y 0=1:=by rw [epoch,Y.S.scale_zero]; ring
lemma epoch_move : Monotone (epoch Y):= monotone_nat_of_le_succ fun i=> (le_add_of_nonneg_right zero_le_one).trans (epoch_step Y i)
lemma epoch_pace (i:ℕ):1+(i:ℝ) ≤ epoch Y i:=by
   induction i with
   | zero=>simp
   | succ i hi => rw [Nat.cast_add_one]; linarith only [hi,epoch_step Y i]
lemma begun (i:ℕ): 1 ≤ epoch Y i:= (by linarith [show 0≤(i:ℝ) by positivity,epoch_pace Y i])
lemma epoch_late : Tendsto (epoch Y) atTop atTop:= tendsto_atTop_mono (fun i=> epoch_pace Y i) (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ))) |>.congr fun _=>add_comm ..)
lemma epoch_ratio {i j:ℕ}(h:i<j):1+(epoch Y i)⁻¹ ≤ epoch Y j / epoch Y i:=by
   have hf:=zero_lt_one.trans_le (begun Y i)
   rw [le_div_iff₀ hf, add_mul,one_mul,inv_mul_cancel₀ hf.ne']
   exact (epoch_step Y i).trans (epoch_move Y h)
lemma epoch_unit {i j:ℕ}(h:i≤j):1 ≤ epoch Y j /epoch Y i:= (one_le_div (zero_lt_one.trans_le (begun Y i))).mpr (epoch_move Y h)
lemma epoch_neighbor : ∀ᶠ i:ℕ in atTop, epoch Y (i+1)/epoch Y i ≤ 2:=by
   filter_upwards [(Y.fits.mesh).eventually (ge_mem_nhds zero_lt_one),Y.S.divergent.eventually_gt_atTop 0] with k hi hk
   let L:ℝ:= (Y.S.block k).val; let a:= Real.log L
   have h':a ≤ Y.S.scale k:= by
      change a/Y.S.scale k ≤ (1:ℝ) at hi
      exact (div_le_one hk).mp hi
   have hs : 0 < epoch Y k:=zero_lt_one.trans_le (begun Y k)
   rw [div_le_iff₀ hs, epoch,epoch,Y.S.scale_succ,add_div]; linarith only [div_le_div_of_nonneg_right h' arc3.le]
include h
lemma year_mono : Monotone χ:=monotone_nat_of_le_succ (liftClock Y h)
lemma year_late : Tendsto χ atTop atTop:=hat_rate Y h
lemma epoch_enveloped : ∀ᶠ i in atTop, epoch Y i ≤ χ i^2:=by
   let x:=G.slopeConstant*Real.log 3; have hx:0<x:=mul_pos (Gauge.slopeConstant_pos h) arc3
   filter_upwards [(year_late Y h).eventually_ge_atTop (1+x⁻¹)] with i hi
   let s:=Y.S.scale i
   have ht: x*(epoch Y i-1)=G.slopeConstant*s:=by unfold x epoch s; field_simp; ring
   have hb: G.slopeConstant*s ≤ χ i:=by unfold Calendar.hatBeta s; have h:0≤Y.clock.bar:=(Y.clock.bar_pos).le; linarith
   have hh:epoch Y i≤χ i*x⁻¹+1:=by
      apply le_of_mul_le_mul_left (a:=x) _ hx; field_simp
      linarith only [ht,hb]
   nlinarith only [hh,hi,delay Y i,mul_le_mul_of_nonneg_left hi (zero_le_one.trans (delay Y i))]

-- Losing errors e per hop, possibly zero. Budget functions track two different accounts.
def outer (Y:Levels G)(Q:ℕ)(i:ℕ):=Real.exp ((pile (Y.clock.J i)*Real.log (Y.clock.hatBeta i))*Q)
def interest (e:ℕ→ℝ) (A j:ℕ):=Real.exp ((∑ i∈Finset.range j,e i)*A)
omit h in
lemma outer_big (Q i:ℕ):1≤outer Y Q i:=one_le_exp (mul_nonneg (mul_nonneg (pile_pos _) (Real.log_nonneg (delay Y _))) (Nat.cast_nonneg _))
omit h in
lemma outer_hat (Q i:ℕ):outer Y Q i ≤ χ i^Q:=by
    calc
      _ ≤ Real.exp ((Q:ℝ) * Real.log (χ i)):=Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_right (pile_le (nY i)) (mul_nonneg (Nat.cast_nonneg Q) (Real.log_nonneg (delay Y i)))])
      _ = χ i ^ Q:=by rw [Real.exp_nat_mul,Real.exp_log (year Y i)]
lemma outer_east (Q i j:ℕ)(he:i≤j):outer Y Q i≤outer Y Q j:=by
    unfold outer; apply Real.exp_monotone
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Q)
    exact mul_le_mul (pile_mono (Y.fits.mono he)) (Real.log_le_log (year Y i) (year_mono Y h he)) (Real.log_nonneg (delay Y i)) (pile_pos _)
lemma outer_step (Q i j m:ℕ)(he:i≤j)(hs:nY i < m)(hm:m≤nY j):
    outer Y Q i*radar (χ j) m^Q ≤ outer Y Q j :=by
   have hg : outer Y Q i ≤ Real.exp ((pile (nY i)*Real.log (χ j)) * Q):= exp_monotone (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.log_le_log (year Y i) (year_mono Y h he)) (pile_pos _)) (Nat.cast_nonneg Q))
   rw [mul_comm]
   exact (mul_le_mul_of_nonneg_left hg (pow_nonneg (zero_le_one.trans (radar_big (delay Y j) _)) _)).trans (radar_paid (delay Y j) hs hm Q)

omit Y h in
lemma interest_big {e:ℕ→ℝ}(h:∀ i,0≤e i)(A i:ℕ):1 ≤ interest e A i:=one_le_exp (mul_nonneg (Finset.sum_nonneg (fun i _=>h i)) (Nat.cast_nonneg _))
omit Y h in
lemma interest_next (e:ℕ→ℝ)(A i:ℕ):interest e A i*Real.exp (e i)^A=interest e A (i+1):=by unfold interest; rw [Finset.sum_range_succ,← Real.exp_nat_mul,←Real.exp_add]; congr 1; ring
omit Y h in
lemma interest_mono {e:ℕ→ℝ}(h:∀ i,0≤e i)(A:ℕ):Monotone (interest e A):=monotone_nat_of_le_succ fun i=> by
    rw [← interest_next]; exact le_mul_of_one_le_right (zero_le_one.trans (interest_big h A i)) (one_le_pow₀ (one_le_exp (h i)))
omit h in
lemma monitor_big (i:ℕ): 1≤ Y.clock.monitor i:=one_le_exp (sq_nonneg _)
lemma monitor_late : Tendsto (Y.clock.monitor) atTop atTop:= by
   exact Real.tendsto_exp_atTop.comp (Filter.Tendsto.comp (tendsto_pow_atTop (by decide : 2 ≠ 0)) (Perch.y_rate.comp (year_late Y h))) -- check theorem
lemma monitor_control: ∀ᶠ i in atTop, ∀ j, i ≤ j → Y.clock.monitor i ≤ Y.clock.monitor j:=by
   filter_upwards [(Real.tendsto_log_atTop.comp (year_late Y h)).eventually_ge_atTop 1] with i hi j hj
   exact Real.exp_monotone (pow_le_pow_left₀ (Real.log_nonneg hi) (Real.log_le_log (zero_lt_one.trans_le hi) (Real.log_le_log (year Y i) (year_mono Y h hj))) _)
omit h in
lemma licensed (H:Slurry Y) (i:ℕ)(hi:0 < i):Y.clock.monitor i ≤ radar (χ i) (nY i):=by
   simpa [passcost,Nat.sub_add_cancel hi] using (H (i-1)).2.2
lemma vast (H:Slurry Y): Tendsto (passcost Y) atTop atTop:=tendsto_atTop_mono' (l:=atTop) ((eventually_gt_atTop 0).mono (fun i hi=> licensed Y H i hi)) (monitor_late Y h)
end YM.RG12.Alidade
