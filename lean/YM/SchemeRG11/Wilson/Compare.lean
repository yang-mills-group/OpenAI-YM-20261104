import YM.SchemeRG11.Wilson.Bounds
/-! Displacement-changing Cell comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.SchemeRG11.Catch
open Lattice Function Filter Asymptotics Pert Full Band Topology Align
open MeasureTheory Metric Set
open Cellular
open scoped Classical BigOperators ENNReal
variable {n : Side}
lemma clock_cost (z : Cover) (x y : E4) : |clock z x-clock z y| ≤ 4*((diam z:ℝ)*(Band.turn)*‖x-y‖):=by
 apply (Real.abs_cos_sub_cos_le ..).trans
 unfold corner
 push_cast
 rw [← Finset.sum_sub_distrib]
 apply (Finset.abs_sum_le_sum_abs ..).trans
 apply le_trans (b:=∑ _i:Axis, ((diam z:ℝ)*Band.turn*‖x-y‖)) _ (le_of_eq (by simp))
 apply Finset.sum_le_sum; intro i _
 have he:= coordinate_le (x-y) i
 simp only [PiLp.sub_apply, PiLp.smul_apply,smul_eq_mul] at *
 rw [show (z i:ℝ)*(2*Real.pi*x i)-(z i:ℝ)*(2*Real.pi*y i)=(z i:ℝ)*(2*Real.pi)*(x i-y i) from by ring, abs_mul,abs_mul,abs_of_pos (by positivity:0<2*Real.pi)]; gcongr; apply castabs

lemma loose : ∃ L≥0,∀ z : Cover,∀ {r : ℝ},0<r→ r≤1 → ∀ {n : Side},8*(n.val:ℝ)⁻¹≤r →∀ {x:E4}, x∈cells→visit n x∈cells→ r < ‖x‖ →
 ‖trace z (visit n x) - trace z x‖ ≤ L*((diam z:ℝ)+1)*(n.val:ℝ)⁻¹ /r^4:=by
 obtain ⟨C,hC,H⟩:= linear_der (0:Cover)
 let D:=4*Band.turn*4
 refine ⟨C+D,add_nonneg hC (show 0≤D by unfold D; positivity),?_⟩
 intro z r hr h1 n hn x hx hw hv
 let y:=visit n x; let N:ℝ:=(n.val:ℝ)⁻¹
 have he(q:E4): trace (0:Cover) q=(dtype q)⁻¹:=by simp [trace,clock,corner]
 have heq : trace z y-trace z x=(trace 0 y-trace 0 x)*clock z y + trace 0 x*(clock z y-clock z x):=by simp_rw [he]; unfold trace; ring
 apply (le_of_eq (congrArg (‖·‖) heq)).trans ((norm_add_le ..).trans ?_)
 simp only [norm_mul]
 apply le_trans (b:=C*N/r^4 + (r^2)⁻¹*(D*diam z*N)) _ ?_
 · apply add_le_add
   · simpa [N] using le_trans (mul_le_of_le_one_right (norm_nonneg _) (clock_price z y)) (H hr h1 hn hx hw hv)
   apply mul_le_mul ((inv_rate _ hx).trans (by gcongr)) _ (norm_nonneg _) (by positivity)
   apply (clock_cost z y x).trans
   calc _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (visit_eps n x) (by positivity : 0≤ (diam z:ℝ)*Band.turn)) (show (0:ℝ) ≤ 4 by norm_num)
        _ = _ := by unfold N D; ring
 have h0 : 0<N := by unfold N; positivity
 have hd : (0:ℝ)≤diam z := by positivity
 have hd' : 0<D := by unfold D; positivity
 change C*N/r^4 + _ ≤ _*_*N/_
 apply le_trans (b:= C*N/r^4 + (r^4)⁻¹ * (D * ↑(diam z) * N)) (add_le_add le_rfl ?_) ?_
 · apply mul_le_mul_of_nonneg_right _ (by positivity)
   apply (inv_le_inv₀ (pow_pos hr _) (pow_pos hr _)).2; have h:= pow_le_one₀ hr.le h1 (n:=2); nlinarith only [h,sq_nonneg r]
 rw [inv_mul_eq_div, ← add_div]; apply div_le_div_of_nonneg_right _ (by positivity); nlinarith only [mul_nonneg hC (mul_nonneg hd h0.le),mul_nonneg hd'.le h0.le]

lemma comparison : ∃ C≥0, ∃ L≥0,∀ {n:Side}, Even n.val →∀ {r : ℝ},0<r → r≤1 → 8*(n.val:ℝ)⁻¹≤r → ∀ z:Cover,
 |thread (wrap n z)-coverLine z| ≤ C*r^2+L*((diam z:ℝ)+1)*(n.val:ℝ)⁻¹ /r^4:=by
 obtain ⟨L,hL,H⟩:=loose
 let C:=26*∫ x:E4, spike 1 x
 have hp (r : ℝ) (x:E4):0≤spike r x:= indicator_nonneg (fun u _=> inv_nonneg.2 <| sq_nonneg _) x
 refine ⟨C, mul_nonneg (by norm_num) (integral_nonneg <| hp 1),L*volume.real cells,mul_nonneg hL ENNReal.toReal_nonneg,?_⟩
 intro n he r hr h1 hn z
 rw [← Real.norm_eq_abs, thread,cover_interp z,weighted z n he,← integral_sub (integrate_visit n he (trace z)).1 (strike z n)]
 let K:=L*((diam z:ℝ)+1)*(n.val:ℝ)⁻¹ /r^4
 have hK : 0≤K:=by unfold K; positivity
 let F:=(cells.indicator (fun _=>K))
 have hf: Integrable F := (integrable_indicator_iff cells_closed.measurableSet).2 (integrableOn_const cells_compact.measure_ne_top)
 apply (norm_integral_le_of_norm_le (g:=fun x=> (26*spike r x)+F x) (((spike_int r).const_mul 26).add hf) ?_).trans_eq
 · dsimp [C]; rw [integral_add ((spike_int r).const_mul 26) hf, integral_const_mul]
   unfold F K; rw [integral_indicator cells_closed.measurableSet, setIntegral_const, smul_eq_mul, spike_pos hr]; ring
 filter_upwards [cell_AE] with x hx
 by_cases ht:x∈cells
 · rw [indicator_of_mem ht,indicator_of_mem ht,show F x=K from indicator_of_mem ht _]; let y:=visit n x
   have hw : visit n x∈cells:=by
     apply (cells_cube _).mpr; unfold visit; obtain ⟨p,hp⟩:= (marked_cell n he hx).mp ht
     rw [←hp,visit_defensive]; apply Full.moment_cube
   rcases lt_or_ge r ‖x‖ with hr'|hr'
   · exact (H z hr h1 hn ht hw hr').trans (le_add_of_nonneg_left (by have := hp r x; positivity))
   rw [show spike r x=(‖x‖^2)⁻¹ from indicator_of_mem (mem_ball.mpr (by rw [dist_zero_right]; linarith)) _]
   exact (inv_visits z n x ht hw).trans (le_add_of_nonneg_right hK)
 rw [indicator_of_notMem ht,indicator_of_notMem ht,show F x=0 from indicator_of_notMem ht _]; have := hp r x; rw [sub_self,norm_zero]; positivity

/-- Convenient filtration for volume errors. -/
def Flat (T : Itinerary) (f : ℕ→ℝ) : Prop := ∀ d:ℕ, Tendsto (fun i=> (T.gap i)^(-(d:ℤ))*f i) atTop (𝓝 0)
def Medium (T : Itinerary) (z : ℕ→Cover) : Prop := ∃ k : ℕ,∀ᶠ i in atTop,(diam (z i):ℝ)+1 ≤ (T.gap i)^(-(k:ℤ))
lemma Medium.shift {T : Itinerary} {z:ℕ→Cover} (hx:Medium T z) (w:Cover) : Medium T (fun i=>z i+w) := by
 obtain ⟨k,hk⟩:=hx
 refine ⟨k+1,?_⟩
 filter_upwards [hk,T.cutoff.eventually (gt_mem_nhds (show 0<(1+(diam w:ℝ))⁻¹ from by positivity)), T.cutoff.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with i hi hf hh
 have hp:=T.positive i
 change (diam (z i+w):ℝ)+1≤_
 push_cast
 grw [(show (diam (z i+w):ℝ) ≤ (diam (z i):ℝ)+(diam w:ℝ) by exact_mod_cast diam_add (z i) w)]
 simp only [neg_add, zpow_add₀ hp.ne', zpow_neg, zpow_natCast,zpow_one] at *
 have hb : 1+(diam w:ℝ) ≤ (T.gap i)⁻¹ := by have := (inv_le_inv₀ (show 0<(1+(diam w:ℝ))⁻¹ by positivity) hp).mpr hf.le; simpa using this
 have hq : 1≤((T.gap i)^k)⁻¹:= one_le_inv_iff₀.mpr ⟨pow_pos hp _,pow_le_one₀ hp.le hh.le⟩
 nlinarith [show (0:ℝ)≤diam w from by positivity]
lemma Flat.add {T:Itinerary} {u v:ℕ→ℝ} (hu:Flat T u)(hv:Flat T v): Flat T (fun i=> u i+v i):= by
 intro k; simp only [mul_add]; simpa only [zero_add] using (hu k).add (hv k)
lemma Flat.sub {T:Itinerary} {u v:ℕ→ℝ} (hu:Flat T u)(hv:Flat T v): Flat T (fun i=> u i-v i):= by
 intro k; simp only [mul_sub]; simpa only [sub_self] using (hu k).sub (hv k)
lemma Flat.naked {T:Itinerary} {u:ℕ→ℝ} (hu:Flat T u): Tendsto u atTop (𝓝 0):=by simpa using hu 0

lemma shrink {T : Itinerary} {z:ℕ→Cover} (hx : Medium T z) : Flat T (fun i=> thread (wrap (T.period i) (z i)) - coverLine (z i)) := by
 obtain ⟨C,hC,L,hL,H⟩:= comparison
 obtain ⟨k,hk⟩:= hx
 intro j
 simp only [zpow_neg,zpow_natCast]
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 let n := k+4*(j+1)+j
 have hx (i : ℕ) : 0<T.gap i:=T.positive i
 apply squeeze_zero' (g:=fun i=> (C*(T.gap i)^(j+2)) + L*(((T.period i).val:ℝ)*(T.gap i)^n)⁻¹) (Eventually.of_forall fun i=> norm_nonneg _) ?_
 · convert (T.cutoff.pow (j+2) |>.const_mul C).add (Tendsto.const_mul L (tendsto_inv_atTop_zero.comp (T.huge n))) using 1 <;> simp
 filter_upwards [hk,(T.huge (j+1)).eventually (eventually_ge_atTop 8),T.cutoff.eventually (gt_mem_nhds zero_lt_one)] with i hi hn ht
 let s:= T.gap i; let N:ℝ:= (T.period i).val
 have hs: 0<s:= T.positive i
 have h0: 0<N:=by unfold N; positivity
 have hv:8*N⁻¹ ≤ s^(j+1):=by rw [← div_eq_mul_inv]; apply (div_le_iff₀ h0).mpr; rw [mul_comm _ N]; exact hn
 have hm:= H (T.even_at i) (pow_pos hs _) (pow_le_one₀ hs.le ht.le) hv (z i)
 rw [norm_mul,Real.norm_of_nonneg (by positivity),Real.norm_eq_abs]
 simp only [zpow_neg,zpow_natCast] at hi
 change (s^j)⁻¹ * _ ≤ C*s^(j+2)+L*(N*s^n)⁻¹
 apply (mul_le_mul_of_nonneg_left hm (show 0≤(s^j)⁻¹ by positivity)).trans
 change (s^j)⁻¹ * (C* (s^(j+1))^2 + L * _ * _/_) ≤ _
 apply le_trans (b:=(s^j)⁻¹ * (C*(s^(j+1))^2 + L * (s^k)⁻¹ * N⁻¹ / (s^(j+1))^4)) (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (show 0≤(s^j)⁻¹ by positivity)) ?_ -- fix
 -- expected
 · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hL) (by positivity:0≤N⁻¹)) (show 0≤ (s^(j+1))^4 by positivity)
 unfold n; rw [show 4*(j+1)=(j+1)*4 by ring]
 change (s^j)⁻¹ * (_+ L * (s^k)⁻¹ * N⁻¹ / _)≤_
 rw [pow_add s (k+_),pow_add s k,pow_mul, pow_add s j, pow_succ]; field_simp; simp only [pow_add]; apply le_of_eq; ring
lemma wideDer {T : Itinerary} {z:ℕ→Cover} (hx:Medium T z) (J : List Axis) : Flat T (fun i=> derive J thread ((wrap (T.period i)) (z i))-derive J coverLine (z i)):=by
 induction J generalizing z with
 | nil => exact shrink hx
 | cons j J ih =>
   have hb := ih (hx.shift (step j))
   have hc:=hb.sub (ih hx)
   simp only [derive,map_add,wrap_step] at *
   convert hc using 1; ext i; abel
end YM.SchemeRG11.Catch
