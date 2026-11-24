import YM.Integration.WilsonInvariantActionPosition
import YM.Integration.WilsonMatrixTicketLanesReportedTransport
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

/-! The charge of the same filed Wilson operator at the first retained mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPromotedQuota
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source RG17 Next.UVStress
open PhysicalNext.Repeat.Legato RG12 OPE Extraction SharpGram Spec Table Trace.Pilot
open WilsonInvariantActionPosition
open private finer from YM.Integration.WilsonInvariantActionPosition
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (h : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "A" => R.family.path.levels
local notation "C" => R.family
local notation "a" => R.family.S.a

private lemma delta (m n:ℕ): H n=H m+G.slopeConstant*(Real.log (a m/a n)) := by
    rw [Real.log_div ((C).S.a_pos _).ne' ((C).S.a_pos _).ne']
    unfold Calendar.hatBeta Schedule.scale; simp_rw [Real.log_inv]; change _ + G.slopeConstant*(-(Real.log (a n)))= _+G.slopeConstant*(-Real.log (a m))+G.slopeConstant*_ -- parentheses
    ring

include h pace in
theorem retained (s:ℕ) : ∀ᶠ m:ℕ in atTop,
    let y:= berth R s m
    H y ≤ 2*H m ∧ a m / a y ≤ H m^(s+2) := by
    let K(z:ℝ):= Real.log z; let l:= G.slopeConstant; have hl:0<l:= Gauge.slopeConstant_pos h
    have hm:Tendsto (fun z:ℝ=> l*((s+2:ℕ)*K z)/z) atTop (𝓝 0):=by
       have hv:= Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
       simpa only [K, mul_zero, ←mul_div_assoc, mul_assoc, id_eq] using! hv.const_mul (l*(s+2:ℕ)) -- type
    have hβ := Next.Rank.Station.hat_rate (A) h; filter_upwards [hβ.eventually_ge_atTop 2, hβ.eventually (hm.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)))] with m hs hb y
    let p:= H m; have hp:2≤p:= hs; have hx:0<p:= zero_lt_one.trans ((A).fits.delayed m)
    have hh:l*((s+2:ℕ)*Real.log p) ≤ p:= (div_le_one₀ hx).mp hb
    obtain ⟨i,hI⟩:= Nat.exists_eq_succ_of_ne_zero (show y ≠ 0 from (Nat.zero_le m|>.trans_lt (arrival R s m).1).ne') -- y is let! can't rfl
    have hi:m ≤ i:=by have hh : m<y:= (arrival R s m).1; omega
    have he : a m/a i ≤ p^s:=by
       obtain he|rfl:= lt_or_eq_of_le hi
       · have hq:a m < a i*p^s:= lt_of_not_ge fun h'=> by
              have hi:y ≤ i:= Nat.find_min' (finer R m s) ⟨he,h'⟩; omega
         exact (div_le_iff₀ ((C).S.a_pos i)).mpr (hq.le.trans_eq (mul_comm ..))
       rw [div_self ((C).S.a_pos _).ne']; exact one_le_pow₀ (by linarith)
    have hz {z q:ℕ} (hq:q≤ s+2) (hf:a m/a z ≤ p^q) : H z ≤ 2*p := by
       have hσ:= Real.log_le_log (div_pos ((C).S.a_pos _) ((C).S.a_pos _)) hf; rw [Real.log_pow] at hσ
       have hf := (mul_le_mul_of_nonneg_left (hσ.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq)
          (Real.log_nonneg ((A).fits.delayed m).le))) hl.le).trans hh
       rw [delta R m]; change p+l*_≤_; linarith only [hf]
    let V:= ((A).S.block i).val
    have hP : (V:ℝ) ≤ p^2:= by
       have bi : 0<H i := zero_lt_one.trans ((A).fits.delayed i)
       have logcap : Real.log (2+Real.log (H i)) ≤ H i := calc
         _ ≤ Real.log (1+H i) := Real.log_le_log (by
           have := Real.log_nonneg ((A).fits.delayed i).le; linarith)
           (by linarith [Real.log_le_sub_one_of_pos bi])
         _ ≤ H i := by linarith [Real.log_le_sub_one_of_pos (show 0<1+H i by linarith)]
       have hr : (V:ℝ) ≤ H i := (pace.2 i).trans logcap
       exact hr.trans ((hz (show s≤ s+2 by omega) he).trans (by nlinarith only [mul_le_mul_of_nonneg_right hp hx.le]))
    have hk : a m / a (i+1) ≤ p^(s+2):=by
       have hf: a m/a (i+1)=(a m/a i)*(V:ℝ):= by rw [(C).S.a_step i]; let M:=a i; exact (by unfold V; rw [div_div_eq_mul_div, div_mul_eq_mul_div])
       rw [hf,pow_add]; exact mul_le_mul he hP (Nat.cast_nonneg _) (pow_nonneg hx.le _)
    rw [hI]; exact ⟨hz le_rfl hk,hk⟩

variable {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)
    (L : RG17.Layout F) (E : OPE.Services R.family f S)

include h pace E in
theorem price (s d e : ℕ) :
    ∀ᶠ m : ℕ in atTop, let k:=berth R s m
      ∀ {r : ℝ}, L.level r=m → ∀ {M:ℝ}, 0 ≤ M →
      ∀ (w : R.family.label d), R.family.ref d ≤ m →
      (∀ N p, m ≤ N → quota R.family d m N p (atRef L d r (N,p) w) ≤
        a m^d*(H m^e*M)) → ∀ N p, k ≤ N →
        quota R.family d k N p (atRef L d r (N,p) w) ≤ a k^d*(H k^((s+2)*(d+1)+e)*M) := by
  filter_upwards [retained R h pace s] with m paid
  dsimp only
  let k:=berth R s m
  intro r date M hM w hr receipt N p hN
  have order : m ≤ k := (arrival R s m).1.le
  have ref : R.family.ref d ≤ L.level r := date.symm ▸ hr
  have upper := WilsonMatrixTicketLanesReportedTransport.later R F L E d r w k N p ref
    (date.symm ▸ order) hN
  rw [date] at upper
  have exactQuota := WilsonMatrixTicketLanesReportedAdmission.quota R F L d r w ref m 0 (by rw [date])
  rw [date] at exactQuota
  have lower := receipt m 0 le_rfl
  rw [exactQuota] at lower
  have cost := (mul_le_mul_iff_right₀ (pow_pos (R.family.S.a_pos m) d)).mp lower
  have positive : 0 ≤ H m := (zero_lt_one.trans (R.family.path.levels.fits.delayed m)).le
  have ratio : 0 ≤ a m / a k := div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos k).le
  have bound : (a m/a k)^(d+1) ≤ H m^((s+2)*(d+1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ ratio paid.2 _
  have heat : H m ≤ H k := WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos h).le order
  have cap := upper.trans (mul_le_mul bound cost (mass_nonneg ..) (pow_nonneg positive _))
  have top : (H m^((s+2)*(d+1)))*(H m^e*M) ≤ H k^((s+2)*(d+1)+e)*M := by
    rw [←mul_assoc,←pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ positive heat _) hM
  exact ((div_le_iff₀ (pow_pos (R.family.S.a_pos k) d)).mp (cap.trans top)).trans_eq (mul_comm ..)

end YM.Integration.WilsonInvariantActionPromotedQuota
