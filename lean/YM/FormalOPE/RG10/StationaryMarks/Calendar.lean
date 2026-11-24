import YM.FormalOPE.RG10.StationaryMarks.Shed
/-!
 # obtaining derivative/gradient budget in clocks. For analytic argument in one fixed finite cell!
 No uniform-in-Λ.. needed at this stage.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {I J:Type}[Fintype I][Fintype J]
lemma guarded {a:Spending G I} (H:Credential a) {v:ℝ}(hv:0<v): Credential (v • a) where
 meas:= Measurable.const_mul H.meas v
 nn u:= mul_nonneg hv.le (H.nn u)
 center:= by simp [H.center]
 smooth:= contDiffAt_const.mul H.smooth
 cut S h:= by
  obtain ⟨R,hr,ha⟩:= H.cut S h
  exact ⟨v*R,mul_pos hv hr,fun u hu=> ha u (lt_of_mul_lt_mul_left (a:=v) hu hv.le)⟩
 strict u hu:= by rw [show (v • a) ∘ expLinks G I = v • (a∘ expLinks G I) from rfl,times _ _ H.smooth]; exact mul_pos hv (H.strict u hu)
variable {P:ChartRatio G}{U: Survey G I J} {w:J→ℝ→ℝ}
namespace Survey.Ready
variable (R:U.Ready)
include R in
lemma event (h:∀ j,Tracks (w j) (U.w j)): ∀ᶠ t in Tested.germ, ∀ j,0<w j t:= Filter.eventually_all.mpr (fun j=> (h j).tendsto_first.eventually (IsOpen.mem_nhds isOpen_Ioi (R.lead_pos j))) -- Tracks

include R in
lemma rate_bound (h:∀ j,Tracks (w j) (U.w j)):∃ B:ℝ,0≤B ∧ ∀ᶠ t in Tested.germ,∀ j,
 ‖Tracks.rate (w j) (U.w j) t‖≤ B*term (U.w j) 0 := by
 choose C hc hb using fun j=> (Tracks.start (h j)).bounded
 let b:= fun i:J=>C i / term (U.w i) 0
 let B:=∑ i,b i
 have ha i:0 ≤ b i := div_nonneg (hc i) (R.lead_pos i).le
 refine ⟨B,Finset.sum_nonneg fun _ _=>ha _, Filter.eventually_all.mpr fun j=>?_⟩
 filter_upwards [hb j] with t ht
 rw [pow_zero,mul_one] at ht
 apply le_trans ht
 apply (div_le_iff₀ (R.lead_pos _)).mp; exact Finset.single_le_sum (f:=b) (fun i _=> ha i) (Finset.mem_univ j)
local notation "W" => U.target
include R in
lemma spike_bill {t B:ℝ} (h:∀ j, ‖Tracks.rate (w j) (U.w j) t‖ ≤ B * term (U.w j) 0) (ht:0<t) (x:Configuration G I):
 ‖U.spike w t x‖ ≤ (B*t)*(W x / t^2) := by
 unfold spike; rw [norm_div,Real.norm_of_nonneg ht.le,div_le_iff₀ ht,show B*t*(W x/t^2)*t= B*W x from by field_simp];
 refine (norm_sum_le ..).trans ?_; unfold Survey.target; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i hi=>?_
 rw [norm_mul,Real.norm_of_nonneg ((R.sincere i).nn x), ←mul_assoc]; exact mul_le_mul_of_nonneg_right (h i) ((R.sincere i).nn _)

-- for calling on any finite-state body where readMarks defined.
include R in
lemma enough {O : Spending G I}(h:Curtain O)(k:ℕ)(w t): Integrable (fun x=> dollar W O t x * U.rubber w k t x) (physical G I):= by
 simp_rw [Survey.rubber_stamp]; apply integrable_finsetSum; intro i hi; apply integrable_finsetSum; exact fun j _=> (endowment R.entire (R.readings i h j) t).const_mul _
include R in
lemma curved {O:Spending G I}(h:Curtain O){t:ℝ} (hs:∀ i,0<w i t): Integrable (dollar (U.adjusted w t) O t) (physical G I):= by
 obtain ⟨b,hb⟩:= h.bounded
 apply (integrable_const b).mono'
 · exact (h.meas.mul ((Measurable.exp (Measurable.div_const (Measurable.neg (show Measurable (U.adjusted w t) from Finset.measurable_sum _ fun i _=>(R.sincere i).meas.const_mul _)) _)))).aestronglyMeasurable
 refine Eventually.of_forall fun u=>?_
 unfold dollar; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
 have hn:0≤ U.adjusted w t u:= Finset.sum_nonneg fun _ _=> mul_nonneg (hs _).le ((R.sincere _).nn u)
 exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn) (sq_nonneg _)))).trans (hb u)
end Survey.Ready
end YM.FormalOPE.RG10.StationaryMarks
