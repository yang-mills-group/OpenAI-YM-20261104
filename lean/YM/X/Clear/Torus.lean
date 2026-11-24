import YM.X.Clear.Methods
/-!
Native torus and fixed regulator path data. Can carry analytic costs for arbitrary itinerary. Extend finite plateau sizes later, use along any filter. All difference orders admissible. Rates not claimed in separated limit. Most lemmas stated at ℕ Itinerary filters but sizes arbitrary positive integers. h huge physical.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval
open Function Filter Set MeasureTheory Metric Lattice Pert Pert.Align Pert.Full
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n : Side} (R: Pert.Align.Itinerary)
local notation "N" j=> R.period j
local notation "S" j=> Site (N j)
local notation "a"=> R.gap
set_option quotPrecheck false
variable (D:List Axis)
lemma stem_tends (x:Cover): Tendsto (fun k=>grads D green (wrap (N k) x)) atTop (𝓝 (grads D Cellular.coverLine x)):= by
   induction D generalizing x with
   | nil=>
     have ht := Cellular.strike_two R.period R.gap R.positive R.even_at R.huge R.cutoff 0 x; simp only [Int.cast_zero, Nat.cast_zero, neg_zero,zpow_zero,mul_one] at ht
     exact tendsto_sub_nhds_zero_iff.mp ht -- name
   | cons i d h=> simp_rw [grads,differ, ← wrap_step (N _) i, ← map_add]; exact (h (x+step i)).sub (h x)
lemma torus_rate : ∃ C:ℝ,C≥0 ∧ ∀ᶠ i:ℕ in atTop,∀ z:S i,|grads D green z| ≤ C/(1+pdist z:ℝ)^(2+D.length):= by
   obtain ⟨C,b,hC,hb⟩:= rate D
   let g k : ℝ:= |grads D Cellular.coverLine k|
   let U:= ∑ k∈Lattice.box b, (g k+1)
   have hp : U≥0:= Finset.sum_nonneg fun i hi=> by unfold g; positivity
   let m:=2+D.length; let H:= C*2^m+U*(1+b)^m; refine ⟨H,by unfold H; positivity,?_⟩
   have ht (x:Cover): ∀ᶠ i in atTop, |grads D green (wrap (N i) x)|≤g x+1:= (stem_tends R D x|>.abs).eventually (ge_mem_nhds (show g x<g x+1 from by linarith))
   filter_upwards [(eventually_all_finset (Lattice.box b)).mpr fun x _=>ht x] with i hi z; let s:ℝ:=pdist z
   change _ ≤ H/(1+s)^m; rw [le_div_iff₀ (show 0<(1+s)^m by dsimp [s]; positivity)]
   rcases lt_or_ge b (pdist z) with hz|hz
   · have hs:1≤s:= Nat.one_le_cast.mpr (Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le _) hz)); have hP := hb z hz; change _ ≤ C/s^m at hP; rw [le_div_iff₀ (by exact pow_pos (lt_of_lt_of_le zero_lt_one hs) _) ] at hP; calc
         _ ≤ |grads D green z| * (s*2)^m := by gcongr; linarith
         _ ≤ C*2^m := by rw [mul_pow, ←mul_assoc]; gcongr
         _ ≤ _ := le_add_of_nonneg_right (by positivity)
   · have hx:lift z∈Lattice.box b:= by rw [box_iff_layers]; intro i; refine Finset.mem_Icc.mpr ?_; have hh:=component_le z i; omega
     specialize hi (Lattice.lift z) hx; rw [wrap_lift] at hi
     have hu : |grads D green z|≤U:= hi.trans (Finset.single_le_sum (f:=fun k=>g k+1) (fun v _=>by unfold g; positivity) hx)
     calc _ ≤ U * (1+b)^m:= by gcongr; unfold s; exact_mod_cast hz
          _ ≤ _:= le_add_of_nonneg_left (by positivity)
lemma rpath_casual (b:E4)(hb:b≠0)(x:StepPath R)(hx:Tendsto (fun i=> incVec (a i) (lift (x i))) atTop (𝓝 b)):
    Tendsto (fun k=>grads D green (x k) / (R.gap k)^(2+D.length)) atTop (𝓝 (Band.casual D b).re):= ((Complex.continuous_re.continuousAt.tendsto.comp (Band.joint_casual _ _ _ _ _ hb R.grid_eq R.positive R.clears R.cutoff hx))).congr (fun k=> ((eq_div_iff (show (R.gap k)^(2+D.length) ≠ 0 from (pow_pos (R.positive _) _).ne')).2 (raw_pay D (x k) (R.positive k))))
end YM.PositionX.Interval
