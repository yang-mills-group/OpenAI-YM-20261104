import YM.SchemeConversionRG11.FirstW.Mark.Gate
/-! Uniform differentiated decay, single-leg. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Pert.Align Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} (k : Labels.Key G)
lemma swim (o x : Site n) (a : Axis) (H : List Axis) : combine H (fun v=>canal k o (v,a)) x = ∑ t:QuotSpot k, combine (H ++ rivDir k t) (linGreen n) (x-o + wrap n (footA k t)) • header k t a := by
  induction H generalizing x with
  | nil=> exact repr_river k o x a
  | cons i H ih=> rw [combine,up,ih,ih,←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro t _; rw [←sub_smul, List.cons_append,combine,up]; congr 3; abel
lemma tread (T : Itinerary) (a : Axis) (H : List Axis) : ∃ C>0,∀ᶠ i in atTop,∀ x o:Site (T.period i), (cy (x-o))^(H.length + mass k + 1) * ‖combine H (fun v=>canal k o (v,a)) x‖ ≤ C := by
  let q:= H.length+mass k+1
  choose A ha hA using fun t:QuotSpot k=> tor_decay T (H++rivDir k t)
  let C (t : QuotSpot k) := (1+stepY (footA k t))^q*A t* ‖header k t a‖
  have hc (t : QuotSpot k) : 0≤ C t := by unfold C; have := unit_stepY (footA k t); specialize ha t; positivity
  refine ⟨1+∑ t,C t, add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun i _=>hc i)),?_⟩
  filter_upwards [eventually_all.mpr hA, eventually_all.mpr (fun t:QuotSpot k=>past T (footA k t))] with i hi he
  intro x o
  change (cy (x-o))^q*_≤_; rw [swim]
  grw [norm_sum_le _ _]; swap; · have := unit_cy (x-o); positivity
  rw [Finset.mul_sum]; apply le_trans (Finset.sum_le_sum (g:=C) (fun t _=>?_)) (le_add_of_nonneg_left (by norm_num))
  rw [norm_smul]; let v:= x-o; let w:=v+wrap (T.period i) (footA k t); let b:= 1+stepY (footA k t); let R:= combine (H++rivDir k t) (linGreen _) w
  have h1 : cy w ^ q * ‖R‖ ≤ A t := by have e:= hi t w; rwa [List.length_append,show H.length+ (rivDir k t).length+2=q from by unfold q; have := riv_mass k t; omega] at e
  have ht : cy v ≤ b *cy w := (he t v).2
  rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (unit_cy _)) ht q) (show 0≤‖R‖ by positivity)) (by rw [mul_pow,mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (by unfold b; linarith [unit_stepY (footA k t)]) _))) (norm_nonneg _)
-- limits of K centered-at-0 and normalized by all engineering powers (last open potential has h unit)
def wageA (k : Labels.Key G) (t : QuotSpot k) (a : Axis) : ℝ →L[ℝ] G.Color := ((ContinuousLinearMap.id ℝ ℝ).smulRight (header k t a))
def tongs (k : Labels.Key G) (a : Axis) : Sheets G.Color := ∑ t:QuotSpot k, (fun (D : List Axis) (x : E4)=>wageA k t a ((Band.casual (D++rivDir k t) x).re))
def knot (T : Itinerary) (k : Labels.Key G) (a : Axis) : Board T G.Color := fun i x=> (T.gap i)⁻¹ • river (T.gap i) k (0:Site (T.period i)) (x,a)
lemma stream (T : Itinerary) (a : Axis) : Score T {x : E4 | x≠0} (knot T k a) (tongs k a) := by
  let X : Board T ℝ := fun i=>(T.gap i^2)⁻¹ • linGreen _
  let Z (t : QuotSpot k) : Board T ℝ := fun i x=>surface (rivDir k t) X i (x+wrap (T.period i) (footA k t))
  let F (t : QuotSpot k) : Board T G.Color := fun i x=>wageA k t a (Z t i x)
  let p (t:QuotSpot k) D x := wageA k t a ((Band.casual (D++rivDir k t) x).re)
  have hv (t): Score T {x:E4| x≠0} (F t) (p t) := Score.map _ (((Score.origin (T:=T)).insect (rivDir k t)).nudge (footA k t))
  have e : (∑ t,F t) = knot T k a := by
    funext i x
    rw [Finset.sum_apply,Finset.sum_apply,knot, river,Pi.smul_apply,repr_river]; simp_rw [sub_zero,Finset.smul_sum]; apply Finset.sum_congr rfl; intro t _
    unfold F wageA; simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply, Z,X,surface,combine_smul,Pi.smul_apply,smul_eq_mul,smul_smul]
    apply congrArg (fun z:ℝ=> z • header k t a); rw [←riv_mass k t,pow_add,pow_two, mul_inv,pow_one,mul_inv]; ring
  rw [← e]; exact Score.sum Finset.univ (fun i _=>hv i)
end YM.RG11.FirstW
