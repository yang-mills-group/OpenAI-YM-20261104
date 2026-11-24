import YM.Trace.Fock.Amplitudes
/-!
Polynomial temperance of shell amplitudes constructed in `Fock.Amplitudes`. In
particular division on Fourier patches does not impose extra regularity.
-/
noncomputable section
namespace YM.Trace.Shell
open YM Boundary Filter MeasureTheory Function Set Complex
open scoped Topology BigOperators InnerProductSpace ENNReal Pointwise
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {m n : ℕ} (v : Test4 →L[ℂ] Sum m) (h : FieldImage v)
noncomputable def energy (x : Cords n) : ℝ := ∑ i : Fin n, ‖x i‖
@[fun_prop] lemma continuous_energy (n : ℕ) : Continuous (@energy n) := by unfold energy; fun_prop
lemma energy_nonneg (p : Cords n) : 0≤energy p := Finset.sum_nonneg (fun _ _=> norm_nonneg ..)
lemma time_equal (p : Cords n) : time (total p)= energy p := by unfold total; rw [show time= ⇑Mink.clockL from rfl,map_sum]; unfold energy; simp
lemma norm_ray_upper (p : Mom) : ‖ray p‖ ≤ 2*‖p‖ := (sq_le_sq₀ (by positivity) (by positivity)).mp (by rw [Mink.squares]; simp; nlinarith [norm_nonneg p])
lemma norm_total_upper (p : Cords n) : ‖total p‖ ≤ 2*energy p := (norm_sum_le ..).trans ((Finset.sum_le_sum (fun _ _=> norm_ray_upper _)).trans_eq (by rw [← Finset.mul_sum]; rfl))
lemma energy_upper (p : Cords n) : energy p ≤ n*‖p‖ := calc _ ≤ _ := Finset.sum_le_sum (fun i _=> norm_le_pi_norm p i)
                                                           _ = _ := by rw [Finset.sum_const]; simp

private lemma probe_available : ∃ f : Test4, CC f ∧ ∀ p:E4, ‖p‖ ≤ 3 → ‖plus f p‖ ≥ 1/2 := by
   have he := ((plus (initial E4)).continuous.tendsto 0).eventually (Metric.ball_mem_nhds _ (by norm_num : 0<(1/2:ℝ)))
   obtain ⟨s,hs,ht⟩ := Metric.mem_nhds_iff.mp he
   have h (p : E4) (hp : ‖p‖<s) : 1/2 ≤ ‖plus (initial E4) p‖ := by
       have hA := ht (by change p ∈ Metric.ball _ _; simpa using hp)
       rw [plus_initial] at hA
       have hB := norm_sub_norm_le (1:ℂ) (plus (initial _) p)
       rw [norm_one,← dist_eq_norm,dist_comm] at hB; change 1/2 ≤ ‖plus (initial E4) p‖; linarith [show dist (plus (initial E4) p) 1 < 1/2 from hA]
   let c := 4/s; have hc : 0<c := by dsimp [c]; positivity
   refine ⟨normalized (initial E4) c, normalized_CC initial_CC _, fun p hp=> ?_⟩
   rw [plus_normalized _ hc]
   apply h; rw [norm_smul, Real.norm_of_nonneg (by exact (inv_pos.mpr hc).le),← div_eq_inv_mul]
   exact (div_lt_iff₀ hc).mpr (by dsimp [c]; field_simp; linarith [hp])
private noncomputable def lowTest := Classical.choose probe_available
private lemma low_compact : CC lowTest := (Classical.choose_spec probe_available).1
private lemma low_lower (p:E4) (hp : ‖p‖ ≤ 3) : 1/2 ≤ ‖plus lowTest p‖ := (Classical.choose_spec probe_available).2 p hp

noncomputable def snapshot (r : ℝ) := normalized lowTest r
lemma snapshot_compact (r : ℝ) : CC (snapshot r) := normalized_CC low_compact _
lemma snapshot_large (r : ℝ) {p : Cords n} (hr : r>0) (hk : energy p ≤ r) : ‖plus (snapshot r) (total p)‖ ≥ 1/2 := by
      rw [snapshot, plus_normalized lowTest hr]; apply low_lower
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr|>.le), ← div_eq_inv_mul]
      exact (div_le_iff₀ hr).mpr ((norm_total_upper p).trans (by linarith))

noncomputable def scalarMass (n : ℕ) (p : Cords n) : ℝ := ‖fullWave v n p‖^2
@[fun_prop] lemma scalarMass_meas (n : ℕ) : Measurable (scalarMass v n) := by unfold scalarMass; exact ((fullWave_meas v ..).norm.pow_const _)
lemma scalarMass_ge (p : Cords n) : 0 ≤ scalarMass v n p := sq_nonneg (‖fullWave v n p‖)
noncomputable def eventMass (n : ℕ) : Measure (Cords n) := (νpow n).withDensity (fun p=> ENNReal.ofReal (scalarMass v n p))
noncomputable def below n (t : ℝ) := {p : Cords n | energy p ≤ t}
lemma below_meas (n:ℕ) (t:ℝ) : MeasurableSet (below n t) := measurableSet_le  (continuous_energy _).measurable measurable_const
lemma below_in (p : Cords n) : p ∈ below n (energy p) := by change energy p ≤ energy p; exact le_refl _
lemma below_upper {r:ℝ} (p:Cords n) (hr:‖p‖≤ r) : p∈below n (r*n) := (energy_upper p).trans (by simp_rw [mul_comm r]; gcongr)

include h in
lemma eventMass_norm (n : ℕ) (f : Test4) (hf : CC f) : (∫⁻ p, ‖plus f (total p)‖ₑ^2∂eventMass v n) = ‖v f n‖ₑ^2 := by
   have ht := fullWave_of_CC _ h _ hf n
   have hEq (x : Cords n) (hx : v f n x = plus f (total x) • fullWave v n x) : ‖v f n x‖^2 = scalarMass v n x * ‖plus f (total x)‖^2 := by
          rw [hx,norm_smul,mul_pow,mul_comm]; rfl
   have hv := lp_sq (v f n)
   unfold eventMass; rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
   simp only [← _root_.ofReal_norm, Pi.mul_apply,← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (scalarMass_ge _ _)]
   rw [hv]
   have hE (i : Cords n) := scalarMass v n i
   rw [lintegral_congr_ae (f:=fun i=> ENNReal.ofReal (scalarMass v n i * ‖plus f (total i)‖^2)) (g:=fun i=> ENNReal.ofReal (‖v f n i‖^2)) (μ:=νpow n) (ht.mono (fun i hi=> congr_arg ENNReal.ofReal (hEq i hi).symm)), ← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ..)).1 (Lp.memLp (v f n))) ?_]
   exact ae_of_all _ (fun x=> sq_nonneg _)
lemma massCost (f : Wave m n) (C : ℝ) : (∫⁻ p : Cords n, ENNReal.ofReal (C*‖f p‖^2) ∂νpow n) ≤ ENNReal.ofReal |C| * ENNReal.ofReal (‖f‖^2) := by
      have hi := memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ..)|>.1 (Lp.memLp f)
      calc _ ≤ (∫⁻ p:Cords n, ENNReal.ofReal (|C| * ‖f p‖^2) ∂νpow n) := lintegral_mono ?_
           _ = _ := ?_
      · exact fun x=> ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
      rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.const_mul hi _) (show 0 ≤ᵐ[νpow n] (fun p=> |C| * ‖f p‖^2) from ae_of_all _ (fun p=> by exact mul_nonneg (abs_nonneg C) (sq_nonneg _))), lp_sq, MeasureTheory.integral_const_mul, ← ENNReal.ofReal_mul (abs_nonneg _)] -- avoiding function mvar?
private lemma mass_le_sq (n : ℕ) (f : Wave m n) (t : ℝ) (c : ℝ) (hC : ∀ᵐ p ∂νpow n, p ∈ below n t → scalarMass v n p ≤ c*‖f p‖^2) :
      eventMass v n (below n t) ≤ ENNReal.ofReal |c| * ENNReal.ofReal (‖f‖^2) := by
      unfold eventMass; rw [withDensity_apply _ (below_meas ..)]
      calc (∫⁻ _ in _, _∂_) ≤ (∫⁻ p:Cords n in _, ENNReal.ofReal (c * ‖f p‖^2)∂νpow n) := lintegral_mono_ae ?_
           _ ≤ (∫⁻ p:Cords n, ENNReal.ofReal (c*‖f p‖^2)∂νpow n) := setLIntegral_le_lintegral _ _
           _ ≤ _ := massCost _ _
      · filter_upwards [Filter.Eventually.filter_mono (ae_mono (Measure.restrict_le_self)) hC,ae_restrict_mem (below_meas ..)] with p hc hp
        exact ENNReal.ofReal_le_ofReal (hc hp)
include h in
lemma mass_le (t : ℝ) (n : ℕ) (ht : t>0) : eventMass v n (below n t) ≤ ENNReal.ofReal 4 * ENNReal.ofReal (‖v (snapshot t) n‖^2) := by
      have hq := fullWave_of_CC v h (snapshot t) (snapshot_compact _) n
      convert (mass_le_sq v n (v (snapshot t) n) t 4 _) using 1
      · norm_num

      filter_upwards [hq] with p hp he
      simp_rw [hp,norm_smul,mul_pow, ← mul_assoc]; exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith [snapshot_large t ht (show energy p ≤ t from he)] : _)
include h in
lemma mass_le_one (t : ℝ) (n : ℕ) (ht : t>0) : eventMass v n (below n t) ≤ ENNReal.ofReal 4 * ENNReal.ofReal (‖v (snapshot t)‖^2) := (mass_le v h _ _ ht).trans
   (mul_le_mul_of_nonneg_left (by exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm (show (2:ℝ≥0∞) ≠ 0 by norm_num) ..) 2)) zero_le)
include h in
lemma mass_growth : ∃ P : ℕ, ∃ c : ℝ, ∀ n, Growth (eventMass v n) (ENNReal.ofReal (c*(n+1)^P)) P := by
   obtain ⟨s,A,hA,H⟩ := normalized_cost v lowTest
   refine ⟨2*s,4*A^2,?_⟩
   intro n r hr
   calc _ ≤ _ := measure_mono (show Metric.closedBall (0:Cords n) r ⊆ _ from fun p hp=> below_upper _ (show ‖p‖ ≤ r by simpa using hp))
        _ ≤ eventMass v n (below n (r*(n+1))) := measure_mono (by
           intro x hx; change energy x ≤ _; calc energy x ≤ r*n := hx
                                          _ ≤ r*(n+1) := by push_cast; nlinarith)
        _ ≤ _ := mass_le_one v h _ _ (by positivity : r*(n+1)>0)
        _ ≤ _ := ?_
   suffices H : 4*‖v (snapshot (r*(n+1)))‖^2 ≤ 4*A^2*(n+1)^(2*s) * r^(2*s) by
       exact (by rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_le_ofReal H)
   have hn : ‖v (snapshot (r*(n+1)))‖ ≤ A*(r*(n+1))^s := H _ (by exact (one_le_mul_of_one_le_of_one_le hr (by simpa)))
   refine (show _ ≤ 4*(A*(r*(n+1))^s)^2 from mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hn) (by positivity)).trans ?_
   exact (le_of_eq (by push_cast; rw [mul_pow,pow_mul,pow_mul,mul_pow, pow_right_comm r, ← pow_right_comm ((n:ℝ)+1) s 2]; ring))
include h in
lemma mass_tempered (n : ℕ) : Tempered (eventMass v n) := by
   obtain ⟨P,c,hc⟩ := mass_growth v h
   exact ⟨P, (c*(n+1)^P), hc n⟩

private lemma product_weight (p : Cords n) (k : ℕ) : weight k p ≤ ∏ i : Fin n, weight k (p i) := by
   rw [weight]; simp only [weight, Finset.prod_pow]
   let t : Fin n → ℝ := fun i=>1+‖p i‖
   let c := ∏ i, t i
   suffices ‖p‖ ≤ c-1 by exact pow_le_pow_left₀ (by positivity) (by linarith : 1+‖p‖≤c) _
   apply (pi_norm_le_iff_of_nonneg (sub_nonneg.mpr (by exact Finset.one_le_prod (fun i _ => by dsimp [t]; simp)))).2
   intro i
   have : t i≤c := (show ∏ i ∈ ({i}:Finset (Fin n)), t i=t i from Finset.prod_singleton ..).ge.trans (Finset.prod_le_prod_of_subset_of_one_le (s:={i}) (t:=Finset.univ)
     (f:=t) (Finset.subset_univ _) (fun _ _=> by dsimp [t]; positivity) (fun _ _ _=>by dsimp [t]; simp))
   dsimp [t] at this; linarith
include h in
lemma tempered_Lp (n : ℕ): ∃ P : ℕ, MemLp (fun p : Cords n => ‖fullWave v n p‖ / (1+‖p‖)^P) 2 (νpow n) := by
   obtain ⟨s,C,hC⟩ := mass_tempered v h n
   have hI : Integrable (fun x => (1+‖x‖)^(-(s+1:ℤ))) (eventMass v n) := by
       convert (hC.integrable_weight _ ENNReal.ofReal_lt_top) using 2
       change _ = (weight (s+1) _)⁻¹; unfold weight; rw [zpow_neg,show (s:ℤ)+1=(s+1:ℕ) from rfl,zpow_natCast]
   have hv := (integrable_withDensity_iff (μ:=νpow n) (f:=fun x=>ENNReal.ofReal (scalarMass v n x)) (by fun_prop) (by simp)).1 hI
   simp only [ENNReal.toReal_ofReal (scalarMass_ge ..)] at hv
   refine ⟨s+1,(memLp_two_iff_integrable_sq_norm (by apply Measurable.aestronglyMeasurable; exact ((fullWave_meas v _).norm).div (by fun_prop) )|>.2 ?_ )⟩ -- p?
   refine hv.mono' (((fullWave_meas v _ |>.norm.div (by fun_prop : Measurable (fun x:Cords n=>(1+‖x‖)^(s+1:ℕ)))).norm.pow_const 2).aestronglyMeasurable) (.of_forall (fun x => ?_))
   dsimp
   unfold scalarMass
   have ht := norm_nonneg (fullWave v n x); have hx : 0≤(1+‖x‖)^(s+1:ℕ) := by positivity
   rw [abs_of_nonneg (by positivity : 0 ≤ |‖fullWave v n x‖ / (1+‖x‖)^(s+1:ℕ)|^2),abs_of_nonneg (show 0 ≤ ‖fullWave v n x‖ / (1+‖x‖)^(s+1:ℕ) by positivity), zpow_neg]
   calc (‖fullWave v n x‖ / (1+‖x‖)^(s+1:ℕ) )^2 ≤ ‖fullWave v n x‖^2 / (1+‖x‖)^(s+1:ℕ) := by
                  rw [div_pow]; gcongr; simpa only [pow_one] using (pow_le_pow_right₀ (one_le_pow₀ (n:=s+1) (show (1:ℝ)≤1+‖x‖ from by linarith [norm_nonneg x])) one_le_two)
        _ = _ := by rw [div_eq_mul_inv,mul_comm]; congr 2
private noncomputable def P (n) := Classical.choose (tempered_Lp v h n)
def decay (x : Cords n) := ∏ i, (1+‖x i‖)^(-2:ℝ)
lemma decay_pos (x : Cords n) : 0≤decay x := Finset.prod_nonneg (fun _ _=> Real.rpow_nonneg (by positivity) _)
private lemma decay_Lp (n) : MemLp (@decay n) 2 (νpow n) := by
     unfold decay
     rw [memLp_two_iff_integrable_sq_norm (show AEStronglyMeasurable _ _ from Measurable.aestronglyMeasurable (by open Classical MeasureTheory in fun_prop))]; simp_rw [Real.norm_eq_abs,sq_abs,← Finset.prod_pow]
     apply Integrable.fintype_prod (f:=fun i p=> ((1+‖p‖)^((-2):ℝ))^2)
     exact fun i=> integrable_shell_arbitrary_bound _ (by fun_prop) 1 (4:ℝ) (by norm_num) (fun p => by
             have hx : 0≤1+‖p‖:=by positivity
             simp only [norm_pow,Real.norm_eq_abs, one_mul]; rw [abs_of_nonneg (Real.rpow_nonneg hx _)]
             exact le_of_eq (by rw [show ((1+‖p‖)^(-2:ℝ))^2=_ from (Real.rpow_natCast ((1+‖p‖)^(-2:ℝ)) 2).symm, ← Real.rpow_mul hx (-(2:ℝ)) ((↑(2:ℕ)):ℝ), show (-(2:ℝ)) * ((↑(2:ℕ)):ℝ) = -4 by norm_num])) -- rpow_two all terms
include h in
private lemma moment_decay (n) : Integrable (fun x => ‖fullWave v n x‖ / (1+‖x‖)^(P v h n) * decay x) (νpow n) := (Classical.choose_spec (tempered_Lp v h n)).integrable_mul (decay_Lp ..)
noncomputable def packing (x:Cords n) (k : ℕ) := ∏ i, ((weight k (x i)))⁻¹
lemma packing_pos (x:Cords n) (k) : 0≤packing x k := Finset.prod_nonneg (fun i _=> inv_nonneg.mpr (weight_pos ..|>.le))
@[fun_prop] lemma packing_meas (k) : Measurable (fun x : Cords n=> packing x k) := by unfold packing weight; fun_prop
lemma packing_mul (x : Cords n) (k s) : packing x (s+k) = packing x s * packing x k := by unfold packing; simp_rw [weight,pow_add,mul_inv,Finset.prod_mul_distrib]
include h in
lemma all_moments (N l : ℕ) : ∃ k : ℕ, Integrable (fun x : Cords N => ‖fullWave v N x‖ * weight l x * packing x k ) (νpow N) := by
    let p := P v h N
    have hp := moment_decay v h N
    have hm (x : Cords N) : packing x 2=decay x := Finset.prod_congr rfl (fun i _ => by unfold weight; rw [Real.rpow_neg (by positivity), Real.rpow_two])
    refine ⟨l+p+2,hp.mono' ((((fullWave_meas v ..|>.norm).mul (by unfold weight; fun_prop : Measurable (fun x:Cords N=> weight l x))).mul (packing_meas ..)).aestronglyMeasurable) (.of_forall fun x => ?_)⟩
    have hx (k : ℕ) := weight_pos k x
    rw [norm_mul, norm_mul, norm_norm,Real.norm_of_nonneg (packing_pos ..), Real.norm_of_nonneg (by unfold weight; positivity)]
    unfold P at p ⊢
    change _ ≤ ‖fullWave v N x‖ / weight p x * decay x
    suffices hm : weight l x * packing x (l+p+2) ≤ (weight p x)⁻¹ * decay x by
         rw [mul_assoc,div_eq_mul_inv, mul_assoc]; exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    rw [packing_mul x 2 _]; -- applies s+k
    change weight l x * (packing x (l+p) * packing _ 2) ≤ _
    rw [hm, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (le_of_mul_le_mul_right (a:=weight p x) (c:=(weight p x)⁻¹) ?_ (weight_pos ..)) (decay_pos x)
    rw [mul_comm (weight l x),mul_assoc,inv_mul_cancel₀ (weight_pos p x |>.ne')]
    have HE : ∀ (x : Cords N), packing x (l+p) * ∏ i, weight (l+p) (x i) = 1 := by
        intro x; unfold packing; rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one (fun _ _=> inv_mul_cancel₀ (weight_pos ..|>.ne'))
    rw [← HE]; apply mul_le_mul_of_nonneg_left _ (packing_pos ..); change _≤_
    rw [show weight l x * weight p x= weight (l+p) x by unfold weight; rw [pow_add]]; exact product_weight ..
end YM.Trace.Shell
