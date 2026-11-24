import YM.UVNext.COUPLING_RESET.Tuning

/-!
# Real finite-history β response, an actual sufficient comparison for inverse tuning

Vary **all** kernels and the normalized bare density along a straight line of real stepwise
inverse coupling vectors. No changes of levels/thresholds/prescriptions. Relates a *relative*
kinetic and activity signal on these quantities (much stronger than absolute error estimates)
to uniqueness of the bare value on any controlled family of admissible real trajectories.
Does not presuppose a holomorphic extension of hard selectors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open MeasureTheory Push.BetaTransport UVNext.CouplingReset Lattice Wilson RG RG.Shoot Function Set Filter Gibbs
open scoped Classical Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge} (a : Levels G) (p N : ℕ) (b : ℕ → ℝ)

private lemma wilsonEstimate (n : Side) : EnergyEstimate (energy (G:=G) (n:=n)) (wilsonCap n) := by
  refine ⟨energy_cont.measurable,energy_nonneg,fun U=> ?_,?_⟩
  · unfold energy; simpa only [wilsonCap,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (G.price_range (faceValue U i)).2))
  unfold wilsonCap; positivity

variable (r : ℕ → ℝ)
lemma normalized_top : normalizedVacuum a p N b N le_rfl = tilt (prior G _) energy (b N) := by
  unfold normalizedVacuum; rw [propagate_top]; funext x; simp only [smul_eq_mul,Pi.mul_apply,mul_one]
lemma normalized_down {m : ℕ} (h : m < N) : normalizedVacuum a p N b m h.le=
    (a.clock.op m p).push (b (m+1)) (normalizedVacuum a p N b (m+1) h) := by
  unfold normalizedVacuum propagate; exact Nat.decreasingInduction_succ_left _ _ h _
lemma response_down {m : ℕ} (h : m < N) : response a p N b (fun _=> (1:ℝ)) r m h.le=
    (a.clock.op m p).push (b (m+1)) (response a p N b (fun _=> (1:ℝ)) r (m+1) h) +
      r (m+1) • pushSlope (a.clock.op m p) (b (m+1)) (normalizedVacuum a p N b (m+1) h) := by
  unfold response; exact Nat.decreasingInduction_succ_left _ _ h _
lemma bill_down {m : ℕ} (h : m < N) : bill a p N r m h.le=bill a p N r (m+1) h + ‖r (m+1)‖ * noiseCap (a.clock.op m p) :=
    Nat.decreasingInduction_succ_left _ _ h _

lemma normalized_full {m : ℕ} (hm : m≤N) : Integrable (normalizedVacuum a p N b m hm) (prior G _) ∧
    (∀ x, 0 < normalizedVacuum a p N b m hm x) ∧ (∫ x, normalizedVacuum a p N b m hm x ∂prior G _) = 1 := by
  induction hm using Nat.decreasingInduction with
  | self => rw [normalized_top]; have h := wilsonEstimate (G:=G) (a.S.side N p); exact ⟨h.tilt_integrable _,fun x => h.tilt_pos (b N) x,h.total _⟩
  | of_succ i hi ih =>
    rcases ih with ⟨hint,hz,he⟩
    rw [normalized_down a p N _ hi]; let S := a.clock.op i p
    have hB := a.transition_mass i p (b (i+1))
    refine ⟨((S.push_integrand hB _ hint).integral_prod_right),fun x=> ?_,(S.push_integral hB _ hint).trans he⟩
    let F y := S.density (b (i+1)) y x * normalizedVacuum a p N b (i+1) hi y
    have he y : 0 < S.density (b (i+1)) y x := lt_of_lt_of_le (inv_pos.mpr (noiseCost_pos S _)) ((density_bounds S (a.blocks i p).branches (le_refl |b (i+1)|) y x).1)
    have hF : Function.support F=univ := Set.eq_univ_of_forall fun _=> (mul_pos (by apply he) (hz _)).ne'
    exact (integral_pos_iff_support_of_nonneg (f:=F) (fun _=> (mul_pos (by apply he) (hz _)).le) (S.push_slice hB _ _ hint)).mpr (by rw [hF,measure_univ]; exact zero_lt_one)

lemma response_bound {m : ℕ} (hm : m≤N) : 0 ≤ bill a p N r m hm ∧ Integrable (response a p N b (fun _=> (1:ℝ)) r m hm) (prior G _) ∧
    ∀ x, ‖response a p N b (fun _=> (1:ℝ)) r m hm x‖ ≤ bill a p N r m hm * (normalizedVacuum a p N b m hm x) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [normalized_top,response_top,bill_top]
    have h := wilsonEstimate (G:=G) (a.S.side N p)
    simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply,mul_one]
    let n := a.S.side N p; let μ := prior G n
    refine ⟨mul_nonneg (norm_nonneg _) h.cap, (h.tilt_integrable (μ:=μ) (b N)|>.const_mul (r N*mean μ energy (b N))
       |>.sub ((h.tilt_integrable (μ:=μ) (b N)).mul_bdd h.measurable.aestronglyMeasurable (Eventually.of_forall h.norm_le) |>.const_mul (r N))).congr
       (Eventually.of_forall (fun y=> by change r N * mean μ energy (b N) * tilt μ energy (b N) y - r N * (tilt μ energy (b N) y * energy y) = r N * ((tiltSlope μ energy (b N) y) * 1); unfold tiltSlope; ring)),fun x=>?_⟩
    rw [norm_mul,tiltSlope,norm_mul]
    have ht := Real.norm_of_nonneg (h.tilt_pos (μ:=μ) (b N) x |>.le)
    change ‖tilt (prior G (a.S.side N p)) energy (b N) x‖ = _ at ht; rw [ht]
    have hh := h.mean_bound (μ:=prior G (a.S.side N p)) (b N)
    have he := h.bound x; have hx := h.nonneg x
    have hz : ‖mean μ energy (b N)-energy x‖ ≤ wilsonCap n := abs_le.mpr (by change _ ≤ mean μ energy (b N)-energy x ∧ mean μ energy (b N)-energy x ≤ _; change 0 ≤ mean μ energy (b N) ∧ mean μ energy (b N) ≤ _ at hh; dsimp [n,μ] at *; constructor <;> linarith)
    unfold μ n at hz
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (h.tilt_pos _ x|>.le)) (norm_nonneg _)).trans_eq (by ring)
  | of_succ k hk ih =>
    rw [response_down a _ _ _ _ hk,normalized_down a _ _ _ hk,bill_down a _ _ _ hk]
    let S := a.clock.op k p; have hS := a.transition_mass k p (b (k+1)); have hB := (a.blocks k p).branches
    have hz := normalized_full a p N b hk
    refine ⟨add_nonneg ih.1 (by have := noiseCap_nonneg S; change 0 ≤ ‖r (k+1)‖ * noiseCap S; positivity), ((S.push_integrand hS _ ih.2.1).integral_prod_right|>.add
      ((pushSlope_integrable S hB hz.1 _).const_mul _)),fun x=>?_⟩
    let q := b (k+1); let t := r (k+1); let u := response a p N b (fun _=> (1:ℝ)) r (k+1) hk; let F := normalizedVacuum a p N b (k+1) hk
    change ‖S.push q u x+t*pushSlope S q F x‖ ≤ _
    have h1 := show ‖S.push q u x‖ ≤ bill a p N r _ hk * S.push q F x from by
      unfold StepData.push; simp only [smul_eq_mul]; apply (norm_integral_le_integral_norm _).trans
      rw [← integral_const_mul]
      apply integral_mono ((S.push_slice hS x u ih.2.1).norm) ((hz.1.bdd_mul (c:=noiseCost S |q|)
        (((slice_estimate S hB x).measurable q).aestronglyMeasurable) (Eventually.of_forall (fun y=>
            Real.norm_of_nonneg (hS.positive y x)|>.trans_le ((density_bounds S hB le_rfl y x).2)))).const_mul (bill a p N r (k+1) hk))
      intro y
      change ‖S.density (b (k+1)) y x * u y‖ ≤ _
      rw [norm_mul,Real.norm_of_nonneg (hS.positive y x)]
      exact (mul_le_mul_of_nonneg_left (ih.2.2 y) (hS.positive y x)).trans_eq (by dsimp [S,q]; ring)
    apply (norm_add_le ..).trans
    rw [norm_mul,add_mul]
    apply add_le_add h1
    change ‖t‖ * ‖pushSlope S q F x‖ ≤ (‖t‖*noiseCap S)*S.push q F x
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (pushSlope_norm_le S hB hz.1 x q).trans_eq (by congr; funext y; exact Real.norm_of_nonneg ((hz.2.1 y).le))


/-- Parameter variation acts on the full bare Wilson law and every intervening true block
kernel. The price used to justify differentiation here by itself need NOT be uniform or small.
-/
lemma read_deriv {m : ℕ} (hm : m ≤ N) (b' : BetaCurve) (hd : ∀ k, ∀ z : ℝ, HasDerivAt (fun w=> b' w k) (r k) z)
    (x : Config G (a.S.side m p)) (z : ℝ) : HasDerivAt (fun w => normalizedVacuum a p N (b' w) m hm x)
    (response a p N (b' z) (fun _=>1) r m hm x) z := by
  induction hm using Nat.decreasingInduction generalizing z with
  | self =>
    simp_rw [normalized_top, response_top]
    simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply,mul_one]
    exact ((wilsonEstimate _ |>.tilt_hasDerivAt (μ:=prior G (a.S.side N p)) _ x).comp z (hd N z)).congr_deriv (mul_comm ..)
  | of_succ k hk ih =>
    have hi (w) := normalized_full a p N (b' w) hk
    let S := a.clock.op k p
    let q (w:ℝ) : ℝ := b' w (k+1)
    have hb := (slice_estimate S (a.blocks k p).branches x)
    simp_rw [normalized_down a _ _ _ hk, response_down a _ _ _ _ hk]
    let F (w:ℝ) := normalizedVacuum a p N (b' w) (k+1) hk
    let u (w:ℝ) := response a p N (b' w) (fun _=>(1:ℝ)) r (k+1) hk
    let I (w:ℝ) := fun y => S.density (q w) y x * F w y
    let dI (w:ℝ) := fun y => S.density (q w) y x * u w y + densitySlope S (q w) y x * r (k+1) * F w y
    let μ := prior G (a.S.side (k+1) p)
    have hr (w:ℝ) := response_bound a p N (b' w) r hk
    have h1' (w:ℝ) : Integrable (fun y=> S.density (q w) y x * u w y) μ := hb.smul_integrable _ (hr w).2.1
    have h2' (w:ℝ) : Integrable (fun y=>densitySlope S (q w) y x * r (k+1) * F w y) μ :=
      (hb.slope_integrable (q w) (hi w).1 |>.const_mul (r (k+1)) |>.congr (Eventually.of_forall fun y=> show _ from by change r _ * (_ * F w y) = _; ring))
    have he (w:ℝ) (y) : HasDerivAt (fun z=>I z y) (dI w y) w :=
      (((hb.has _ y).comp w (hd _ w)).mul (ih y w)).congr_deriv (add_comm _ _)
    -- obtain a local dominating bound uniform over configurations
    have hv : ∀ {j : ℕ} (hj : j ≤ N), ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ w in 𝓝 z,
        ∀ y, ‖normalizedVacuum a p N (b' w) j hj y‖ ≤ A := by
      intro j hj; rcases eq_or_lt_of_le hj with rfl | hj'
      · refine ⟨cost (wilsonCap (a.S.side j p)) (|b' z j|+1) * cost (wilsonCap (a.S.side j p)) (|b' z j|+1), (mul_self_nonneg _),?_⟩
        filter_upwards [(hd j z).continuousAt (eventually_abs_bound (b' z j))] with w hw
        intros y
        rw [normalized_top,Real.norm_of_nonneg ((wilsonEstimate _).tilt_pos _ y |>.le)]; exact ((wilsonEstimate _).tilt_bounds hw y).2
      let q' := a.clock.op j p
      refine ⟨noiseCost q' (|b' z (j+1)|+1), (noiseCost_pos ..).le,?_⟩
      filter_upwards [(hd (j+1) z).continuousAt (eventually_abs_bound _)] with w hw
      intros y; rw [Real.norm_of_nonneg (((normalized_full a p _ _ hj).2.1 y).le)]
      let e := normalizedVacuum a p N (b' w) (j+1) hj'; let B := noiseCost q' (|b' z (j+1)|+1)
      rw [normalized_down a _ _ _ hj']; change _ ≤ B; rw [show B=∫ t, B*e t ∂prior G _ by rw [integral_const_mul,(normalized_full ..).2.2, mul_one]]
      exact integral_mono (q'.push_slice (a.transition_mass ..) y e (normalized_full ..).1) ((normalized_full ..).1.const_mul B)
        (fun _=> mul_le_mul_of_nonneg_right ((density_bounds _ (a.blocks j p).branches hw _ _).2) ((normalized_full ..).2.1 _|>.le))
    obtain ⟨C,hC,hbc⟩ := hv hk
    let B := bill a p N r (k+1) hk; let H := noiseCost S (|q z|+1)
    have hdI : ∀ᶠ w in 𝓝 z,∀ y, ‖dI w y‖ ≤ H * (B * C) + noiseCap S * H * ‖r (k+1)‖ * C := by
      filter_upwards [(hd _ z).continuousAt (eventually_abs_bound _),hbc] with w hw hF
      intro y; refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; apply mul_le_mul (b:=H)
        · exact (Real.norm_of_nonneg (hb.nonneg ..)).trans_le (hb.le hw y)
        · exact ((hr w).2.2 y).trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hF y)) (hr w).1)
        exact norm_nonneg _
        exact (noiseCost_pos ..).le
      rw [norm_mul,norm_mul]
      apply mul_le_mul (d:=C)
      · exact (mul_le_mul_of_nonneg_right ((hb.slope ..).trans (mul_le_mul_of_nonneg_left (hb.le hw y) (hb.cap))) (norm_nonneg _))
      exact hF y
      exact norm_nonneg _
      exact mul_nonneg (mul_nonneg (noiseCap_nonneg S) (noiseCost_pos ..).le) (norm_nonneg _)
    let C₁ := H * (B * C) + noiseCap S * H * ‖r (k+1)‖ * C
    let K : Set ℝ := {w | ∀ y, ‖dI w y‖ ≤ C₁}
    have hI (w:ℝ) : Integrable (I w) μ := hb.smul_integrable _ (hi w).1
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=K) (F':=dI) (bound:=fun _=> C₁) (μ:=μ) (F:=I) (x₀:=z) hdI
      (Eventually.of_forall (fun w=> (hI w).1)) (hI z) ((h1' z|>.add (h2' z)).1)
      (Eventually.of_forall fun y w (hw : w ∈ K) => hw y) (integrable_const C₁) (Eventually.of_forall (fun y w _ => he w y))).2.congr_deriv ?_
    have hx₂ : Integrable (fun y=> densitySlope S (q z) y x * F z y) μ := hb.slope_integrable _ (hi z).1
    unfold dI
    change (∫ y, (_+_) ∂μ)= _
    rw [show (fun y=> S.density (q z) y x * u z y + densitySlope S (q z) y x * r (k+1) * F z y)= fun y=> (S.density (q z) y x * u z y + r (k+1) * (densitySlope S (q z) y x * F z y)) from funext fun _=> by ring]
    rw [integral_add (h1' z) (hx₂.const_mul _),integral_const_mul]; rfl


lemma contrast_has_change (b' : BetaCurve) {m : ℕ} (h : m ≤ N) (u : Config G (a.S.side m p)) (x y z : ℝ) :
    HasDerivAt (contrast (normRead a p N (join b' x y) m h) u)
      (ratioChange a p N (join b' x y) (b' y-b' x) h u z) z := by
  have hd k w : HasDerivAt (fun w=> join b' x y w k) ((b' y - b' x) k) w := by
    simpa only [UVNext.CouplingReset.join,Pi.sub_apply,one_mul] using (((hasDerivAt_id' w).mul_const (b' y k - b' x k)).add_const (b' x k))
  have he (v : Config G (a.S.side m p)) := read_deriv a p N (b' y - b' x) h _ hd v z
  have hPos := (normalized_full a p N (join b' x y z) h).2.1
  unfold contrast ratioChange normRead
  exact ((he 1).log (hPos 1|>.ne')).sub ((he u).log (hPos u|>.ne'))

open Precision Input RG.Supply
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

lemma scanned (R : Recipe a) (u : Trail a p) (h : Competes R p N 0 u) {m : ℕ} (hm : m ≤ N) : ∀ x,
    (u m).eval x / partition G (a.S.side N p) (u N).beta = normalizedVacuum a p N (fun i=> (u i).beta) m hm x := by
  induction hm using Nat.decreasingInduction with
  | self =>
    intro x; rw [normalized_top,h.fromTop.raw]
    change bare (u N).beta x / _ = (Gibbs.Z (prior G _) energy (u N).beta)⁻¹ * factor energy (u N).beta x
    rw [div_eq_inv_mul]; rfl
  | of_succ k hk ih =>
    intro x; rw [normalized_down a _ _ _ hk,(h.persists k (Nat.zero_le _) hk).link]
    unfold StepData.push; rw [←integral_div]; exact integral_congr_ae (Eventually.of_forall fun y=> by
      simp only [smul_eq_mul,← ih y,mul_div_assoc])

set_option maxHeartbeats 500000 in
lemma tuned_contrast (u : Trail B.a p) (h : Competes B.bake p N 0 u) {m : ℕ} (hm : m ≤ N)
    (v : Config G (B.a.S.side m p)) (hf : flags (B.a.budget m).threshold v = ∅) : let q := (fun _ : ℝ => normalizedVacuum B.a p N (fun i => (u i).beta) m hm)
    contrast (q : ℝ → _ → ℝ) v 0 = (u m).beta * key B N m v + (B.bake.path N m).inChannels (B.a.params m).clip (B.a.budget m) 0 v +
      (u m).activities.additive (B.a.budget m) v := by
  intro q
  have hZ := h.prices _ (Nat.zero_le _) hm |>.1
  have hc' : q = fun _ z => (u m).eval z / partition G (B.a.S.side N p) (u N).beta := by
    funext _ z; exact (scanned B.a p N B.bake u h hm z).symm
  unfold contrast; rw [hc']; dsimp
  have he z : 0 < (u m).eval z := by
    have hp := (normalized_full B.a p _ (fun i=> (u i).beta) hm).2.1 z; rw [← scanned B.a p N B.bake u h] at hp
    exact pos_of_mul_pos_left (div_eq_mul_inv ((u m).eval z) _ ▸ hp) (inv_pos.mpr (partition_pos _)).le
  rw [Real.log_div (he 1).ne' (partition_pos _).ne',Real.log_div (he v).ne' (partition_pos _).ne']
  have ha := hZ.valid.labels.regular.at_flat
  have hF : flags (u m).p.threshold v = ∅ := hZ.point ▸ hf
  rw [show (u m).eval 1 = Real.exp ((u m).exponent 1) from ?_,show (u m).eval v = Real.exp ((u m).exponent v) from ?_, Real.log_exp,Real.log_exp]
  rotate_left
  · unfold Rep.eval; rw [Activities.gas_one _ _ hF, mul_one]
  · unfold Rep.eval; rw [Activities.gas_one _ _ (flags_one _), mul_one]
  unfold Rep.exponent; rw [additive_one ha,hZ.point,hZ.path,hZ.clip,channels_split 1,channels_split v, kinetic_one,loop_one,mul_zero]; unfold key; abel


/- Relative signal suffices for injectivity of the terminal bare value from the lower target.
We don't vary the representative itself along a complex trajectory to make this comparison;
it uses entire bands of possible actual histories as endpoints. -/
set_option maxHeartbeats 800000 in
lemma signal_inverse {m : ℕ} {s : Set ℝ} (F : ℝ → Trail B.a p)
    (hs : ∀ z∈s, Competes B.bake p N 0 (F z)) (U : ∀ i, Config G (B.a.S.side i p)) (h : Signal B p N m F s U)
    {x y : ℝ} (hx : x∈s) (hy : y∈s)
    {i : ℕ} (hi : m ≤ i) (hi' : i ≤ N) (hd : knob F x m=knob F y m) : knob F x i=knob F y i := by
  induction i,hi using Nat.le_induction with
  | base => exact hd
  | succ k hk ih =>
    have hkn : k < N := hi'
    specialize ih hkn.le
    let Δ := knob F y (k+1)-knob F x (k+1)
    let κ := key B N k (U k)
    let E := fun t : ℝ => (F t k).activities.additive (B.a.budget k) (U k)
    suffices Δ * κ = 0 by exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ((h.kinetic k hk hi').ne'))).symm
    let q' := UVNext.CouplingReset.join (knob F) x y
    let c := contrast (normRead B.a p N q' k hkn.le) (U k)
    have hu (z) : HasDerivAt c (ratioChange B.a p N q' (knob F y-knob F x) hkn.le (U k) z) z :=
      contrast_has_change B.a ..
    have hdif : c 1 - c 0 = E y-E x := by
      have hv z hz := tuned_contrast p N B (F z) (hs z hz) hkn.le (U k) (h.weak k hk hi')
      have h1 : c 1 = (F y k).beta*κ + (B.bake.path N k).inChannels (B.a.params k).clip (B.a.budget k) 0 (U k) + E y := by
        convert hv y hy using 1
        dsimp [c,q',contrast,normRead]; rw [join_one]; rfl
      have h0 : c 0 = (F x k).beta*κ + (B.bake.path N k).inChannels (B.a.params k).clip (B.a.budget k) 0 (U k) + E x := by
        convert hv x hx using 1
        dsimp [c,q',contrast,normRead]; rw [join_zero]; rfl
      have hβ : (F x k).beta=(F y k).beta := ih
      rw [h1,h0,hβ]; ring
    let f z := z* (Δ*κ) - c z
    have hf z : HasDerivAt f (Δ*κ - ratioChange B.a p N q' (knob F y-knob F x) hkn.le (U k) z) z :=
      (hasDerivAt_id' z |>.mul_const (Δ*κ) |>.sub (hu z)).congr_deriv (by rw [one_mul])
    have he : ‖f 1 - f 0‖ ≤ |Δ| * κ / 4 * ‖(1:ℝ)-0‖ := Convex.norm_image_sub_le_of_norm_deriv_le (s:=Icc (0:ℝ) 1) (fun z _ => (hf z).differentiableAt)
      (fun z hz=> by rw [(hf z).deriv]; exact h.error k hk hi' x hx y hy z hz) (convex_Icc ..) ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩
    have hK := h.kinetic k hk hi'
    have h' : |E y-E x| ≤ |Δ| * κ/4 := h.activities k hk hi' x hx y hy
    have hT := abs_sub_abs_le_abs_sub (Δ*κ) (c 1 - c 0)
    rw [abs_mul,abs_of_pos (by exact hK : 0<κ),hdif] at hT
    simp only [sub_zero,norm_one,mul_one,show f 1 - f 0 = Δ*κ-(E y-E x) from by unfold f; rw [← hdif,one_mul,zero_mul,zero_sub, sub_neg_eq_add]; ring,Real.norm_eq_abs] at he
    apply mul_eq_zero.mpr; left; apply abs_nonpos_iff.mp; nlinarith

end YM.UVExt
