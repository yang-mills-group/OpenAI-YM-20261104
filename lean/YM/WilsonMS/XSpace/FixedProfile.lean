import YM.WilsonMS.Regulator.Treed
/-!
# Test integrals in the aligned (still MS-stamped) basis

Use stair-step integrator from XSpace and the quantitative Hölder improvement
for momentum kernels. Fixed C1 compact seminorm. Also point profile error at
actual shifted locations in the physical chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Set Filter MeasureTheory Real Finset Metric
open MS MS.Latch MS.Tone MS.Landau MS.Landau.Detect MS.Plane MS.Land MS.High MS.Dial MS.Rake MS.Tide
  MS.Menus
open XSpace XSpace.Expense XSpace.TestBudget XSpace.Cirrus Lattice
open Fiscal BMenu Rider
open scoped Topology ContDiff BigOperators
variable {n d : ℕ} {G : Gauge}
local notation "𝕄" => XSpace.Mesh

lemma apart (i : Fin n) (p q : Points n) : ‖VisitH.actual p i - VisitH.actual q i‖ ≤ dist p q := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  exact (PiLp.norm_apply_le ((p - q) i) k).trans (PiLp.norm_apply_le (p - q) i)

abbrev FareP (e : ℝ) (p : 𝕄) :=
  exp (-e * height p)

lemma fare_lower (h p : ℝ) (ht : p ≤ h) : ∀ᶠ i in Front, FareP h i ≤ FareP p i :=
  frontier.smaller.mono
    (fun i hi => exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg ht) (height0 (p := i) hi)))
variable (f : Fin n → Glyph (Ensure.deck G) d) {M : Booked (Ensure.deck G)} (F : MS_Data G M)
variable (μ : ℝ) (j : ℕ) {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n)
local notation "Y'" => answers f F μ j

lemma act_inj (p : Points n) (hp : p ∈ conf n) : Injective (VisitH.actual p) :=
  Theater.out.injective.comp (show Injective p.ofLp from hp)

lemma cont_answer (x : Points n) (hx : x ∈ conf n) : ContinuousAt Y' x :=
  (Dial.contin F (profileK f) (VisitH.actual x) (act_inj x hx) Finset.univ j μ).1.comp
    ((continuous_pi (fun k => actC (n := n) k)).continuousAt)
include hK hc

lemma answers_cost :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖Y' x‖ ≤ C) ∧
      ∃ a : ℝ,
        0 < a ∧
          ∃ D : ℝ,
            0 ≤ D ∧
              ∀ x ∈ K,
                ∀ y ∈ K, ∀ r : ℝ, 0 ≤ r → dist x y ≤ exp (-r) → ‖Y' x - Y' y‖ ≤ D * exp (-a * r) := by
  let H := group_visit hK hc μ (fun i : K => show i.val ∈ K from i.property)
  obtain hP := (Climb.holderMS H (profileK f) F).2 Finset.univ j
  obtain ⟨⟨C, hC, hV⟩, a, ha, D, hD, hB⟩ := Climb.Traced.exported hP
  exact
    ⟨⟨C, hC, fun i hi => hV ⟨i, hi⟩⟩, a, ha, D, hD, fun x hx y hy r hr ht =>
      hB ⟨x, hx⟩ ⟨y, hy⟩ r hr (fun w => (apart w x y).trans ht)⟩

lemma felt_shape :
    ∃ a : ℝ,
      0 < a ∧
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ (t : Test n),
              tsupport t ⊆ K →
                ∀ b,
                  TestBudget.Bound t b →
                    ∀ x y : Points n,
                      ∀ r : ℝ,
                        0 ≤ r →
                          dist x y ≤ exp (-r) → ‖Damp t Y' x - Damp t Y' y‖ ≤ b * C * exp (-a * r) := by
  obtain ⟨⟨C, hC, h⟩, a, ha, D, hD, hT⟩ := answers_cost f F μ j hK hc
  let k := min a 1
  refine ⟨k, lt_min ha (by linarith), C + D, by positivity, fun t hs b hb x y r hr hv => ?_⟩
  have hu := bound_nonneg t hb
  let U := exp (-k * r)
  have hh : 0 < U := exp_pos _
  have hF z (hK : z ∉ K) : t z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hK (hs h))
  have hX : ‖t x - t y‖ ≤ b * exp (-r) := by
    refine
      ((convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_fderiv_le
            (fun x _ => t.contDiff |>.differentiable (by simp) x) (fun x _ => (hb x).2)
            (Set.mem_univ y) (Set.mem_univ x)).trans
        ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hv hu
  have hR : exp (-r) ≤ U := by
    refine exp_monotone ?_
    have hm : k ≤ 1 := min_le_right ..
    nlinarith
  have hA : exp (-a * r) ≤ U :=
    exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)) hr)
  have hW := hX.trans (mul_le_mul_of_nonneg_left hR hu)
  have hL (i : Points n) (v : ℂ) (hv : ‖v‖ ≤ b * U) (hp : i ∈ K) : ‖v * Y' i‖ ≤ b * (C + D) * U := by
    rw [norm_mul]
    apply (mul_le_mul hv (h i hp) (norm_nonneg _) (by positivity)).trans
    rw [mul_right_comm b (C + D)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold Damp
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ K
  by_cases hy : y ∈ K
  · rw [show t x * Y' x - t y * Y' y = (t x - t y) * Y' y + t x * (Y' x - Y' y) from (by ring)]
    apply (norm_add_le ..).trans
    rw [norm_mul, norm_mul]
    apply
      (add_le_add (mul_le_mul hW (h y hy) (norm_nonneg _) (by positivity))
          (mul_le_mul (hb x).1 (le_trans (hT x hx y hy r hr hv) (mul_le_mul_of_nonneg_left hA hD))
            (norm_nonneg _) hu)).trans_eq
    unfold U
    ring
  · rw [hF y hy, sub_zero] at hW
    rw [hF y hy, zero_mul, sub_zero]
    exact hL x _ hW hx
  rw [hF x hx, zero_mul, zero_sub, norm_neg]
  by_cases he : y ∈ K
  · rw [hF x hx, zero_sub, norm_neg] at hW
    exact hL y _ hW he
  rw [hF y he, zero_mul, norm_zero]
  positivity
omit hK hc

lemma shape_cont : ContinuousOn Y' (conf n) := fun x hx =>
  (cont_answer f F μ j x hx).continuousWithinAt

lemma shaped_legal (t : Test n) : Integrable (Damp t Y') :=
  can_pay t _ (conf_open n) (shape_cont f F μ j) t.tsupport_subset (Set.Subset.refl _)

lemma stair_fee : ∀ᶠ p in Front, (4 * n : ℝ) * p.spacing ≤ exp (-(height p / 2)) := by
  let v (k : ℝ) := exp ((1 / 2 : ℝ) * k)
  have ht : Tendsto (fun p => v (height p)) Front atTop :=
    tendsto_exp_atTop.comp ((attained frontier).const_mul_atTop (by norm_num : 0 < (1 / 2 : ℝ)))
  filter_upwards [ht.eventually_ge_atTop (4 * n : ℝ)] with p hp
  refine (mul_le_mul_of_nonneg_right hp p.positive.le).trans_eq ?_
  unfold v
  rw [small_p, ← exp_add]
  congr 1
  ring
include hK hc

lemma reference_bound :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ (t : Test n), tsupport t ⊆ K → ∀ b, TestBudget.Bound t b → ‖t.applyTo Y'‖ ≤ b * C := by
  obtain ⟨C, hC, h⟩ := answers_cost f F μ j hK hc |>.1
  refine ⟨C * volume.real K, mul_nonneg hC ENNReal.toReal_nonneg, fun t ht b hb => ?_⟩
  rw [Test.applyTo, ←
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun hv => hx (ht hv))) _),
    ← mul_assoc]
  exact
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx =>
      (norm_mul_le ..).trans (mul_le_mul (hb x).1 (h x hx) (norm_nonneg _) (bound_nonneg t hb))
variable (hG : G.Simple) (V : XSpace.Initialize G) (A : Prescription (Ensure.deck G))
  (hA : Installed V F A)
include hA hG

lemma layPoint :
    ∃ a : ℝ,
      0 < a ∧
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ᶠ p in Front,
              ∀ f' : Test n,
                tsupport f' ⊆ K →
                  ∀ b,
                    TestBudget.Bound f' b →
                      ‖amended V μ A p d j n f' (glow ∘ f) - f'.applyTo Y'‖ ≤ b * C * FareP a p := by
  obtain ⟨a, ha, C, hC, hi⟩ := felt_shape f F μ j hK hc
  obtain ⟨B, hB, hL⟩ := picture V μ A f _ F hG hA hK hc j
  let k := min (a / 2) mildG
  have hk : 0 < k := lt_min (by positivity) mild_p
  obtain ⟨r, h⟩ := (hK.image continuous_norm).bddAbove
  let U := closedBall (0 : Points n) (r + 4 * n)
  let s := volume.real U
  have hs : 0 ≤ s := ENNReal.toReal_nonneg
  let Y (p : Sample n) := note V μ A f p j
  have hE := fare_lower (a / 2) k (min_le_left ..)
  have hV := fare_lower mildG k (min_le_right ..)
  refine ⟨k, hk, (B + C) * s, by positivity, ?_⟩
  filter_upwards [hE, hV, hL, stair_fee (n := n), frontier.smaller,
    XSpace.Mesh.fits_compact frontier U (isCompact_closedBall ..)] with p he hv hW hq hp ht t hs' b hb
  rw [revised]
  refine homeward_price p t Y _ _ fun i hh => ?_
  let Q := p.levels i (board p t Y i)
  let w := Damp t Y'
  have hb' := bound_nonneg t hb
  let v := FareP k p
  have hv' : 0 < v := Real.exp_pos _
  have hY : ∀ x ∈ K, ‖x‖ ≤ r := fun x hx => h (mem_image_of_mem norm hx)
  have hZ x (h : ‖x‖ ≤ r + 4 * n) : x ∈ U :=
    Metric.mem_closedBall.mpr
      (by
        rw [dist_zero_right]
        exact h)
  have hI : K ⊆ U := fun x hx => hZ x ((hY x hx).trans (by simp))
  have hA (x) (h : x ∉ K) : t x = 0 := image_eq_zero_of_notMem_tsupport (fun he => h (hs' he))
  have hP := height0 (p := p) hp
  let J := b * (B + C) * v
  have hJ : 0 ≤ J := by
    unfold J
    positivity
  have hw (x : Points n) : ‖Q x - w x‖ ≤ J ∧ (x ∉ U → Q x - w x = 0) := by
    by_cases hz : ∃ y : p.Tuple, x ∈ p.cell i (p.back y)
    · obtain ⟨y, hy⟩ := hz
      let u := p.rel (p.back y) i
      have hu : dist u x ≤ _ := XSpace.Mesh.upper_corner p i hy
      let Fz := Y ⟨p, p.back y, 0⟩
      rw [show Q x = t u * Fz from p.stair_at i x hy]
      constructor
      · have hc : ‖t u * Fz - w u‖ ≤ b * B * v := by
          rw [show w u = t u * Y' u from rfl, ← mul_sub, norm_mul]
          by_cases h : u ∈ K
          · exact
              mul_le_mul (hb u).1 (le_trans (hW _ i hh h) (mul_le_mul_of_nonneg_left hv hB))
                  (norm_nonneg _) hb' |>.trans_eq
                (by ring)
          rw [hA u h, norm_zero, zero_mul]
          positivity
        have ht' := hi t hs' b hb u x (height p / 2) (by positivity) (hu.trans hq)
        rw [← sub_add_sub_cancel (t u * Fz) (w u) (w x)]
        apply (norm_add_le ..).trans
        apply
          (add_le_add hc
              (ht'.trans
                (mul_le_mul_of_nonneg_left (show exp (-a * (height p / 2)) ≤ v from ?_)
                  (by positivity)))).trans_eq
        · unfold J
          ring
        exact
          le_trans
            (le_of_eq
              (show exp _ = FareP (a / 2) p from
                (by
                  unfold FareP
                  congr 1
                  ring)))
            he
      intro H
      rw [show w x = t x * Y' x from rfl, hA x (fun hx => H (hI hx)),
        hA u
          (fun hu' =>
            H
              (hZ x
                (XSpace.Mesh.norm_near hp (hY u hu')
                  (by
                    rw [dist_comm]
                    exact hu)))),
        zero_mul, zero_mul, sub_zero]
    have h' : t x = 0 := hA x (fun h => hz (p.gained i hp hh ht x (hY _ h)))
    rw [show Q x = 0 from p.stair_off i x (fun j hj => hz ⟨j, hj⟩), show w x = t x * Y' x from rfl,
      h', zero_mul, sub_zero, norm_zero]
    exact ⟨hJ, fun _ => rfl⟩
  change ‖(∫ z, Q z) - (∫ z, w z)‖ ≤ _
  rw [← integral_sub (p.integrable_stair ..) (shaped_legal ..), ←
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun z => (hw z).2)]
  refine
    (norm_setIntegral_le_of_norm_le_const (C := J) (isCompact_closedBall .. |>.measure_lt_top)
          (fun z _ => (hw z).1)).trans_eq
      ?_
  unfold J v s
  ring
end YM.WilsonMS.VisitH
