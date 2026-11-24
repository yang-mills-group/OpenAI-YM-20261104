import YM.WilsonMS.Scales.ChartWork
/-!
# General sample estimate for carrying the detector

Hölder and compact distance, not redefining the measurement by a simpler
diagnostic. Expose the integrated result at the same time. This includes
small *power* on positive-order products at a common mesh shift before
passing through the stance functional.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameConj
open Function Set Filter MeasureTheory Real Finset Metric Asymptotics
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Rider Reservoir VisitH Sea Fray
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {F H : Cirrus.Sample n → ℂ} {p q : Points n → ℂ} {K : Set (Points n)}

def Rel (K : Set (Points n)) (x y : K) (r : ℝ) :=
  dist x.val y.val ≤ exp (-r)

structure Vitals (F : Cirrus.Sample n → ℂ) (p : Points n → ℂ) (K : Set (Points n)) : Prop where
  vital : Climb.Traced (Rel K) (fun x => p x.val)
  run :
    ∃ a : ℝ,
      0 < a ∧
        ∃ D : ℝ,
          0 ≤ D ∧
            ∀ᶠ m in Front,
              ∀ v : Fin n → Cover,
                ∀ c ∈ m.Box, m.rel v c ∈ K → ‖F ⟨m, v, c⟩ - p (m.rel v c)‖ ≤ D * FareP a m
namespace Vitals

lemma exact_s {F' : Cirrus.Sample n → ℂ} (h : Vitals F p K)
    (hp : ∀ᶠ i in Front, ∀ (p : Cirrus.Sample n), p.F = i → F p = F' p) : Vitals F' p K := by
  obtain ⟨hh, a, ha, D, hD, hT⟩ := h
  refine ⟨hh, a, ha, D, hD, ?_⟩
  filter_upwards [hp, hT] with i he hi v c hv hx
  rw [← he _ rfl]
  exact hi v c hv hx

lemma const (k : ℂ) : Vitals (fun _ => k) (fun _ => k) K :=
  ⟨Climb.Handles.point _, 1, zero_lt_one, 0, le_rfl, Eventually.of_forall (fun _ _ _ _ _ => by simp)⟩

lemma confirm {c : 𝕄 → ℂ} {v : ℂ} (h : Fast c v) : Vitals (fun i => c i.F) (fun _ => v) K := by
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨D, hD, h⟩ := (show _ =O[Front] _ from h).exists_pos
  refine ⟨Climb.Handles.point _, a, ha, D, hD.le, h.bound.mono fun i hi _ _ _ _ => ?_⟩
  change ‖c i - v‖ ≤ D * ‖FareP a i‖ at hi
  rwa [Real.norm_of_nonneg (exp_pos _).le] at hi

lemma knits (h : Vitals F p K) (ht : Vitals H q K) : Vitals (F + H) (p + q) K := by
  obtain ⟨hL, a, ha, C, hC, he⟩ := h
  obtain ⟨hV, b, hb, D, hD, hH⟩ := ht
  refine ⟨Climb.Handles.main_add hL hV, min a b, lt_min ha hb, C + D, by positivity, ?_⟩
  let s := min a b
  filter_upwards [he, hH, fare_lower a s (min_le_left ..), fare_lower b s (min_le_right ..)] with i hp
    hu hv hx v c hy hK
  rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, add_mul]
  exact
    (norm_add_le ..).trans
      (add_le_add ((hp _ _ hy hK).trans (mul_le_mul_of_nonneg_left hv hC))
        ((hu _ _ hy hK).trans (mul_le_mul_of_nonneg_left hx hD)))

lemma sum {J : Type*} (s : Finset J) {h : J → Cirrus.Sample n → ℂ} {g : J → Points n → ℂ}
    (he : ∀ i ∈ s, Vitals (h i) (g i) K) :
    Vitals (fun p => ∑ i ∈ s, h i p) (fun p => ∑ i ∈ s, g i p) K := by
  induction s using Finset.induction_on with
  | empty =>
    simp_rw [Finset.sum_empty]
    exact Vitals.const 0
  | insert i v hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (he _ (by simp)).knits (ih fun i h => he i (Finset.mem_insert_of_mem h))

lemma team (h : Vitals F p K) (ht : Vitals H q K) : Vitals (F * H) (p * q) K := by
  obtain ⟨he, a, ha, C, hC, hF⟩ := h
  obtain ⟨hp, b, hb, D, hD, hH⟩ := ht
  obtain ⟨M, hM, h⟩ := (Climb.Traced.exported he).1
  obtain ⟨N, hN, h'⟩ := (Climb.Traced.exported hp).1
  let s := min a b
  have hs : 0 < s := lt_min ha hb
  refine ⟨Climb.Handles.main_mul he hp, s, hs, C * N + (C + M) * D, by positivity, ?_⟩
  filter_upwards [hF, hH, (fare_limit hs).eventually (ge_mem_nhds zero_lt_one),
    fare_lower a s (min_le_left ..), fare_lower b s (min_le_right ..)] with i hi hv hh hU ht v c hV hx
  let x := i.rel v c
  let f := F ⟨i, v, c⟩
  let g := H ⟨i, v, c⟩
  let U := FareP s i
  change U ≤ 1 at hh
  have hI : ‖f - p x‖ ≤ C * U := (hi v c hV hx).trans (mul_le_mul_of_nonneg_left hU hC)
  have hz : ‖f‖ ≤ C + M :=
    le_trans (le_of_eq (congr_arg norm (sub_add_cancel f (p x)).symm))
      ((norm_add_le ..).trans (add_le_add (hI.trans (mul_le_of_le_one_right hC hh)) (h ⟨_, hx⟩)))
  change ‖f * g - _‖ ≤ _
  rw [Pi.mul_apply,
    show f * g - _ = (f - p x) * q x + f * (g - q x) from
      (by
        unfold x
        ring)]
  apply (norm_add_le ..).trans
  rw [norm_mul, norm_mul]
  exact
    (add_le_add
          (mul_le_mul hI (show ‖q x‖ ≤ N from h' ⟨_, hx⟩) (norm_nonneg _)
            (by
              unfold U FareP
              positivity))
          (mul_le_mul hz (le_trans (hv _ _ hV hx) (mul_le_mul_of_nonneg_left ht hD)) (norm_nonneg _)
            (add_nonneg hC hM))).trans_eq
      (by
        unfold U
        ring)

lemma negs (h : Vitals F p K) : Vitals (-F) (-p) K := by
  have he (X : Type) (F : X → ℂ) : (-F) = (fun _ => (-1 : ℂ)) * F := by
    ext
    simp
  rw [he _ F, he _ p]
  exact (Vitals.const _).team h

lemma sub (h : Vitals F p K) (ht : Vitals H q K) : Vitals (F - H) (p - q) K := by
  rw [sub_eq_add_neg, sub_eq_add_neg p]
  exact h.knits ht.negs

lemma felt_shape {P} (h : Vitals F P K) :
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
                          dist x y ≤ exp (-r) → ‖Damp t P x - Damp t P y‖ ≤ b * C * exp (-a * r) := by
  obtain ⟨⟨C, hC, h⟩, a, ha, D, hD, hT⟩ := (Climb.Traced.exported h.vital)
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
  have hL (i : Points n) (v : ℂ) (hv : ‖v‖ ≤ b * U) (hp : i ∈ K) : ‖v * P i‖ ≤ b * (C + D) * U := by
    rw [norm_mul]
    apply (mul_le_mul hv (h ⟨i, hp⟩) (norm_nonneg _) (by positivity)).trans
    rw [mul_right_comm b (C + D)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold Damp
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ K
  by_cases hy : y ∈ K
  · rw [show t x * P x - t y * P y = (t x - t y) * P y + t x * (P x - P y) from (by ring)]
    apply (norm_add_le ..).trans
    rw [norm_mul, norm_mul]
    apply
      (add_le_add (mul_le_mul hW (h ⟨y, hy⟩) (norm_nonneg _) (by positivity))
          (mul_le_mul (hb x).1
            (le_trans (hT ⟨x, hx⟩ ⟨y, hy⟩ r hr hv) (mul_le_mul_of_nonneg_left hA hD)) (norm_nonneg _)
            hu)).trans_eq
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

lemma reference_bound {P} (h : Vitals F P K) (hK : IsCompact K) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∀ (t : Test n), tsupport t ⊆ K → ∀ b, TestBudget.Bound t b → ‖t.applyTo P‖ ≤ b * C := by
  obtain ⟨C, hC, h⟩ := (Climb.Traced.exported h.vital) |>.1
  refine ⟨C * volume.real K, mul_nonneg hC ENNReal.toReal_nonneg, fun t ht b hb => ?_⟩
  rw [Test.applyTo, ←
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun hv => hx (ht hv))) _),
    ← mul_assoc]
  exact
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx =>
      (norm_mul_le ..).trans (mul_le_mul (hb x).1 (h ⟨x, hx⟩) (norm_nonneg _) (bound_nonneg t hb))

lemma layPoint {P} (hK : IsCompact K) (hcont : ContinuousOn P (conf n)) (Z : Centered F)
    (hx : Vitals F P K) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ᶠ p in Front,
              ∀ f' : Test n,
                tsupport f' ⊆ K →
                  ∀ b, TestBudget.Bound f' b → ‖Deposit p F f' - f'.applyTo P‖ ≤ b * C * FareP a p := by
  obtain ⟨a, ha, C, hC, hi⟩ := hx.felt_shape
  obtain ⟨e, he, B, hB, hL⟩ := hx.run
  let k := min (a / 2) e
  have hk : 0 < k := lt_min (by positivity) he
  obtain ⟨r, h⟩ := (hK.image continuous_norm).bddAbove
  let U := closedBall (0 : Points n) (r + 4 * n)
  let s := volume.real U
  have hs : 0 ≤ s := ENNReal.toReal_nonneg
  let Y := F
  have hE := fare_lower (a / 2) k (min_le_left ..)
  have hV := fare_lower e k (min_le_right ..)
  refine ⟨k, hk, (B + C) * s, by positivity, ?_⟩
  filter_upwards [hE, hV, hL, stair_fee (n := n), frontier.smaller,
    XSpace.Mesh.fits_compact frontier U (isCompact_closedBall ..)] with p he hv hW hq hp ht t hs' b hb
  refine homeward_price p t Y _ _ fun i hh => ?_
  let Q := p.levels i (board p t Y i)
  let w := Damp t P
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
          rw [show w u = t u * P u from rfl, ← mul_sub, norm_mul]
          by_cases h : u ∈ K
          · rw [show Fz = F ⟨p, p.back y, i⟩ from (Z _ _ _).symm]
            exact
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
      rw [show w x = t x * P x from rfl, hA x (fun hx => H (hI hx)),
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
    rw [show Q x = 0 from p.stair_off i x (fun j hj => hz ⟨j, hj⟩), show w x = t x * P x from rfl, h',
      zero_mul, sub_zero, norm_zero]
    exact ⟨hJ, fun _ => rfl⟩
  change ‖(∫ z, Q z) - (∫ z, w z)‖ ≤ _
  have hYt : Integrable w volume := t.smearing hcont
  have hpT : Integrable Q volume := p.integrable_stair ..
  rw [← integral_sub hpT hYt, ←
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun z => (hw z).2)]
  refine
    (norm_setIntegral_le_of_norm_le_const (C := J) (isCompact_closedBall .. |>.measure_lt_top)
          (fun z _ => (hw z).1)).trans_eq
      ?_
  unfold J v s
  ring
end Vitals
end YM.WilsonMS.FrameConj
